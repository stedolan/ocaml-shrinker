module LocSet = Set.Make (struct
  type t = Location.t
  let compare (a : t) (b : t) =
    (* order by end pos then *reversed* start pos,
       so intervals sort after subintervals they include *)
    compare
      (a.loc_end, b.loc_start, a.loc_ghost)
      (b.loc_end, a.loc_start, b.loc_ghost)
end)

module Deleter : sig
  val find_deletable : Parsetree.structure -> LocSet.t
  val delete : locs:LocSet.t -> Parsetree.structure -> Parsetree.structure
end = struct
  let def = Ast_mapper.default_mapper

  let dummy_exp =
    Ast_helper.(Exp.assert_ (Exp.construct (Location.mknoloc (Longident.Lident "false")) None))

  let is_triv_expr (e : Parsetree.expression) =
    match e.pexp_desc with
    | Pexp_assert {pexp_desc = Pexp_construct _; _}
    | Pexp_construct ({txt=Lident ("false"|"true");_},_)
    | Pexp_constant _ -> true
    | _ -> false

  let is_triv_pat (p : Parsetree.pattern) =
    match p.ppat_desc with
    | Ppat_any -> true
    | _ -> false

  let fake_end_loc (l : Location.t) : Location.t =
    { loc_ghost = true; loc_end = l.loc_end; loc_start = l.loc_end }

  let find_deletable (ast : Parsetree.structure) =
    let locs = ref LocSet.empty in
    let note loc = locs := LocSet.add loc !locs in
    let collect =
      { def with
        signature_item = (fun mapper si -> note si.psig_loc; def.signature_item mapper si);
        structure_item = (fun mapper si ->
          note si.pstr_loc;
          def.structure_item mapper si);
        expr = (fun mapper e -> if not (is_triv_expr e) then note e.pexp_loc; def.expr mapper e);
        pat = (fun mapper e -> if not (is_triv_pat e) then note e.ppat_loc; def.pat mapper e);
        type_declaration = (fun mapper td -> if td.ptype_manifest <> None || td.ptype_kind <> Ptype_abstract then note td.ptype_name.loc; def.type_declaration mapper td);
        module_expr = (fun mapper me ->
          begin match me.pmod_desc with
          | Pmod_constraint _ -> note (fake_end_loc me.pmod_loc)
          | _ -> ()
          end;
          def.module_expr mapper me); }
    in
    let _ = collect.structure collect ast in
    !locs
  
  let delete ~locs ast =
    let mapper =
      { def with
        signature = (fun mapper ss ->
          let psg_items =
            List.filter (fun s -> not (LocSet.mem s.Parsetree.psig_loc locs)) ss in
          def.signature mapper psg_items);
        structure = (fun mapper ss ->
          let ss =
            List.filter (fun s -> not (LocSet.mem s.Parsetree.pstr_loc locs)) ss in
          def.structure mapper ss);
        expr = (fun mapper e ->
          if LocSet.mem e.pexp_loc locs
          then dummy_exp
          else def.expr mapper e);
        pat = (fun mapper p ->
          if LocSet.mem p.ppat_loc locs
          then { p with ppat_desc = Ppat_any }
          else def.pat mapper p);
        type_declaration = (fun mapper td ->
          if LocSet.mem td.ptype_name.loc locs
          then { td with ptype_manifest = None; ptype_kind = Ptype_abstract }
          else def.type_declaration mapper td);
        module_expr = (fun mapper me ->
          let me =
            match me.pmod_desc with
            | Pmod_constraint (m, _) when LocSet.mem (fake_end_loc me.pmod_loc) locs ->
               m
            | _ -> me
          in
          def.module_expr mapper me )
      }
    in
    mapper.structure mapper ast
end

(* Remove the [count] latest nonoverlapping locations from a set,
   and all of their included subintervals. *)
let take_latest ~count ls =
  let remove_included (loc : Location.t) ls =
    let rec aux ~drops ls =
      match LocSet.max_elt_opt ls with
      | None -> drops, LocSet.empty
      | Some l' ->
         if l'.loc_end < loc.loc_start then
           (* everything in ls ends before loc starts *)
           drops, ls
         else
           if loc.loc_start <= l'.loc_start &&
              l'.loc_end <= loc.loc_end then
             aux ~drops:(LocSet.add l' drops) (LocSet.remove l' ls)
           else
             let drops, keep = aux ~drops (LocSet.remove l' ls) in
             drops, LocSet.add l' keep
    in aux ~drops:LocSet.empty ls
  in
  let rec drop_max ~count ls =
    if count <= 0 then LocSet.empty, LocSet.empty, ls
    else match LocSet.max_elt_opt ls with
    | None -> LocSet.empty, LocSet.empty, ls
    | Some loc ->
       let extra, ls = remove_included loc ls in
       let drop, extra2, keep = drop_max ~count:(count-1) ls in
       LocSet.add loc drop,
       LocSet.add loc (LocSet.union extra extra2),
       keep
  in
  let drop, included, keep = drop_max ~count ls in
  drop, keep, LocSet.cardinal included


external terminfo_rows: out_channel -> int = "caml_terminfo_rows"

let shrink pt =
  let runs = ref 0 in
  let tmpfile = Filename.temp_file "shrink" ".ml" in
  let success_file = Filename.temp_file "shrink" ".ml" in
  let is_interesting pt =
    incr runs;
    Out_channel.with_open_text tmpfile (fun ch ->
      Format.fprintf (Format.formatter_of_out_channel ch) "%a@." Pprintast.structure pt);
    match Sys.command (Printf.sprintf "ocamlc.opt -c -impl '%s' 2>&1 | grep -q 'Fatal error'" tmpfile) with
    | 0 -> true
    | _ -> false
  in
  let all_locations = Deleter.find_deletable pt in
  let total_count = LocSet.cardinal all_locations in
  let deleted_count = ref 0 in
  let last_success_rate = ref 1 in
  let ansi_clear = "\027[2J\027[H" in
  let ansi_bold_green = "\027[1;92m" in
  let ansi_normal = "\027[0m" in
  let rec shrink ~locs ~rate pt =
    Printf.printf "%sRun %03d: %2.0f%% deleted%s\n\n%!"
      (ansi_clear ^ ansi_bold_green)
      !runs
      (100. *. float_of_int !deleted_count /. float_of_int total_count)
      ansi_normal;
    Sys.command (Printf.sprintf "tail -n -%d '%s'"
                   (max 10 (min 30 (terminfo_rows stdout - 2)))
                   success_file) |> ignore;
    if LocSet.is_empty locs then pt else
    let count = max 1 (rate/2) in
    let drop, keep, drop_count = take_latest ~count locs in
    let pt' = Deleter.delete ~locs:drop pt in
    if is_interesting pt' then begin
      Sys.command (Printf.sprintf "mv '%s' '%s'" tmpfile success_file) |> ignore;
      last_success_rate := rate;
      deleted_count := !deleted_count + drop_count;
      shrink ~locs:keep ~rate:(rate * 2) pt'
    end else
      if count > 1 then
        shrink ~locs ~rate:(max 1 (rate / 4)) pt
      else begin
        let rate = !last_success_rate in
        last_success_rate := max 1 (rate / 2);
        shrink ~locs:(LocSet.fold LocSet.remove drop locs) ~rate pt
      end
  in
  let shrink_locs = Deleter.find_deletable pt in 
  let pt = shrink ~locs:shrink_locs ~rate:1 pt in
  Format.printf "%sComplete after %d runs@.@.%a@." ansi_clear !runs Pprintast.structure pt;
  ()

let () =
  let filename = Sys.argv.(1) in
  let pt = Pparse.parse_implementation ~tool_name:"shrinker" filename in
  let _pt' = shrink pt in
  ()
