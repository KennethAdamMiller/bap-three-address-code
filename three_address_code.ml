open Core_kernel
open Bap.Std
open Regular.Std
open Format
open Bap_term_manip

include Self()

let make_var e =
  let sz = exp_size e in
  Var.create (vname ()) Bil.(Imm sz)

let flatten b =
  let make_def ?tid e blk_bdr r =
    let v1 = (make_var e) in
    let d = Def.create ?tid v1 e in
    Blk.Builder.add_def blk_bdr d;
    blk_bdr,Map.set r e v1 in
  (* TODO this object belongs in bap_term_manip, and *)
  let tac =
    object(self)
      inherit [Blk.Builder.t * var Exp.Map.t * tid option] Term.visitor as super

      method leave_concat l r (blk_bdr,replace,tid) =
        let l = (transform replace)#map_exp l in
        let r = (transform replace)#map_exp r in
        let blk_bdr, replace,tid =
          if not ((is_var l) || (is_int l)) then
            let b,rep = make_def ?tid l blk_bdr replace in b,rep,None
          else blk_bdr,replace,tid in
        let blk_bdr, replace,tid =
          if not ((is_var r) || (is_int r)) then
            let b,rep = make_def ?tid r blk_bdr replace in b,rep,None
          else blk_bdr,replace,tid in
        blk_bdr,replace,tid

      method leave_cast c i e (blk_bdr,replace,tid) =
        let e = (transform replace)#map_exp e in
        let blk_bdr, replace,tid =
          if not (is_terminator e) then
            let b,r = make_def ?tid e blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        blk_bdr,replace,tid

      method leave_unop u e (blk_bdr,replace,tid) =
        let e = (transform replace)#map_exp e in
        let blk_bdr, replace,tid =
          if not (is_var e) then
            let b,rep = make_def ?tid e blk_bdr replace in b,rep,None
          else blk_bdr,replace,tid in
        blk_bdr,replace,tid

      method leave_binop b e1 e2 (blk_bdr,replace,tid) =
        let e1 = (transform replace)#map_exp e1 in
        let e2 = (transform replace)#map_exp e2 in
        if is_terminator e1 && not (is_terminator e2) then
          let blk_bdr,replace = make_def ?tid e2 blk_bdr replace in
          blk_bdr,replace,None
        else if not (is_terminator e1) && is_terminator e2 then
          let blk_bdr,replace = make_def ?tid e1 blk_bdr replace in
          blk_bdr,replace,None
        else if not (is_terminator e1) && not (is_terminator e2) then
          let blk_bdr,replace = make_def ?tid e1 blk_bdr replace in
          let blk_bdr,replace = make_def e2 blk_bdr replace in
          blk_bdr,replace,None
        else
          blk_bdr, replace,tid

      method enter_def d (b,r,_) =
        (b,r,Some Term.(tid d))
      method leave_def d (blk_bdr,replace,tid) =
        let d = Def.map_exp d (transform replace)#map_exp in
        let rhs = Def.rhs d in
        (* replace the original tid if need be *)
        let d = Def.create ?tid Def.(lhs d) rhs in 
        Blk.Builder.add_def blk_bdr d;
        blk_bdr,Map.set replace rhs Def.(lhs d),None

      method leave_load ~mem ~addr en s (blk_bdr,replace,tid) =
        let mem = (transform replace)#map_exp mem in
        let addr = (transform replace)#map_exp addr in
        let blk_bdr,replace,tid = 
          if not (is_terminator mem) then
            let b,r = make_def ?tid mem blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        let blk_bdr,replace,tid =
          if not (is_terminator addr) then
            let b,r = make_def ?tid addr blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        blk_bdr,replace,tid

      method leave_store ~mem ~addr ~exp en s (blk_bdr,replace,tid) =
        let mem = (transform replace)#map_exp mem in
        let addr = (transform replace)#map_exp addr in
        let exp = (transform replace)#map_exp exp in
        let blk_bdr,replace,tid = 
          if not (is_terminator mem) then
            let b,r = make_def ?tid mem blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        let blk_bdr,replace,tid =
          if not (is_terminator addr) then
            let b,r = make_def ?tid addr blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        let blk_bdr,replace,tid = 
          if not (is_terminator exp) then
            let b,r = make_def ?tid exp blk_bdr replace in b,r,None
          else blk_bdr,replace,tid in
        blk_bdr, replace,tid

      method enter_phi p (b,r,_) =
        (b,r,Some Term.(tid p))
      method leave_phi p (blk_bdr,replace,bid) =
        let exps,blk_bdr,replace,bid =
          Seq.fold Phi.(values p)
            ~init:([],blk_bdr,replace,bid)
            ~f:(fun (exps,blk_bdr,replace,bid) (tid,e) ->
              (*let blk_bdr,replace,bid =
                self#visit_exp e (blk_bdr,replace,bid) in*)
              if not (is_terminator e) then
                let e = Exp.fixpoint (transform replace)#map_exp e in
                let blk_bdr,replace,bid =
                  let b,r = make_def ?tid:bid e blk_bdr replace in b,r,None in
                let e = Exp.fixpoint (transform replace)#map_exp e in
                ((tid,e) :: exps),blk_bdr,replace,bid
              else ((tid,e) :: exps),blk_bdr,replace,bid
              ) in
        let np = List.fold exps ~init:None ~f:(fun np (tid,e) -> 
            match np with
            | None -> Some(Phi.create ?tid:bid Phi.(lhs p) tid e)
            | Some p -> Some(Phi.update p tid e)
          ) in
        let p = Option.value np ~default:p in
        Blk.Builder.add_phi blk_bdr p;
        blk_bdr,replace,bid

      method enter_jmp j (b,r,_) = (b,r,Some Term.(tid j))

      method leave_jmp j (blk_bdr,replace,tid) =
        let cond = Jmp.cond j in
        let cond = Exp.fixpoint (transform replace)#map_exp cond in
        let j = Jmp.with_cond j cond in
        let check_update_label l =
          match l with
          | Indirect e ->
            let e = Exp.fixpoint (transform replace)#map_exp e in
            let blk_bdr,replace = make_def ?tid e blk_bdr replace in
            let e = Exp.fixpoint (transform replace)#map_exp e in
            (blk_bdr,replace,None),Indirect e
          | Direct _  -> (blk_bdr,replace,tid),l in
        let kind,blk_bdr,replace,tid = 
          match Jmp.kind j with
          | Call call ->
            let (blk_bdr,replace,tid),target =
              check_update_label Call.(target call) in
            let call = Call.with_target call target in
            let ret =
              Option.map Call.(return call) ~f:check_update_label in
            let (blk_bdr,replace,tid),ret =
              match ret with
              | Some ((blk_bdr,replace,tid),r) -> (blk_bdr,replace,tid),Some(r)
              | None -> (blk_bdr,replace,tid),None in
            let call =
              Option.value_map ret
                ~f:(fun ret -> Call.(with_return call ret)) ~default:call in
            Jmp.(Call call),blk_bdr,replace,tid
          | Goto target ->
            let (blk_bdr,replace,tid),l = check_update_label target in
            Jmp.(Goto l),blk_bdr,replace,tid
          | Ret r ->
            let (blk_bdr,replace,tid),r = (check_update_label r) in
            Jmp.(Ret r),blk_bdr,replace,tid
          | Int (i, l) -> Jmp.(Int (i,l)),blk_bdr,replace,tid in
        let j = Jmp.create ?tid ~cond kind in
        Blk.Builder.add_jmp blk_bdr j;
        blk_bdr,replace,tid

    end in
  let tid = Term.tid b in
  let blk_bdr = Blk.Builder.create ~tid () in
  let blk_bdr,_,_ = tac#visit_blk b (blk_bdr,Exp.Map.empty,None) in
  Blk.Builder.result blk_bdr

let main proj =
  let prog = Project.program proj in
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        let sub = Sub.ssa sub in
        Term.map blk_t sub flatten
      ) in
  Project.with_program proj prog


let () =
  let () = Config.manpage [
      `S "DESCRIPTION";
      `P
        "Transform a BIR program to a three-address-code.";
    ] in
  let deps = [] in
  Config.when_ready (fun {Config.get=(!)} ->
      Project.register_pass ~deps main;
    )
