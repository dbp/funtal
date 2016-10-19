open Ftal;;


(* Factorial Two Ways *)

let factorial_f =
  let f = F.(ELam ([("f", TRec ("a", TArrow ([TVar "a"; TInt], TInt)));
                    ("x1", TInt)],
                   EIf0 (EVar "x1",
                         EInt 1,
                         EBinop (EVar "x1",
                                 BTimes,
                                 EApp (EUnfold (EVar "f"),
                                       [EVar "f"; EBinop (EVar "x1", BMinus, EInt 1)]))))) in
  F.(ELam ([("x2", TInt)],
           EApp (f, [EFold ("b",
                            TArrow ([TVar "b"; TInt], TInt),
                            f);
                     EVar "x2"])))

let factorial_t =
  let lf = FTAL.gen_sym ~pref:"l" () in
  let la = FTAL.gen_sym ~pref:"l" () in
  let h = [(lf, TAL.(HCode ([DZeta "z3"; DEpsilon "e"],
                            [],
                            SAbstract ([TInt], "z3"),
                            QEnd (TInt, SAbstract ([], "z3")),
                            [Isld ("rn", 0); Imv ("rr", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SAbstract ([], "z3"))]));
                             Isfree 1;
                             Iret (QEnd (TInt, SAbstract ([], "z1")), "rr")])));
           (la, TAL.(HCode ([DZeta "z4"],
                            [("rr", TInt); ("ri", TInt); ("rn", TInt)],
                            SAbstract ([TInt], "z3"),
                            QEnd (TInt, SAbstract ([], "z3")),
                            [Iaop (Mult, "rr", "rr", UR "rn");
                             Iaop (Sub, "rn", "rn", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SAbstract ([], "z1"))]));
                             Isfree 1;
                             Iret (QEnd (TInt, SAbstract ([],  "z4")), "rr")])))] in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary (TArrow ([TInt], TInt),
                            ([TAL.(Imv ("r1", UW (WLoc lf))); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ([TInt], TInt)), SAbstract ([], "z2")), "r1"))], h)),
                 [EVar "x"])))


(* Different number of basic blocks *)

let blocks_1 =
  let l = FTAL.gen_sym ~pref:"l" () in
  let h = [(l,
            TAL.(HCode ([DZeta "z3"; DEpsilon "e"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SAbstract ([], "z3"), QEpsilon "e")))],
                        SAbstract ([TInt], "z3"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iret (QR "ra", "r1")])))] in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary (TArrow ([TInt], TInt),
                            (TAL.([Imv ("r1", UW (WLoc l)); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ([TInt], TInt)), SAbstract ([], "z2")), "r1"))], h))),
                 [EVar "x"])))


let blocks_2 =
  let l1 = FTAL.gen_sym ~pref:"l" () in
  let l2 = FTAL.gen_sym ~pref:"l" () in
  let h = [(l1,
            TAL.(HCode ([DZeta "z3"; DEpsilon "e1"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SAbstract ([], "z3"), QEpsilon "e1")))],
                        SAbstract ([TInt], "z3"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Isst (0, "r1");
                         Ijmp (UApp (UW (WLoc l2), [OS (SAbstract ([], "z3")); OQ (QEpsilon "e1")]))])));
           (l2,
            TAL.(HCode ([DZeta "z4"; DEpsilon "e2"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SAbstract ([], "z4"), QEpsilon "e2")))],
                        SAbstract ([TInt], "z4"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iret (QR "ra", "r1")])))
            ] in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary (TArrow ([TInt], TInt),
                            (TAL.([Imv ("r1", UW (WLoc l1)); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ([TInt], TInt)), SAbstract ([], "z2")), "r1"))], h))),
                 [EVar "x"])))


(* Higher-order Profiling *)

(*
p = λf.let c = ref 0 in < λx.(c := !c + 1; f x),λ_.!c >
e1 = λf.λg.λa.let <g′,g'′> = p g in (f g′ ; g′ <> ; a g ′ ; g′′ <>)
e2 = λf.λg.λa.let <g′,g′′> = p g in (f g′ ; g <> ; a g′ ; g′′ <> + 1)
*)

(* let gen_ref = TAL.(HCode ([DZeta "z1"; DEpsilon "e1"], *)
(*                           [("ra", TBox (PBlock ([], [("r1", TTupleRef [TInt])], *)
(*                                                 SZeta "z1", QEpsilon "e1")))], *)
(*                           SZeta "z1", *)
(*                           QR "ra", *)
(*                           [Imv ("r1", UW (WInt 0)); *)
(*                            Isalloc 1; *)
(*                            Isst (0, "r1"); *)
(*                            Iralloc ("r1", 1); *)
(*                            Iret (QR "ra", "r1")])) *)

(* let read_ref = TAL.(HCode ([DZeta "z1"; DEpsilon "e1"], *)
(*                            [("ra", TBox (PBlock ([], [("r1", TInt)], *)
(*                                                 SZeta "z1", QEpsilon "e1")))], *)
(*                            SZeta "z1", *)
(*                            QR "ra", *)
(*                            [Isld ("r1", 0); *)
(*                             Ild ("r1", "r1", 0); *)
(*                             Iret (QR "ra", "r1")])) *)

(* let write_ref = TAL.(HCode ([DZeta "z1"; DEpsilon "e1"], *)
(*                             [("ra", TBox (PBlock ([], [("r1", TUnit)], *)
(*                                                   SCons (TTupleRef [TInt], SCons (TInt, SZeta "z1")), *)
(*                                                   QEpsilon "e1")))], *)
(*                             SCons (TTupleRef [TInt], SCons (TInt, SZeta "z1")), *)
(*                             QR "ra", *)
(*                             [Isld ("r1", 0); *)
(*                              Isld ("r2", 1); *)
(*                              Ist ("r1", 0, "r2"); *)
(*                              Imv ("r1", UW WUnit); *)
(*                              Iret (QR "ra", "r1")])) *)



(* let profiler = *)
(*   TAL.(HCode ([DZeta "z1", DEpsilon "e1"], *)
(*               [("ra", TBox (PBlock ([], [("r1", FTAL.tytrans F.(TTuple [TArrow ("z2",[TUnit],TUnit); TArrow ("z3", [TUnit], TInt)]))], SZeta "z1", QEpsilon "e1")))], *)
(*               SCons (FTAL.tytrans F.(TArrow ("z4",[TUnit],TUnit)), SZeta "z1"), *)
(*               QR "ra", *)
(*               [Isalloc 1; *)
(*                Imv ("r1", WInt 0); *)
(*                Isst (0, "r1"); *)
(*                Iralloc ("rc", 1); *)
(*                Iimport ("rf", SZeta "z1", F.(TArrow ("z5",[TUnit],TUnit)), *)
(*                         F.(ELam ("z6", [("x", TUnit)], *)

(*                                 ))) *)
(*                Iballoc ("r1", 2); *)


(* let profiling_1 = *)
