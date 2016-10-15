open Ftal;;


(* Factorial Two Ways *)

let factorial_f =
  let f = F.(ELam ("z1", [("f", TRec ("a", TArrow ("z2", [TVar "a"; TInt], TInt)));
                          ("x1", TInt)],
                   EIf0 (EVar "x1",
                         EInt 1,
                         EBinop (EVar "x1",
                                 BTimes,
                                 EApp (EUnfold (EVar "f"),
                                       TAL.SZeta "z3",
                                       [EVar "f"; EBinop (EVar "x1", BMinus, EInt 1)]))))) in
  F.(ELam ("z4", [("x2", TInt)],
           EApp (f, TAL.SZeta "z4", [EFold ("b",
                                            TArrow ("z5", [TVar "b"; TInt], TInt),
                                            f);
                                    EVar "x2"])))

let factorial_t =
  let lf = FTAL.gen_sym ~pref:"l" () in
  let la = FTAL.gen_sym ~pref:"l" () in
  let h = [(lf, TAL.(HCode ([DZeta "z3"; DEpsilon "e"],
                            [],
                            SCons (TInt, SZeta "z3"),
                            QEnd (TInt, SZeta "z3"),
                            [Isld ("rn", 0); Imv ("rr", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SZeta "z3")]));
                             Isfree 1;
                             Iret (QEnd (TInt, SZeta "z1"), "rr")])));
           (la, TAL.(HCode ([DZeta "z4"],
                            [("rr", TInt); ("ri", TInt); ("rn", TInt)],
                            SCons (TInt, SZeta "z3"),
                            QEnd (TInt, SZeta "z3"),
                            [Iaop (Mult, "rr", "rr", UR "rn");
                             Iaop (Sub, "rn", "rn", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SZeta "z1")]));
                             Isfree 1;
                             Iret (QEnd (TInt, SZeta "z4"), "rr")])))] in
  F.(ELam ("z1", [("x", TInt)],
           EApp (EBoundary (TArrow ("z2", [TInt], TInt), TAL.SZeta "z2",
                            ([TAL.(Imv ("r1", UW (WLoc lf))); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ("z1", [TInt], TInt)), SZeta "z2"), "r1"))], h)),
                 TAL.SZeta "z1",
                 [EVar "x"])))


(* Different number of basic blocks *)

let blocks_1 =
  let l = FTAL.gen_sym ~pref:"l" () in
  let h = [(l,
            TAL.(HCode ([DZeta "z3"; DEpsilon "e"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SZeta "z3", QEpsilon "e")))],
                        SCons (TInt, SZeta "z3"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iret (QR "ra", "r1")])))] in
  F.(ELam ("z1", [("x", TInt)],
           EApp (EBoundary (TArrow ("z2", [TInt], TInt), TAL.SZeta "z2",
                            (TAL.([Imv ("r1", UW (WLoc l)); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ("z1", [TInt], TInt)), SZeta "z2"), "r1"))], h))),
                 TAL.SZeta "z1",
                 [EVar "x"])))


let blocks_2 =
  let l1 = FTAL.gen_sym ~pref:"l" () in
  let l2 = FTAL.gen_sym ~pref:"l" () in
  let h = [(l1,
            TAL.(HCode ([DZeta "z3"; DEpsilon "e1"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SZeta "z3", QEpsilon "e1")))],
                        SCons (TInt, SZeta "z3"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Isst (0, "r1");
                         Ijmp (UApp (UW (WLoc l2), [OS (SZeta "z3"); OQ (QEpsilon "e1")]))])));
           (l2,
            TAL.(HCode ([DZeta "z4"; DEpsilon "e2"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SZeta "z4", QEpsilon "e2")))],
                        SCons (TInt, SZeta "z4"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iret (QR "ra", "r1")])))
            ] in
  F.(ELam ("z1", [("x", TInt)],
           EApp (EBoundary (TArrow ("z2", [TInt], TInt), TAL.SZeta "z2",
                            (TAL.([Imv ("r1", UW (WLoc l1)); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ("z1", [TInt], TInt)), SZeta "z2"), "r1"))], h))),
                 TAL.SZeta "z1",
                 [EVar "x"])))
