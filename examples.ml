open Ftal;;


(* Factorial Two Ways *)

let factorial_f =
  let f = F.(ELam (dummy_loc, [("f", TRec ("a", TArrow ([TVar "a"; TInt], TInt)));
                    ("x1", TInt)],
                   EIf0 (dummy_loc, EVar (dummy_loc, "x1"),
                         EInt (dummy_loc, 1),
                         EBinop (dummy_loc, EVar (dummy_loc, "x1"),
                                 BTimes,
                                 EApp (dummy_loc, EUnfold (dummy_loc, EVar (dummy_loc, "f")),
                                       [EVar (dummy_loc, "f"); EBinop (dummy_loc, EVar (dummy_loc, "x1"), BMinus, EInt (dummy_loc, 1))]))))) in
  F.(ELam (dummy_loc, [("x2", TInt)],
           EApp (dummy_loc, f, [EFold (dummy_loc, "b",
                            TArrow ([TVar "b"; TInt], TInt),
                            f);
                     EVar (dummy_loc, "x2")])))

let factorial_t' =
  let lf = FTAL.gen_sym ~pref:"l" () in
  let la = FTAL.gen_sym ~pref:"l" () in
  let h = [(lf, TAL.(Box, HCode ([DZeta "z3"; DEpsilon "e"],
                            [("ra", TBox (PBlock ([],
                                                  [("r1", TInt)],
                                                  SAbstract ([], "z3"),
                                                  QEpsilon "e")))],
                            SAbstract ([TInt], "z3"),
                            QR "ra",
                            [Isld (dummy_loc, "r7", 0);
                             Imv (dummy_loc, "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                             Ibnz (dummy_loc, "r7", UApp (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, la)), [OS (SAbstract ([], "z3"))]));
                             Isfree (dummy_loc, 1);
                             Iret (dummy_loc, "ra", "r1")])));
           (la, TAL.(Box, HCode ([DZeta "z4"],
                            [("r1", TInt); ("r7", TInt);
                             ("ra", TBox (PBlock ([],
                                                  [("r1", TInt)],
                                                  SAbstract ([], "z3"),
                                                  QEpsilon "e")))],
                            SAbstract ([TInt], "z3"),
                            QR "ra",
                            [Iaop (dummy_loc, Mult, "r1", "r1", UR (dummy_loc, "r7"));
                             Iaop (dummy_loc, Sub, "r7", "r7", UW (dummy_loc, WInt (dummy_loc, 1)));
                             Ibnz (dummy_loc, "r7", UApp (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, la)), [OS (SAbstract ([], "z1"))]));
                             Isfree (dummy_loc, 1);
                             Ihalt (dummy_loc, TInt, SAbstract ([],  "z4"), "r1")])))] in
  (TAL.WLoc (dummy_loc, lf), h)

let factorial_t =
  let (l, h) = factorial_t' in
  F.(ELam (dummy_loc, [("x", TInt)],
           EApp (dummy_loc, EBoundary (dummy_loc, TArrow ([TInt], TInt), None,
                            TAL.([Iprotect (dummy_loc, [], "z2");
                                  Imv (dummy_loc, "r1", UW (dummy_loc, l));
                                  Ihalt (dummy_loc, FTAL.tytrans (TArrow ([TInt], TInt)),
                                         SAbstract ([], "z2"),
                                         "r1")], h)
),
                 [EVar (dummy_loc, "x")])))
(* Different number of basic blocks *)

let blocks_1 =
  let l = FTAL.gen_sym ~pref:"l" () in
  let h = [(l,
            TAL.(Box, HCode ([DZeta "z3"; DEpsilon "e"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SAbstract ([], "z3"), QEpsilon "e")))],
                        SAbstract ([TInt], "z3"),
                        QR "ra",
                        [Isld (dummy_loc, "r1", 0);
                         Iaop (dummy_loc, Add, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                         Iaop (dummy_loc, Add, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                         Isfree (dummy_loc, 1);
                         Iret (dummy_loc, "ra", "r1")])))] in
  F.(ELam (dummy_loc, [("x", TInt)],
           EApp (dummy_loc, EBoundary
                   (dummy_loc, TArrow ([TInt], TInt),
                    None,
                    (TAL.([Iprotect (dummy_loc, [], "z2");
                           Imv (dummy_loc, "r1", UW (dummy_loc, WLoc (dummy_loc, l)));
                           Ihalt (dummy_loc, FTAL.tytrans (TArrow ([TInt], TInt)),
                                  SAbstract ([], "z2"),
                                  "r1")],
                          h))),
                 [EVar (dummy_loc, "x")])))


let blocks_2 =
  let l1 = FTAL.gen_sym ~pref:"l" () in
  let l2 = FTAL.gen_sym ~pref:"l" () in
  let h = TAL.([(l1,
                 (Box, HCode ([DZeta "z3"; DEpsilon "e1"],
                        [("ra", TBox (PBlock ([],
                                              [("r1", TInt)],
                                              SAbstract ([], "z3"),
                                              QEpsilon "e1")))],
                        SAbstract ([TInt], "z3"),
                        QR "ra",
                        [Isld (dummy_loc, "r1", 0);
                         Iaop (dummy_loc, Add, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                         Isst (dummy_loc, 0, "r1");
                         Ijmp (dummy_loc, UApp (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, l2)), [OS (SAbstract ([], "z3"));
                                                    OQ (QEpsilon "e1")]))])));
                (l2,
                 (Box, HCode ([DZeta "z4"; DEpsilon "e2"],
                        [("ra", TBox (PBlock ([],
                                              [("r1", TInt)],
                                              SAbstract ([], "z4"),
                                              QEpsilon "e2")))],
                        SAbstract ([TInt], "z4"),
                        QR "ra",
                        [Isld (dummy_loc, "r1", 0);
                         Iaop (dummy_loc, Add, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                         Isfree (dummy_loc, 1);
                         Iret (dummy_loc, "ra", "r1")])))
               ]) in
  F.(ELam (dummy_loc, [("x", TInt)],
           EApp (dummy_loc, EBoundary (dummy_loc, TArrow ([TInt], TInt),
                            None,
                            (TAL.([Iprotect (dummy_loc, [], "z2");
                                   Imv (dummy_loc, "r1", UW (dummy_loc, WLoc (dummy_loc, l1)));
                                   Ihalt (dummy_loc, FTAL.tytrans (TArrow ([TInt], TInt)),
                                          SAbstract ([], "z2"),
                                          "r1")], h))),
                 [EVar (dummy_loc, "x")])))


let higher_order =
  let tau = F.(TArrow([TArrow([TInt],TInt)], TInt)) in
  let g = F.(ELam (dummy_loc, [("h", TArrow ([TInt], TInt))], EApp (dummy_loc, EVar (dummy_loc, "h"), [EInt (dummy_loc, 1)]))) in
  let h = TAL.([
      ("l", (Box, HCode ([DZeta "z1"; DEpsilon "e1"],
                   [("ra", TBox (PBlock ([],
                                         [("r1", TInt)],
                                         SAbstract ([], "z1"),
                                         QEpsilon "e1")))],
                   SAbstract ([FTAL.tytrans tau], "z1"),
                   QR "ra",
                   [Isld (dummy_loc, "r1",0);
                    Isalloc (dummy_loc, 1);
                    Imv (dummy_loc, "r2", UW (dummy_loc, WLoc (dummy_loc, "lh")));
                    Isst (dummy_loc, 0, "r2");
                    Isst (dummy_loc, 1, "ra");
                    Imv (dummy_loc, "ra", UApp (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, "lgret")), [OS (SAbstract ([], "z1")); OQ (QEpsilon "e1")]));
                    Icall (dummy_loc, UR (dummy_loc, "r1"),
                           SAbstract ([TBox
                                         (PBlock ([],
                                                  [("r1", TInt)],
                                                  SAbstract ([], "z3"),
                                                  QEpsilon "e1"))],
                                      "z1"),
                           QI 0)])));
      ("lh", (Box, HCode ([DZeta "z2"; DEpsilon "e2"],
                    [("ra", TBox (PBlock ([],
                                          [("r1", TInt)],
                                          SAbstract ([], "z2"),
                                          QEpsilon "e2")))],
                    SAbstract ([TInt], "z2"),
                    QR "ra",
                    [Isld (dummy_loc, "r1",0);
                     Isfree (dummy_loc, 1);
                     Iaop (dummy_loc, Mult, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 2)));
                     Iret (dummy_loc, "ra", "r1")])));
      ("lgret", (Box, HCode ([DZeta "z3"; DEpsilon "e3"],
                       [("ra", TBox (PBlock ([],
                                             [("r1", TInt)],
                                             SAbstract ([], "z3"),
                                             QEpsilon "e3")));
                        ("r1", TInt)],
                       SAbstract ([TBox
                                     (PBlock ([],
                                              [("r1", TInt)],
                                              SAbstract ([], "z3"),
                                              QEpsilon "e3"))],
                                  "z3"),
                       QI 0,
                       [Isld (dummy_loc, "ra", 0);
                        Isfree (dummy_loc, 1);
                        Iret (dummy_loc, "ra", "r1")])))]) in
  F.(EApp (dummy_loc, EBoundary (dummy_loc, TArrow([tau],TInt),
                      None,
                      TAL.([Imv(dummy_loc, "r1", UW (dummy_loc, WLoc (dummy_loc, "l")));
                            Ihalt(dummy_loc, FTAL.tytrans F.(TArrow([tau],TInt)),
                                  SConcrete [],
                                  "r1")],
                           h)),
           [g]))


let call_to_call =
  let h = TAL.[
      ("l1", (Box, HCode ([DZeta "z1"; DEpsilon "e1"],
                    [("ra", TBox (PBlock ([],
                                          [("r1", TInt)],
                                          SAbstract ([], "z1"),
                                          QEpsilon "e1")))],
                    SAbstract ([], "z1"),
                    QR "ra",
                          [Isalloc (dummy_loc, 1);
                           Isst (dummy_loc, 0, "ra");
                           Imv (dummy_loc, "ra", UW (dummy_loc, WLoc (dummy_loc, "l2ret")));
                     Icall (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, "l2")),
                            SAbstract ([TBox (PBlock ([],
                                                      [("r1", TInt)],
                                                      SAbstract ([], "z1"),
                                                      QEpsilon "e1"))],
                                       "z1"),
                            QI 0)])));
      ("l1ret", (Box, HCode ([],
                       [("r1", TInt)],
                       SConcrete [],
                       QEnd (TInt, SConcrete []),
                       [Ihalt (dummy_loc, TInt, SConcrete [], "r1")])));
      ("l2", (Box, HCode ([DZeta "z2"; DEpsilon "e2"],
                    [("ra", TBox (PBlock ([],
                                          [("r1", TInt)],
                                          SAbstract ([], "z2"),
                                          QEpsilon "e2")))],
                    SAbstract ([], "z2"),
                    QR "ra",
                    [Imv (dummy_loc, "r1", UW (dummy_loc, WInt (dummy_loc, 1)));
                     Ijmp (dummy_loc, UApp (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, "l2aux")),
                                 [OS (SAbstract ([], "z2"));
                                  OQ (QEpsilon "e2")]))])));
      ("l2aux", (Box, HCode ([DZeta "z3"; DEpsilon "e3"],
                       [("r1", TInt);
                        ("ra", TBox (PBlock ([],
                                          [("r1", TInt)],
                                          SAbstract ([], "z3"),
                                             QEpsilon "e3")))],
                       SAbstract ([], "z3"),
                    QR "ra",
                       [Iaop (dummy_loc, Mult, "r1", "r1", UW (dummy_loc, WInt (dummy_loc, 2)));
                        Iret (dummy_loc, "ra", "r1")])));
      ("l2ret", (Box, HCode ([],
                       [("r1", TInt)],
                       SConcrete [TBox (PBlock ([],
                                                [("r1", TInt)],
                                                SConcrete [],
                                                QEnd (TInt, SConcrete [])))],
                       QI 0,
                             [Isld (dummy_loc, "ra", 0);
                              Isfree (dummy_loc, 1);
                              Iret (dummy_loc, "ra", "r1")])))] in
  (TAL.[Imv (dummy_loc, "ra", UW (dummy_loc, WLoc (dummy_loc, "l1ret")));
        Icall (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, "l1")), SConcrete [], QEnd (TInt, SConcrete []))],
   h)

let ref_settyp = F.(TArrowMod ([TInt], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TUnit))
let ref_gettyp = F.(TArrowMod ([], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TInt))

let with_ref =
  let ref_k = F.(TArrow ([ref_settyp; ref_gettyp], TInt)) in
  let ftyp = F.(TArrow ([ref_settyp; ref_gettyp],TInt)) in
  let stack = TAL.(SAbstract ([TTupleRef [TInt]; FTAL.tytrans ftyp], "z1")) in
  F.(ELam (dummy_loc, [("init", TInt);
            ("k", ref_k)],
           EApp (dummy_loc, ELam (dummy_loc, [("_", TUnit);
                        ("res", TInt);
                        ("_", TUnit)],
                      EVar (dummy_loc, "res")),
                 [EBoundary (dummy_loc, TUnit, Some (TAL.(SAbstract ([TTupleRef [TInt]], "z"))), (TAL.([
                      Iprotect (dummy_loc, [], "z");
                      Isalloc (dummy_loc, 1);
                      Iimport (dummy_loc, "r1", "z_", SAbstract ([], "z"), F.TInt, EVar (dummy_loc, "init"));
                      Isst (dummy_loc, 0, "r1");
                      Iralloc (dummy_loc, "r7", 1);
                      Isalloc (dummy_loc, 1);
                      Isst (dummy_loc, 0, "r7");
                      Imv (dummy_loc, "r1", UW (dummy_loc, WUnit dummy_loc));
                      Ihalt (dummy_loc, TUnit, SAbstract ([TTupleRef [TInt]], "z"), "r1")],
                      [])));
                  EApp (dummy_loc, EVar (dummy_loc, "k"),
                        [ELamMod (dummy_loc, [("x", TInt)],
                                  [TAL.(TTupleRef [TInt])],
                                  [TAL.(TTupleRef [TInt])],
                                  (EBoundary (dummy_loc, TUnit, Some stack,
                                              TAL.([Isld (dummy_loc, "r1", 0);
                                                    Iimport (dummy_loc, "r2", "z_",
                                                             stack,
                                                             F.TInt,
                                                             F.EVar (dummy_loc, "x"));
                                                    Ist (dummy_loc, "r1", 0, "r2");
                                                    Imv (dummy_loc, "r1", UW (dummy_loc, WUnit dummy_loc));
                                                    Ihalt (dummy_loc, TUnit, stack, "r1")], []))));
                         ELamMod (dummy_loc, [],
                                  [TAL.(TTupleRef [TInt])],
                                  [TAL.(TTupleRef [TInt])],
                                  (EBoundary (dummy_loc, TInt, Some stack,
                                              TAL.([Isld (dummy_loc, "r1", 0);
                                                    Ild (dummy_loc, "r2", "r1", 0);
                                                    Ihalt (dummy_loc, TInt, stack, "r2")], []))))]);
                  EBoundary (dummy_loc, TUnit, Some TAL.(SAbstract ([], "z")), (TAL.([
                      Iprotect (dummy_loc, [TTupleRef [TInt]], "z");
                      Isfree (dummy_loc, 1);
                      Imv (dummy_loc, "r1", UW (dummy_loc, WUnit dummy_loc));
                      Ihalt (dummy_loc, TUnit, SAbstract ([], "z"), "r1")],
                      []
                    )))])))


(* References *)

let ref_1 = F.(EApp (dummy_loc, with_ref, [EInt (dummy_loc, 1); ELam (dummy_loc, [("set", ref_settyp); ("get", ref_gettyp)],
                                              EApp (dummy_loc, ELam (dummy_loc, [("_", TUnit);
                                                           ("res", TInt)],
                                                          EVar (dummy_loc, "res")),
                                                    [EApp (dummy_loc, EVar (dummy_loc, "set"), [EInt (dummy_loc, 20)]);
                                                     EApp (dummy_loc, EVar (dummy_loc, "get"), [])]))]))


let ref_2 = F.(EApp (dummy_loc, with_ref, [EInt (dummy_loc, 1); ELam (dummy_loc, [("set", ref_settyp); ("get", ref_gettyp)],
                                              EApp (dummy_loc, ELam (dummy_loc, [("_", TUnit);
                                                           ("_", TUnit);
                                                           ("res", TInt)],
                                                          EVar (dummy_loc, "res")),
                                                    [EApp (dummy_loc, EVar (dummy_loc, "set"), [EInt (dummy_loc, 20)]);
                                                     EApp (dummy_loc, EVar (dummy_loc, "set"), [EBinop (dummy_loc, EApp (dummy_loc, EVar (dummy_loc, "get"), []), BPlus, EInt (dummy_loc, 5))]);
                                                     EApp (dummy_loc, EVar (dummy_loc, "get"), [])]))]))



(* Higher-order Profiling *)

(*
p = λf.let c = ref 0 in < λx.(c := !c + 1; f x),λ_.!c >
e1 = λf.λg.λa.let <g′,g'′> = p g in (f g′ ; g′ <> ; a g ′ ; g′′ <>)
e2 = λf.λg.λa.let <g′,g′′> = p g in (f g′ ; g <> ; a g′ ; g′′ <> + 1)
*)

let p =
  F.(ELam (dummy_loc, [("f", TArrow ([], TUnit));
            ("k", TArrow ([TArrow ([], TUnit); TArrow ([], TInt)], TInt))],
           EApp (dummy_loc, with_ref,
                 [EInt (dummy_loc, 0);
                  ELam (dummy_loc, [("set", ref_settyp); ("get", ref_gettyp)],
                        EApp (dummy_loc, EVar (dummy_loc, "k"),
                              [ELam (dummy_loc, [],
                                     EApp (dummy_loc, ELam (dummy_loc, [("_", TUnit); ("res", TUnit)], EVar (dummy_loc, "res")),
                                           [EApp (dummy_loc, EVar (dummy_loc, "set"), [EBinop (dummy_loc, EApp (dummy_loc, EVar (dummy_loc, "get"), []), BPlus, EInt (dummy_loc, 1))]);
                                            EApp (dummy_loc, EVar (dummy_loc, "f"), [])]));
                               EVar (dummy_loc, "get")]))])))


let profiling_1 = F.(EApp (dummy_loc, p,
                           [ELam (dummy_loc, [], EUnit dummy_loc);
                            ELam (dummy_loc, [("f'", TArrow ([], TUnit));
                                   ("get", TArrow ([], TInt))],
                                  EApp (dummy_loc, ELam (dummy_loc, [("_", TUnit);
                                               ("_", TUnit);
                                               ("res", TInt)],
                                              EVar (dummy_loc, "res")),
                                        [EApp (dummy_loc, EVar (dummy_loc, "f'"), []);
                                         EApp (dummy_loc, EVar (dummy_loc, "f'"), []);
                                         EApp (dummy_loc, EVar (dummy_loc, "get"), [])]))]))
