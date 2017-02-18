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
                            [Isld ("rn", 0);
                             Imv ("r1", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SAbstract ([], "z3"))]));
                             Isfree 1;
                             Iret ("ra", "r1")])));
           (la, TAL.(Box, HCode ([DZeta "z4"],
                            [("r1", TInt); ("rn", TInt);
                             ("ra", TBox (PBlock ([],
                                                  [("r1", TInt)],
                                                  SAbstract ([], "z3"),
                                                  QEpsilon "e")))],
                            SAbstract ([TInt], "z3"),
                            QR "ra",
                            [Iaop (Mult, "r1", "r1", UR "rn");
                             Iaop (Sub, "rn", "rn", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SAbstract ([], "z1"))]));
                             Isfree 1;
                             Ihalt (TInt, SAbstract ([],  "z4"), "r1")])))] in
  let ht = TAL.([(lf, (Box, PBlock ([DZeta "z3"; DEpsilon "e"],
                                    [("ra", TBox (PBlock ([],
                                                          [("r1", TInt)],
                                                          SAbstract ([], "z3"),
                                                          QEpsilon "e")))],
                                    SAbstract ([TInt], "z3"),
                                    QR "ra")));
                 (la, (Box, PBlock ([DZeta "z4"],
                                    [("r1", TInt); ("rn", TInt);
                                     ("ra", TBox (PBlock ([],
                                                          [("r1", TInt)],
                                                          SAbstract ([], "z3"),
                                                          QEpsilon "e")))],
                                    SAbstract ([TInt], "z3"),
                                    QR "ra")))]) in
  (TAL.WLoc lf, h, ht)

let factorial_t =
  let (l, h, ht) = factorial_t' in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary (TArrow ([TInt], TInt), None,
                            TAL.([Iprotect ([], "z2");
                                  Imv ("r1", UW l);
                                  Ihalt (FTAL.tytrans (TArrow ([TInt], TInt)),
                                         SAbstract ([], "z2"),
                                         "r1")], h, ht)
),
                 [EVar "x"])))
(* Different number of basic blocks *)

let blocks_1 =
  let l = FTAL.gen_sym ~pref:"l" () in
  let h = [(l,
            TAL.(Box, HCode ([DZeta "z3"; DEpsilon "e"],
                        [("ra", TBox (PBlock ([], [("r1", TInt)], SAbstract ([], "z3"), QEpsilon "e")))],
                        SAbstract ([TInt], "z3"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Isfree 1;
                         Iret ("ra", "r1")])))] in
  let ht = [(l, TAL.(Box, PBlock ([DZeta "z3"; DEpsilon "e"],
                                  [("ra", TBox (PBlock ([],
                                                        [("r1", TInt)],
                                                        SAbstract ([], "z3"),
                                                        QEpsilon "e")))],
                                  SAbstract ([TInt], "z3"),
                                  QR "ra")))] in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary
                   (TArrow ([TInt], TInt),
                    None,
                    (TAL.([Iprotect ([], "z2");
                           Imv ("r1", UW (WLoc l));
                           Ihalt (FTAL.tytrans (TArrow ([TInt], TInt)),
                                  SAbstract ([], "z2"),
                                  "r1")],
                          h, ht))),
                 [EVar "x"])))


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
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Isst (0, "r1");
                         Ijmp (UApp (UW (WLoc l2), [OS (SAbstract ([], "z3"));
                                                    OQ (QEpsilon "e1")]))])));
                (l2,
                 (Box, HCode ([DZeta "z4"; DEpsilon "e2"],
                        [("ra", TBox (PBlock ([],
                                              [("r1", TInt)],
                                              SAbstract ([], "z4"),
                                              QEpsilon "e2")))],
                        SAbstract ([TInt], "z4"),
                        QR "ra",
                        [Isld ("r1", 0);
                         Iaop (Add, "r1", "r1", UW (WInt 1));
                         Isfree 1;
                         Iret ("ra", "r1")])))
               ]) in
  let ht = TAL.([(l1, (Box, PBlock ([DZeta "z3"; DEpsilon "e1"],
                                    [("ra", TBox (PBlock ([],
                                                          [("r1", TInt)],
                                                          SAbstract ([], "z3"),
                                                          QEpsilon "e1")))],
                                    SAbstract ([TInt], "z3"),
                                    QR "ra")));
                 (l2, (Box, PBlock ([DZeta "z4"; DEpsilon "e2"],
                                    [("ra", TBox (PBlock ([],
                                                          [("r1", TInt)],
                                                          SAbstract ([], "z4"),
                                                          QEpsilon "e2")))],
                                    SAbstract ([TInt], "z4"),
                                    QR "ra")))]) in
  F.(ELam ([("x", TInt)],
           EApp (EBoundary (TArrow ([TInt], TInt),
                            None,
                            (TAL.([Iprotect ([], "z2");
                                   Imv ("r1", UW (WLoc l1));
                                   Ihalt (FTAL.tytrans (TArrow ([TInt], TInt)),
                                          SAbstract ([], "z2"),
                                          "r1")], h, ht))),
                 [EVar "x"])))


let higher_order =
  let tau = F.(TArrow([TArrow([TInt],TInt)], TInt)) in
  let g = F.(ELam ([("h", TArrow ([TInt], TInt))], EApp (EVar "h", [EInt 1]))) in
  let h = TAL.([
      ("l", (Box, HCode ([DZeta "z1"; DEpsilon "e1"],
                   [("ra", TBox (PBlock ([],
                                         [("r1", TInt)],
                                         SAbstract ([], "z1"),
                                         QEpsilon "e1")))],
                   SAbstract ([FTAL.tytrans tau], "z1"),
                   QR "ra",
                   [Isld ("r1",0);
                    Isalloc 1;
                    Imv ("r2", UW (WLoc "lh"));
                    Isst (0, "r2");
                    Isst (1, "ra");
                    Imv ("ra", UApp (UW (WLoc "lgret"), [OS (SAbstract ([], "z1")); OQ (QEpsilon "e1")]));
                    Icall (UR "r1",
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
                    [Isld ("r1",0);
                     Isfree 1;
                     Iaop (Mult, "r1", "r1", UW (WInt 2));
                     Iret ("ra", "r1")])));
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
                       [Isld ("ra", 0);
                        Isfree 1;
                        Iret ("ra", "r1")])))]) in
  let ht = TAL.([]) in
  F.(EApp (EBoundary (TArrow([tau],TInt),
                      None,
                      TAL.([Imv("r1", UW (WLoc "l"));
                            Ihalt(FTAL.tytrans F.(TArrow([tau],TInt)),
                                  SConcrete [],
                                  "r1")],
                           h,
                           ht)),
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
                    [Isalloc 1; Isst (0, "ra"); Imv ("ra", UW (WLoc "l2ret"));
                     Icall (UW (WLoc "l2"),
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
                       [Ihalt (TInt, SConcrete [], "r1")])));
      ("l2", (Box, HCode ([DZeta "z2"; DEpsilon "e2"],
                    [("ra", TBox (PBlock ([],
                                          [("r1", TInt)],
                                          SAbstract ([], "z2"),
                                          QEpsilon "e2")))],
                    SAbstract ([], "z2"),
                    QR "ra",
                    [Imv ("r1", UW (WInt 1));
                     Ijmp (UApp (UW (WLoc "l2aux"),
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
                       [Iaop (Mult, "r1", "r1", UW (WInt 2));
                        Iret ("ra", "r1")])));
      ("l2ret", (Box, HCode ([],
                       [("r1", TInt)],
                       SConcrete [TBox (PBlock ([],
                                                [("r1", TInt)],
                                                SConcrete [],
                                                QEnd (TInt, SConcrete [])))],
                       QI 0,
                       [Isld ("ra", 0); Isfree 1; Iret ("ra", "r1")])))] in
  let ht = TAL.[("l1", (Box, PBlock ([DZeta "z1"; DEpsilon "e1"],
                                    [("ra", TBox (PBlock ([],
                                                          [("r1", TInt)],
                                                          SAbstract ([], "z1"),
                                                          QEpsilon "e1")))],
                                    SAbstract ([], "z1"),
                                    QR "ra")));
                ("l1ret", (Box, PBlock ([],
                                  [("r1", TInt)],
                                  SConcrete [],
                                  QEnd (TInt, SConcrete []))));
                ("l2", (Box, PBlock ([DZeta "z2"; DEpsilon "e2"],
                               [("ra", TBox (PBlock ([],
                                                     [("r1", TInt)],
                                                     SAbstract ([], "z2"),
                                                     QEpsilon "e2")))],
                               SAbstract ([], "z2"),
                               QR "ra")));
                ("l2aux", (Box, PBlock ([DZeta "z3"; DEpsilon "e3"],
                                  [("r1", TInt);
                                   ("ra", TBox (PBlock ([],
                                                        [("r1", TInt)],
                                                        SAbstract ([], "z3"),
                                                        QEpsilon "e3")))],
                                  SAbstract ([], "z3"),
                                  QR "ra")));
                ("l2ret", (Box, PBlock ([],
                                  [("r1", TInt)],
                                  SConcrete [TBox (PBlock ([],
                                                           [("r1", TInt)],
                                                           SConcrete [],
                                                           QEnd (TInt, SConcrete [])))],
                                  QI 0)))] in
  (TAL.[Imv ("ra", UW (WLoc "l1ret"));
        Icall (UW (WLoc "l1"), SConcrete [], QEnd (TInt, SConcrete []))],
   h,
   ht)

let ref_settyp = F.(TArrowMod ([TInt], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TUnit))
let ref_gettyp = F.(TArrowMod ([], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TInt))

let with_ref =
  let ref_k = F.(TArrow ([ref_settyp; ref_gettyp], TInt)) in
  let ftyp = F.(TArrow ([ref_settyp; ref_gettyp],TInt)) in
  let stack = TAL.(SAbstract ([TTupleRef [TInt]; FTAL.tytrans ftyp], "z1")) in
  F.(ELam ([("init", TInt);
            ("k", ref_k)],
           EApp (ELam ([("_", TUnit);
                        ("res", TInt);
                        ("_", TUnit)],
                      EVar "res"),
                 [EBoundary (TUnit, Some (TAL.(SAbstract ([TTupleRef [TInt]], "z"))), (TAL.([
                      Iprotect ([], "z");
                      Isalloc 1;
                      Iimport ("r1", "_", SAbstract ([], "z"), F.TInt, EVar "init");
                      Isst (0, "r1");
                      Iralloc ("rc", 1);
                      Isalloc 1;
                      Isst (0, "rc");
                      Imv ("r1", UW WUnit);
                      Ihalt (TUnit, SAbstract ([TTupleRef [TInt]], "z"), "r1")],
                      [], [])));
                  EApp (EVar "k",
                        [ELamMod ([("x", TInt)],
                                  [TAL.(TTupleRef [TInt])],
                                  [TAL.(TTupleRef [TInt])],
                                  (EBoundary (TUnit, Some stack,
                                              TAL.([Isld ("r1", 0);
                                                    Iimport ("r2", "_",
                                                             stack,
                                                             F.TInt,
                                                             F.EVar "x");
                                                    Ist ("r1", 0, "r2");
                                                    Imv ("r1", UW WUnit);
                                                    Ihalt (TUnit, stack, "r1")], [], []))));
                         ELamMod ([],
                                  [TAL.(TTupleRef [TInt])],
                                  [TAL.(TTupleRef [TInt])],
                                  (EBoundary (TInt, Some stack,
                                              TAL.([Isld ("r1", 0);
                                                    Ild ("r2", "r1", 0);
                                                    Ihalt (TInt, stack, "r2")], [], []))))]);
                  EBoundary (TUnit, Some TAL.(SAbstract ([], "z")), (TAL.([
                      Iprotect ([TTupleRef [TInt]], "z");
                      Isfree 1;
                      Imv ("r1", UW WUnit);
                      Ihalt (TUnit, SAbstract ([], "z"), "r1")],
                      [], []
                    )))])))


(* References *)

let ref_1 = F.(EApp (with_ref, [EInt 1; ELam ([("set", ref_settyp); ("get", ref_gettyp)],
                                              EApp (ELam ([("_", TUnit);
                                                           ("res", TInt)],
                                                          EVar "res"),
                                                    [EApp (EVar "set", [EInt 20]);
                                                     EApp (EVar "get", [])]))]))


let ref_2 = F.(EApp (with_ref, [EInt 1; ELam ([("set", ref_settyp); ("get", ref_gettyp)],
                                              EApp (ELam ([("_", TUnit);
                                                           ("_", TUnit);
                                                           ("res", TInt)],
                                                          EVar "res"),
                                                    [EApp (EVar "set", [EInt 20]);
                                                     EApp (EVar "set", [EBinop (EApp (EVar "get", []), BPlus, EInt 5)]);
                                                     EApp (EVar "get", [])]))]))



(* Higher-order Profiling *)

(*
p = λf.let c = ref 0 in < λx.(c := !c + 1; f x),λ_.!c >
e1 = λf.λg.λa.let <g′,g'′> = p g in (f g′ ; g′ <> ; a g ′ ; g′′ <>)
e2 = λf.λg.λa.let <g′,g′′> = p g in (f g′ ; g <> ; a g′ ; g′′ <> + 1)
*)

let p =
  F.(ELam ([("f", TArrow ([], TUnit));
            ("k", TArrow ([TArrow ([], TUnit); TArrow ([], TInt)], TInt))],
           EApp (with_ref,
                 [EInt 0;
                  ELam ([("set", ref_settyp); ("get", ref_gettyp)],
                        EApp (EVar "k",
                              [ELam ([],
                                     EApp (ELam ([("_", TUnit); ("res", TUnit)], EVar "res"),
                                           [EApp (EVar "set", [EBinop (EApp (EVar "get", []), BPlus, EInt 1)]);
                                            EApp (EVar "f", [])]));
                               EVar "get"]))])))


let profiling_1 = F.(EApp (p,
                           [ELam ([], EUnit);
                            ELam ([("f'", TArrow ([], TUnit));
                                   ("get", TArrow ([], TInt))],
                                  EApp (ELam ([("_", TUnit);
                                               ("_", TUnit);
                                               ("res", TInt)],
                                              EVar "res"),
                                        [EApp (EVar "f'", []);
                                         EApp (EVar "f'", []);
                                         EApp (EVar "get", [])]))]))
