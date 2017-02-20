open Ftal;;


(* Factorial Two Ways *)

let factorial_f = Parse.parse_string Parser.f_expression_eof {|
  lam (x2:int).
    (lam (fact : (mu a.(a, int) -> int, int) -> int).
       fact (fold (mu b.(b, int) -> int) fact) x2)
      (lam (f:mu a.(a, int) -> int, x1:int).
          if0 x1 1 (x1*((unfold f) f (x1-1))))
|}

let factorial_t' =
  let lf = FTAL.gen_sym ~pref:"lf" () in
  let la = FTAL.gen_sym ~pref:"la" () in
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

let factorial_t = Parse.parse_string Parser.f_expression_eof {|
lam (x:int).
  FT[(int) -> int, ?]
    ([protect , z2;
      mv r1, lf0;
      halt
        box forall[z2, e3].
          {ra : box forall[].{r1 : int; z2} e3;
           int :: z2} ra,
        z2 {r1}],
      [lf0 -> box code [z3, e]{ra : box forall[].{r1 : int; z3} e;
                              int :: z3} ra.
                [sld r7, 0; mv r1, 1; bnz r7, la1[z3]; sfree 1; ret ra {r1}],
       la1 -> box code [z4]{r1 : int,
                            r7 : int,
                            ra : box forall[].{r1 : int; z3} e;
                           int :: z3} ra.
                [mul r1, r1, r7;
                 sub r7, r7, 1;
                 bnz r7, la1[z1];
                 sfree 1;
                 halt int, z4 {r1}]])
    x
|}
(* Different number of basic blocks *)

let blocks_1 = Parse.parse_string Parser.f_expression_eof {|
lam (x:int).
  FT[(int) -> int, ?]
    ([protect , z2;
      mv r1, l2;
      halt
        box forall[z3, e4].
          {ra : box forall[].{r1 : int; z3} e4;
           int :: z3} ra,
        z2 {r1}],
      [l2 -> box code [z3, e]{ra : box forall[].{r1 : int; z3} e;
                             int :: z3} ra.
               [sld r1, 0; add r1, r1, 1; add r1, r1, 1; sfree 1; ret ra {r1}]])
    x
|}

let blocks_2 = Parse.parse_string Parser.f_expression_eof {|
lam (x:int).
  FT[(int) -> int, ?]
    ([protect , z2;
      mv r1, l2;
      halt
        box forall[z4, e5].
          {ra : box forall[].{r1 : int; z4} e5;
           int :: z4} ra,
        z2 {r1}],
      [l2 -> box code [z3, e1]{ra : box forall[].{r1 : int; z3} e1;
                              int :: z3} ra.
               [sld r1, 0; add r1, r1, 1; sst 0, r1; jmp l3[z3, e1]],
       l3 -> box code [z4, e2]{ra : box forall[].{r1 : int; z4} e2;
                              int :: z4} ra.
               [sld r1, 0; add r1, r1, 1; sfree 1; ret ra {r1}]])
    x
|}

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
                      TAL.(dummy_loc, [Imv(dummy_loc, "r1", UW (dummy_loc, WLoc (dummy_loc, "l")));
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
  (dummy_loc, TAL.[Imv (dummy_loc, "ra", UW (dummy_loc, WLoc (dummy_loc, "l1ret")));
        Icall (dummy_loc, UW (dummy_loc, WLoc (dummy_loc, "l1")), SConcrete [], QEnd (TInt, SConcrete []))],
   h)

let ref_settyp = F.(TArrowMod ([TInt], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TUnit))
let ref_gettyp = F.(TArrowMod ([], [TAL.(TTupleRef [TInt])], [TAL.(TTupleRef [TInt])], TInt))

let with_ref = Parse.parse_string Parser.f_expression_eof {|
lam (init:int, k:((int)[ref <int>] -> [ref <int>]unit,
                   ()[ref <int>] -> [ref <int>]int) -> int).
  (lam (_:unit, res:int, _:unit). res)
    FT[unit, ref <int> :: z]
      ([protect , z;
        salloc 1;
        import r1, z_ as z, int TF{init};
        sst 0, r1;
        ralloc r7, 1;
        salloc 1;
        sst 0, r7;
        mv r1, ();
        halt unit, ref <int> :: z {r1}],
        [])
    (k
      (lam [ref <int>][ref <int>](x:int).
        FT[unit,
           ref <int>
             :: box forall[z12, e13].
               {ra : box forall[].{r1 : int; z12} e13;
                box forall[z14, e15].
                    {ra : box forall[].{r1 : unit; ref <int> :: z14} e15;
                     int :: ref <int> :: z14} ra
                  :: box forall[z16, e17].
                    {ra : box forall[].{r1 : int; ref <int> :: z16} e17;
                     ref <int> :: z16} ra :: z12} ra :: z1]
            ([sld r1, 0;
              import
                r2,
                z_ as ref <int>
                  :: box forall[z12, e13].
                    {ra : box forall[].{r1 : int; z12} e13;
                     box forall[z14, e15].
                         {ra : box forall[].{r1 : unit; ref <int> :: z14} e15;
                          int :: ref <int> :: z14} ra
                       :: box forall[z16, e17].
                         {ra : box forall[].{r1 : int; ref <int> :: z16} e17;
                          ref <int> :: z16} ra :: z12} ra :: z1,
                int TF{x};
              st r1[0], r2;
              mv r1, ();
              halt
                unit,
                ref <int>
                  :: box forall[z12, e13].
                    {ra : box forall[].{r1 : int; z12} e13;
                     box forall[z14, e15].
                         {ra : box forall[].{r1 : unit; ref <int> :: z14} e15;
                          int :: ref <int> :: z14} ra
                       :: box forall[z16, e17].
                         {ra : box forall[].{r1 : int; ref <int> :: z16} e17;
                          ref <int> :: z16} ra :: z12} ra :: z1 {r1}],
              []))
      (lam [ref <int>][ref <int>]().
        FT[int,
           ref <int>
             :: box forall[z12, e13].
               {ra : box forall[].{r1 : int; z12} e13;
                box forall[z14, e15].
                    {ra : box forall[].{r1 : unit; ref <int> :: z14} e15;
                     int :: ref <int> :: z14} ra
                  :: box forall[z16, e17].
                    {ra : box forall[].{r1 : int; ref <int> :: z16} e17;
                     ref <int> :: z16} ra :: z12} ra :: z1]
            ([sld r1, 0;
              ld r2, r1[0];
              halt
                int,
                ref <int>
                  :: box forall[z12, e13].
                    {ra : box forall[].{r1 : int; z12} e13;
                     box forall[z14, e15].
                         {ra : box forall[].{r1 : unit; ref <int> :: z14} e15;
                          int :: ref <int> :: z14} ra
                       :: box forall[z16, e17].
                         {ra : box forall[].{r1 : int; ref <int> :: z16} e17;
                          ref <int> :: z16} ra :: z12} ra :: z1 {r2}],
              [])))
    FT[unit, z]
      ([protect ref <int>, z; sfree 1; mv r1, (); halt unit, z {r1}],
        [])
|}

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
