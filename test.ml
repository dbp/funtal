open OUnit2;;
open Ftal;;

let empty = ([],[],[])

let test1 _ = assert_equal
    (F.stepn 10 (empty, F.EBinop (F.EInt 1, F.BPlus, F.EInt 1)))
    (empty, F.EInt 2);;

let test1_ty _ = assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (F.EBinop (F.EInt 1, F.BPlus, F.EInt 1))))
    (FTAL.FT (F.TInt), TAL.SNil);;

let test2 _ = assert_equal
    (F.stepn 10 (empty, F.EBoundary (F.TInt, TAL.SNil,
                                     TAL.([Imv ("r1", UW (WInt 1));
                                           Iaop (Add, "r1", "r1", UW (WInt 1));
                                           Iret (QEnd (TInt, SNil), "r1")], []))))
    (([], [("r1", TAL.WInt 2)], []), F.EInt 2)

let test_f_app _ =
  assert_equal
    (F.stepn 10 (empty, F.(EApp
                             (ELam ("z", [("x", TInt)], EBinop (EVar "x", BPlus, EVar "x")),
                             TAL.SNil,
                             [EInt 1]))))
    (empty, F.EInt 2)

(* NOTE(dbp 2016-09-07): I'm confused about binding for zetas - are
   they _all_ the same?  It doesn't actually matter for now, as they have
   no runtime consequences, but... *)
let test_factorial_f _ =
  let f = F.(ELam ("z1", [("f", TRec ("a", TArrow ("z2", [TVar "a"], TInt)))],
                   ELam ("z3", [("x1", TInt)], EIf0 (EVar "x1",
                                                     EInt 1,
                                                     EBinop (EVar "x1",
                                                             BTimes,
                                                             EApp (EApp (EUnfold (EVar "f"),
                                                                         TAL.SZeta "z3",
                                                                         [EVar "f"]),
                                                                   TAL.SZeta "z3",
                                                                   [EBinop (EVar "x1", BMinus, EInt 1)])))))) in
  let fact = F.(ELam ("z4", [("x2", TInt)],
                      EApp (EApp (f, TAL.SZeta "z4", [EFold ("b",
                                                               TArrow ("z5", [TVar "b"], TInt),
                                                               f)]),
                            TAL.SZeta "z4",
                            [EVar "x2"]))) in
  (* let () = print_endline (F.show_exp (snd (F.stepn 100 (empty, F.EApp (fact, [], [F.EInt 3]))))) in *)
  assert_equal
    (snd (F.stepn 100 (empty, F.EApp (fact, TAL.SNil, [F.EInt 3]))))
    (F.EInt 6)


let test_factorial_t _ =
  let lf = FTAL.gen_sym () in
  let la = FTAL.gen_sym () in
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
  let fact = F.(ELam ("z1", [("x", TInt)],
                      EApp (EBoundary (TArrow ("z2", [TInt], TInt), TAL.SZeta "z2",
                                       ([TAL.(Imv ("r1", UW (WLoc lf))); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ("z1", [TInt], TInt)), SZeta "z2"), "r1"))], h)),
                            TAL.SZeta "z1",
                            [EVar "x"]))) in
  assert_equal
    (snd (F.stepn 30 (empty, F.EApp (fact, TAL.SNil, [F.EInt 3]))))
    (F.EInt 6)

let test_closures _ =
  let f = F.(ELam ("z", [("x", TInt)],
                   EApp (EBoundary (TArrow ("z2", [TInt], TInt), TAL.SZeta "z3",
                                    ([TAL.Iimport ("rf", TAL.SZeta "z2", TArrow ("z3", [TInt], TInt), ELam ("z3", [("y", TInt)], EBinop (EVar "x", BMinus, EVar "y"))); TAL.Iret (TAL.QEnd (FTAL.tytrans (TArrow ("z3", [TInt], TInt)), TAL.SZeta "z3"), "rf")], [])),
                         TAL.SZeta "z",
                         [EInt 1]))) in
  assert_equal
    (snd (F.stepn 40 (empty, F.EApp (f, TAL.SNil, [F.EInt 3]))))
    (F.EInt 2)


let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "1 + 1 : int" >:: test1_ty;
              "TAL: 1 + 1 = 2" >:: test2;
              "F: (\x -> x + x) 1 = 2" >:: test_f_app;
              "F: fact 3 = 6" >:: test_factorial_f;
              "TAL: fact 3 = 6" >:: test_factorial_t;
              "FTAL: (\x -> FT(TF(\y -> x - y)) 1) 3 = 2" >:: test_closures
            ]
;;

let () =
  run_test_tt_main suite
;;
