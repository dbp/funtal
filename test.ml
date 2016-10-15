open OUnit2;;
open Ftal;;
open Examples;;

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


let test_factorial_f _ =
  assert_equal
    (snd (F.stepn 100 (empty, F.EApp (factorial_f, TAL.SNil, [F.EInt 3]))))
    (F.EInt 6)

let test_factorial_f_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC factorial_f))
    (FTAL.FT (F.TArrow ("z4", [F.TInt], F.TInt)), TAL.SNil);;

let test_factorial_t _ =
  assert_equal
    (snd (F.stepn 30 (empty, F.EApp (factorial_t, TAL.SNil, [F.EInt 3]))))
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

let test_blocks1 _ =
  assert_equal
    (snd (F.stepn 20 (empty, F.EApp (blocks_1, TAL.SNil, [F.EInt 3]))))
    (F.EInt 5)

let test_blocks2 _ =
  assert_equal
    (snd (F.stepn 20 (empty, F.EApp (blocks_2, TAL.SNil, [F.EInt 3]))))
    (F.EInt 5)


let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "1 + 1 : int" >:: test1_ty;
              "TAL: 1 + 1 = 2" >:: test2;
              "F: (\x -> x + x) 1 = 2" >:: test_f_app;
              "F: fact 3 = 6" >:: test_factorial_f;
              "fact : int -> int" >:: test_factorial_f_ty;
              "TAL: fact 3 = 6" >:: test_factorial_t;
              "FTAL: (\x -> FT(TF(\y -> x - y)) 1) 3 = 2" >:: test_closures;
              "TAL(1block): (\x -> x + 2)3 = 5" >:: test_blocks1;
              "TAL(2blocks): (\x -> x + 2)3 = 5" >:: test_blocks2;
            ]
;;

let () =
  run_test_tt_main suite
;;
