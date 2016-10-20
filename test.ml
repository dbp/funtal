open OUnit2;;
open Ftal;;
open Examples;;

let empty = ([],[],[])

let test1 _ = assert_equal
    (F.stepn 10 (empty, F.EBinop (F.EInt 1, F.BPlus, F.EInt 1)))
    (empty, F.EInt 2);;

(* let test1_ty _ = assert_equal *)
(*     (FTAL.tc *)
(*        (FTAL.default_context TAL.QOut) *)
(*        (FTAL.FC (F.EBinop (F.EInt 1, F.BPlus, F.EInt 1)))) *)
(*     (FTAL.FT (F.TInt), TAL.SNil);; *)

let test2 _ = assert_equal
    (F.stepn 10 (empty, F.EBoundary (F.TInt,
                                     TAL.([Imv ("r1", UW (WInt 1));
                                           Iaop (Add, "r1", "r1", UW (WInt 1));
                                           Iret (QEnd (TInt, SConcrete []), "r1")], []))))
    (([], [("r1", TAL.WInt 2)], []), F.EInt 2)

let test_f_app _ =
  assert_equal
    (F.stepn 10 (empty, F.(EApp
                             (ELam ([("x", TInt)], EBinop (EVar "x", BPlus, EVar "x")),
                             [EInt 1]))))
    (empty, F.EInt 2)


let test_factorial_f _ =
  assert_equal
    (snd (F.stepn 100 (empty, F.EApp (factorial_f, [F.EInt 3]))))
    (F.EInt 6)

(* let test_factorial_f_ty _ = *)
(*   assert_equal *)
(*     (FTAL.tc *)
(*        (FTAL.default_context TAL.QOut) *)
(*        (FTAL.FC factorial_f)) *)
(*     (FTAL.FT (F.TArrow ("z4", [F.TInt], F.TInt)), TAL.SNil);; *)

let test_factorial_t _ =
  assert_equal
    (snd (F.stepn 30 (empty, F.EApp (factorial_t, [F.EInt 3]))))
    (F.EInt 6)

let test_closures _ =
  let f = F.(ELam ([("x", TInt)],
                   EApp (EBoundary (TArrow ( [TInt], TInt),
                                    ([TAL.Iprotect ([], "z2");
                                      TAL.Iimport ("rf", TAL.SAbstract ([], "z2"), TArrow ([TInt], TInt), ELam ([("y", TInt)], EBinop (EVar "x", BMinus, EVar "y")));
                                      TAL.Iret (TAL.QEnd (FTAL.tytrans (TArrow ([TInt], TInt)), TAL.SAbstract ([], "z2")), "rf")], [])),
                         [EInt 1]))) in
  assert_equal
    (snd (F.stepn 40 (empty, F.EApp (f, [F.EInt 3]))))
    (F.EInt 2)

let test_blocks1 _ =
  assert_equal
    (snd (F.stepn 20 (empty, F.EApp (blocks_1, [F.EInt 3]))))
    (F.EInt 5)

let test_blocks2 _ =
  assert_equal
    (snd (F.stepn 20 (empty, F.EApp (blocks_2, [F.EInt 3]))))
    (F.EInt 5)

let test_ref1 _ =
  assert_equal
    (snd (F.stepn 50 (empty, ref_1)))
    (F.EInt 20)

let test_ref2 _ =
  assert_equal
    (snd (F.stepn 50 (empty, ref_2)))
    (F.EInt 25)

let test_profiling1 _ =
  assert_equal
    (snd (F.stepn 70 (empty, profiling_1)))
    (F.EInt 2)


let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              (* "1 + 1 : int" >:: test1_ty; *)
              "TAL: 1 + 1 = 2" >:: test2;
              "F: (\x -> x + x) 1 = 2" >:: test_f_app;
              "F: fact 3 = 6" >:: test_factorial_f;
              (* "fact : int -> int" >:: test_factorial_f_ty; *)
              "TAL: fact 3 = 6" >:: test_factorial_t;
              "FTAL: (\x -> FT(TF(\y -> x - y)) 1) 3 = 2" >:: test_closures;
              "TAL(1block): (\x -> x + 2)3 = 5" >:: test_blocks1;
              "TAL(2blocks): (\x -> x + 2)3 = 5" >:: test_blocks2;
              "REF: r = ref 1; r := 20; !r = 20" >:: test_ref1;
              "REF: r = ref 1; r := 20; r := !r + 5; !r = 25" >:: test_ref2;
              "PROFILING_1 = 2" >:: test_profiling1;
            ]
;;

let () =
  run_test_tt_main suite
;;
