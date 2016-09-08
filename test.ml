open OUnit2;;
open Ftal;;

let empty = ([],[],[])

let test1 _ = assert_equal
    (F.stepn 10 (empty, F.EBinop (F.EInt 1, F.BPlus, F.EInt 1)))
    (empty, F.EInt 2);;

let test2 _ = assert_equal
    (F.stepn 10 (empty, F.EBoundary (F.TInt, TAL.([Imv ("r1", UW (WInt 1));
                                                   Iaop (Add, "r1", "r1", UW (WInt 1));
                                                   Iret (QEnd (TInt, SNil), "r1")], []))))
    (([], [("r1", TAL.WInt 2)], []), F.EInt 2)

let test_f_app _ =
  assert_equal
    (F.stepn 10 (empty, F.(EApp
                             (ELam ("z", [("x", TInt)], EBinop (EVar "x", BPlus, EVar "x")),
                             [],
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
                                                                         [TAL.SZeta "z3"],
                                                                         [EVar "f"]),
                                                                   [TAL.SZeta "z3"],
                                                                   [EBinop (EVar "x1", BMinus, EInt 1)])))))) in
  let fact = F.(ELam ("z4", [("x2", TInt)],
                      EApp (EApp (f, [TAL.SZeta "z4"], [EFold ("b",
                                                               TArrow ("z5", [TVar "b"], TInt),
                                                               f)]),
                            [TAL.SZeta "z4"],
                            [EVar "x2"]))) in
  (* let () = print_endline (F.show_exp (snd (F.stepn 100 (empty, F.EApp (fact, [], [F.EInt 3]))))) in *)
  assert_equal
    (snd (F.stepn 100 (empty, F.EApp (fact, [], [F.EInt 3]))))
    (F.EInt 6)


let test_factorial_t _ =
  let lf = FTAL.gen_sym () in
  let la = FTAL.gen_sym () in
  let h = [(lf, TAL.(HCode ([DZeta "z1";DEpsilon "e"],
                            [],
                            SCons (TInt, SZeta "z1"),
                            QEnd (TInt, SZeta "z1"),
                            [Isld ("rn", 0); Imv ("rr", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SZeta "z1"); OQ (QEpsilon "e")]));
                             Isfree 1;
                             Iret (QEnd (TInt, SZeta "z1"), "rr")])));
           (la, TAL.(HCode ([DZeta "z1";DEpsilon "e"],
                            [("rr", TInt); ("ri", TInt); ("rn", TInt)],
                            SCons (TInt, SZeta "z1"),
                            QEnd (TInt, SZeta "z1"),
                            [Iaop (Mult, "rr", "rr", UR "rn");
                             Iaop (Sub, "rn", "rn", UW (WInt 1));
                             Ibnz ("rn", UApp (UW (WLoc la), [OS (SZeta "z1"); OQ (QEpsilon "e")]));
                             Isfree 1;
                             Iret (QEnd (TInt, SZeta "z1"), "rr")])))] in
  let fact = F.(ELam ("z1", [("x", TInt)],
                      EApp (EBoundary (TArrow ("z2", [TInt], TInt),
                                       ([TAL.(Imv ("r1", UW (WLoc lf))); TAL.(Iret (QEnd (FTAL.tytrans (TArrow ("z2", [TInt], TInt)), SZeta "z2"), "r1"))], h)),
                            [TAL.SCons (TAL.TInt, TAL.SZeta "z1")],
                            [EVar "x"]))) in
  assert_equal
    (snd (F.stepn 100 (empty, F.EApp (fact, [], [F.EInt 3]))))
    (F.EInt 6)



let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "TAL: 1 + 1 = 2" >:: test2;
              "F: (\x -> x + x) 1 = 2" >:: test_f_app;
              "F: fact 3 = 6" >:: test_factorial_f;
              "TAL: fact 3 = 6" >:: test_factorial_t;
            ]
;;

let () =
  run_test_tt_main suite
;;
