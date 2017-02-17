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
    (FTAL.FT (F.TInt), TAL.SConcrete []);;

let test_parse1 _ = assert_equal
  (Parse.parse_string Parser.component_eof {|
(
     mv r1, 1;
     add r1, r1, 1;
     halt int, * {r1}
;
)
|})
  TAL.([Imv ("r1", UW (WInt 1));
        Iaop (Add, "r1", "r1", UW (WInt 1));
        Ihalt (TInt, SConcrete [], "r1")], [], [])

let test2 _ = assert_equal
    (F.stepn 10 (empty, F.EBoundary (F.TInt, None,
                                     TAL.([Imv ("r1", UW (WInt 1));
                                           Iaop (Add, "r1", "r1", UW (WInt 1));
                                           Ihalt (TInt, SConcrete [], "r1")], [], []))))
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


let test_mv_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Imv ("r1", UW (WInt 1)); Ihalt (TInt, SConcrete [], "r1")],[], [])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_aop_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Imv ("r1", UW (WInt 1)); Iaop (Add,"r2","r1", UW (WInt 2)); Ihalt (TInt, SConcrete [], "r2")], [], [])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_import_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Iimport ("r1", "z", SConcrete [], F.TInt, F.EInt 10); Ihalt (TInt, SConcrete [], "r1")], [], [])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_salloc_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit; TUnit]))))
       (FTAL.TC TAL.([Imv ("r1", UW (WInt 1)); Isalloc 2; Ihalt (TInt, SConcrete [TUnit; TUnit], "r1")], [], [])))
    (FTAL.TT TAL.TInt, TAL.(SConcrete [TUnit; TUnit]))

let test_import_stk_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit]))))
       (FTAL.TC TAL.([Isalloc 3;
                      Iimport ("r1", "z'", SConcrete [TUnit], F.TInt,
                               F.EBoundary (F.TInt,
                                            Some (SAbstract ([TUnit],"z'")),
                                            (TAL.([Iprotect ([TUnit], "z");
                                                   Imv ("r1", UW (WInt 10));
                                                   Isfree 1;
                                                   Ihalt (TInt, SAbstract ([],"z"),
                                                          "r1")]),
                                             [], [])));
                      Isfree 1;
                      Ihalt (TInt, SConcrete [TUnit], "r1")], [], [])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [TAL.TUnit])

let test_sst_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TInt]))))
       (FTAL.TC TAL.([Imv ("r1", UW (WInt 1)); Isalloc 1; Isst (0,"r1"); Ihalt (TInt, SConcrete [TInt], "r1")], [],[])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [TAL.TInt])


let test_sld_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TUnit, SConcrete [TUnit]))))
       (FTAL.TC TAL.([Imv ("r1", UW (WInt 1)); Isalloc 1; Isld ("r2", 0); Ihalt (TUnit, SConcrete [TUnit], "r2")], [], [])))
    (FTAL.TT TAL.TUnit, TAL.SConcrete [TAL.TUnit])

let test_ld_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Imv ("r2", UW (WLoc "l"));
                      Ild ("r1", "r2", 0);
                      Ihalt (TInt, SConcrete [], "r1")],
                     [("l", HTuple [WInt 1])],
                     [("l", (Box, PTuple [TInt]))])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])


let test_ld2_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Imv ("r2", UW (WLoc "l"));
                      Ild ("r1", "r2", 0);
                      Ihalt (TInt, SConcrete [], "r1")],
                     [("l", HTuple [WInt 1])],
                     [("l", (Ref, PTuple [TInt]))])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_st_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.([Imv ("r1", UW (WLoc "l"));
                      Imv ("r2", UW (WInt 10));
                      Ist ("r1", 0, "r2");
                      Ihalt (TInt, SConcrete [], "r2")],
                     [("l", HTuple [WInt 1])],
                     [("l", (Ref, PTuple [TInt]))])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_factorial_f_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC factorial_f))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])

let test_factorial_t _ =
  assert_equal
    (snd (F.stepn 30 (empty, F.EApp (factorial_t, [F.EInt 3]))))
    (F.EInt 6)

let test_factorial_t_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC factorial_t))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])

let test_closures _ =
  let f = F.(ELam ([("x", TInt)],
                   EApp (EBoundary (TArrow ( [TInt], TInt), None,
                                    ([TAL.Iprotect ([], "z2");
                                      TAL.Iimport ("rf", "_z", TAL.SAbstract ([], "z2"), TArrow ([TInt], TInt), ELam ([("y", TInt)], EBinop (EVar "x", BMinus, EVar "y")));
                                      TAL.Ihalt (FTAL.tytrans (TArrow ([TInt], TInt)), TAL.SAbstract ([], "z2"), "rf")], [], [])),
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
              "F: 1 + 1 : int" >:: test1_ty;
              "F: 1 + 1 = 2" >:: test2;
              "F: (\\x -> x + x) 1 = 2" >:: test_f_app;
              "parse: 1 + 1 = 2" >:: test_parse1;
              "F: fact 3 = 6" >:: test_factorial_f;
              "F: fact : int -> int" >:: test_factorial_f_ty;
              "TAL: mv r1,1;halt r1 : int" >:: test_mv_ty;
              "TAL: mv r1,1; + r1,r1,1;halt r1 : int" >:: test_aop_ty;
              "TAL: import r1,1; halt r1 : int" >:: test_import_ty;
              "TAL: mv r1, 1; salloc 2; halt r1 : int" >:: test_salloc_ty;
              "TAL: import w/ stack mod : int" >:: test_import_stk_ty;
              "TAL: sst" >:: test_sst_ty;
              "TAL: sld" >:: test_sld_ty;
              "TAL: ld" >:: test_ld_ty;
              "TAL: ld" >:: test_ld2_ty;
              "TAL: st" >:: test_st_ty;
              "TAL: fact 3 = 6" >:: test_factorial_t;
              (* "TAL: int -> int" >:: test_factorial_t_ty; *)
              "FTAL: (\\x -> FT(TF(\\y -> x - y)) 1) 3 = 2" >:: test_closures;
              "TAL(1block): (\\x -> x + 2)3 = 5" >:: test_blocks1;
              "TAL(2blocks): (\\x -> x + 2)3 = 5" >:: test_blocks2;
              "REF: r = ref 1; r := 20; !r = 20" >:: test_ref1;
              "REF: r = ref 1; r := 20; r := !r + 5; !r = 25" >:: test_ref2;
              "PROFILING_1 = 2" >:: test_profiling1;
            ]


let () =
  run_test_tt_main suite
