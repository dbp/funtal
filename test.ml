open OUnit2;;
open Ftal;;
open Examples;;
let f_expr str = Parse.parse_string Parser.f_expression_eof str

let roundtrip ?source comp =
  let orig, roundtrip =
    Filename.temp_file ~temp_dir:"." "orig" ".ftal",
    Filename.temp_file ~temp_dir:"." "roundtrip" ".ftal" in
  let write_source () =
    match source with
      | None -> ()
      | Some str ->
        let chan = open_out orig in
        output_string chan str;
        flush chan;
        close_out chan;
  in
  let write_result () =
    let doc = TALP.p_component comp in
    let chan = open_out roundtrip in
    PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
    flush chan;
    close_out chan;
  in
  write_source ();
  write_result ();
  match Parse.parse_file Parser.component_eof roundtrip with
  | exception exn ->
    Printf.eprintf "%!\nRountrip failure %S %S%!\n" orig roundtrip;
    comp
  | roundtripped_comp ->
    Sys.remove orig; Sys.remove roundtrip;
    roundtripped_comp

let tal_comp str =
  roundtrip ~source:str (Parse.parse_string Parser.component_eof str)

let empty = ([],[],[])

let assert_eint e n =
  match e with
  | F.EInt (_, x) -> assert_equal x n
  | _ -> assert_failure "not equal"


let test1 _ = assert_eint
    (snd (F.stepn 10 (empty, f_expr "1 + 1")))
    2

let test1_ty _ = assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (f_expr "1 + 1")))
    (FTAL.FT F.TInt, TAL.SConcrete []);;

let test2 _ =
  assert_eint
    (snd (F.stepn 10 (empty, F.EBoundary (dummy_loc, F.TInt, None,
                                          (tal_comp
                                             "([mv r1, 1;
                                          add r1, r1, 1;
                                          halt int, * {r1};],
                                          [])")))))
    2

let test_f_app _ =
  assert_eint
    (snd (F.stepn 10 (empty, f_expr "(lam (x:int). x + x) 1")))
    2

let test_factorial_f _ =
  assert_eint
    (snd (F.stepn 300 (empty, F.EApp (dummy_loc, factorial_f, [F.EInt (dummy_loc, 3)]))))
    6

let test_mv_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp "([mv r1, 1; halt int, * {r1};], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_aop_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp "([mv r1, 1; add r2, r1, 2; halt int, * {r2}], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let assert_raises_typeerror (f : unit -> 'a) : unit =
  FTAL.(try (f (); assert_failure "didn't raise an exception")
        with TypeError _  -> ())

let test_aop_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
        (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
        (FTAL.TC (tal_comp "([mv r1, (); add r2, r1, 2; halt int, * {r2}], [])")))

let test_aop_ty_exc2 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
        (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
        (FTAL.TC (tal_comp "([mv r1, 1; add r2, r1, (); halt int, * {r2}], [])")))

let test_aop_ty_exc3 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
        (FTAL.default_context (TAL.QR "r2"))
        (FTAL.TC (tal_comp "([mv r1, 1; add r2, r1, 1; halt int, * {r2}], [])")))


let test_import_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC
          (tal_comp "([import r1, z as *, int TF{10}; halt int, * {r1}], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])


let test_import_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC
          (tal_comp "([import r1, z as *, int TF{()}; halt int, * {r1}], [])")))

let test_import_ty_exc2 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.(dummy_loc, [Iimport (dummy_loc, "r1", "z", SConcrete [], F.TUnit, F.EInt (dummy_loc, 1)); Ihalt (dummy_loc, TInt, SConcrete [], "r1")], [])))

let test_import_ty_exc3 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC TAL.(dummy_loc, [Iimport (dummy_loc, "r1", "z", SConcrete [TUnit], F.TInt, F.EInt (dummy_loc, 1)); Ihalt (dummy_loc, TInt, SConcrete [], "r1")], [])))

let test_salloc_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit; TUnit]))))
       (FTAL.TC TAL.(dummy_loc, [Imv (dummy_loc, "r1", UW (dummy_loc, WInt (dummy_loc, 1))); Isalloc (dummy_loc, 2); Ihalt (dummy_loc, TInt, SConcrete [TUnit; TUnit], "r1")], [])))
    (FTAL.TT TAL.TInt, TAL.(SConcrete [TUnit; TUnit]))

let test_import_stk_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit]))))
       (FTAL.TC (tal_comp "([salloc 3;
                             import r1, z' as unit::*, int TF{
                               FT [int, unit::z'] (
                                 [protect unit::, z;
                                  mv r1, 10;
                                  sfree 1;
                                  halt int, z {r1}]
                               ,
                                 []
                               )
                             };
                             sfree 1;
                             halt int, unit::* {r1};
                           ], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [TAL.TUnit])

let test_sst_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TInt]))))
       (FTAL.TC TAL.(dummy_loc, [Imv (dummy_loc, "r1", UW (dummy_loc, WInt (dummy_loc, 1))); Isalloc (dummy_loc, 1); Isst (dummy_loc, 0,"r1"); Ihalt (dummy_loc, TInt, SConcrete [TInt], "r1")],[])))
    (FTAL.TT TAL.TInt, TAL.SConcrete [TAL.TInt])


let test_sld_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TUnit, SConcrete [TUnit]))))
       (FTAL.TC (tal_comp
                   "([mv r1, 1; salloc 1; sld r2, 0; halt unit, unit::* {r2}],
                     [])")))
    (FTAL.TT TAL.TUnit, TAL.SConcrete [TAL.TUnit])

let test_ld_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([
                       mv r2, l;
                       ld r1, r2[0];
                       halt int, * {r1};
                    ], [l -> box <1>])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_ld2_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([
                       mv r2, l;
                       ld r1, r2[0];
                       halt int, * {r1};
                     ],
                     [l -> ref <1>]
                   )")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_st_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([
                     mv r1, l;
                     mv r2, 10;
                     st r1[0], r2;
                     halt int, * {r2};
                     ],
                     [l -> ref <1>]
                   )")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_ralloc_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([
                       mv r1, 1;
                       salloc 1;
                       sst 0, r1;
                       ralloc r2, 1;
                       mv r1, 10;
                       st r2[0], r1;
                       ld r3, r2[0];
                       halt int, * {r3};
                     ], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_balloc_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit]))))
       (FTAL.TC (tal_comp
                   "([
                       mv r1, 1;
                       salloc 2;
                       sst 0, r1;
                       balloc r2, 1;
                       ld r3, r2[0];
                       halt int, unit::* {r3}
                     ], [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [TAL.TUnit])

let test_balloc_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
        (FTAL.default_context (TAL.(QEnd (TInt, SConcrete [TUnit]))))
        (FTAL.TC (tal_comp
                    "([
                        mv r1, 1;
                        salloc 2;
                        sst 0, r1;
                        balloc r2, 1;
                        st r2[0], r1;
                        ld r3, r2[0];
                        halt int, unit::* {r3}
                      ], [])")))

(* NOTE(dbp 2017-02-17): Writing a "small" example using unpack
   is actually quite hard, because we really need large values &
   functions in order to do anything useful, which then involves
   jumps, calls, etc... So these are dumb tests, but... bleh. *)

let test_unpack_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TUnit, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([unpack <a, r2>, pack <int, 1> as exists a. a;
                      mv r1, ();
                      halt unit, * {r1}],
                     [])")))
    (FTAL.TT TAL.TUnit, TAL.SConcrete [])

let test_parse5 _ =
  (* check that parentheses are allowed: unpack <a, r>, (u); *)
  assert_equal
    (tal_comp
       "([unpack <a, r2>, pack <int, 1> as exists a. a;
          mv r1, ();
          halt unit, * {r1}], [])")
    (tal_comp
       "([unpack <a, r2>, (pack <int, 1> as exists a. a);
          mv r1, ();
          halt unit, * {r1}], [])")


let test_unpack_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
        (FTAL.default_context (TAL.(QEnd (TUnit, SConcrete []))))
        (FTAL.TC (tal_comp
                    "([unpack <a, r2>, 10;
                       mv r1, ();
                       halt unit, * {r1}], [])")))

(* NOTE(dbp 2017-02-17): Like unpack, non-trivial unfold really needs
   large values. But we can do trivial ones easily! *)
let test_unfold_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([unfold r1, fold mu a. int 1;
                      halt int, * {r1}],
                     [])")))
    (FTAL.TT TAL.TInt, TAL.SConcrete [])

let test_unfold_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context (TAL.(QEnd (TInt, SConcrete []))))
       (FTAL.TC (tal_comp
                   "([unfold r1, 1;
                      halt int, * {r1};]
                   , [])")))

let call_tl =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [mv r1, 10;
                ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_tl _ =
  assert_eint (snd (F.stepn 30 (empty, call_tl))) 10

let test_call_tl_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_tl))
    (FTAL.FT F.TInt, TAL.SConcrete [])


let call_tl_exc =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; int :: z} ra.
               [sld r1, 0;
                sfree 1;
                ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_tl_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_tl_exc))

let call_tl_exc2 =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         salloc 1; mv r1, 0; sst 0, r1;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; int :: z} ra.
               [sld r1, 0;
                ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_tl_ty_exc2 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_tl_exc2))

let call_tl_exc3 =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         salloc 1; mv r1, 0; sst 0, r1;
         call l {int::int::*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; int :: z} ra.
               [sld r1, 0; sfree 1;
                ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_tl_ty_exc3 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_tl_exc3))


let call_tl_exc4 =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         salloc 1; mv r1, 0; sst 0, r1;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e, r1 : unit; int :: z} ra.
               [sld r1, 0; sfree 1;
                ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_tl_ty_exc4 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_tl_exc4))

let call_st =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z1, e1]
               {ra: box forall[]. {r1:int; z1} e1; z1} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h[z1,e1];
                call l1 {box forall[]. {r1:int; z1} e1 :: z1, 0}],
         l1 -> box code [z2, e]
               {ra: box forall[]. {r1:int; z2} e; z2} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [z3,e3] {r1:int; box forall[]. {r1:int; z3} e3 :: z3} 0.
                    [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}.
                    [halt int, * {r1}]])")

let test_call_st _ =
  assert_eint (snd (F.stepn 30 (empty, call_st))) 0

let test_call_st_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_st))
    (FTAL.FT F.TInt, TAL.SConcrete [])

let call_st_exc =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h;
                call l1 {*, 0}],
         l1 -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [] {r1:int; box forall[]. {r1:int; *} e :: *} 0. [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")

let test_call_st_ty_exc _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_st_exc))

let call_st_exc2 =
   F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h;
                call l1 {box forall[]. {r1:int; z} e :: *, 0}],
         l1 -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e, r1: int; z} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [] {r1:int; box forall[]. {r1:int; *} e :: *} 0. [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_st_ty_exc2 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_st_exc2))

let call_st_exc3 =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h;
                call l1 {*, 0}],
         l1 -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [] {r1:int; box forall[]. {r1:int; *} e :: *} 0. [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")

let test_call_st_ty_exc3 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC call_st_exc3))


let test_call_to_call _ =
  assert_eint
    (snd (F.stepn 50 (empty, F.EBoundary (dummy_loc, F.TInt, None, call_to_call))))
    2


let test_call_to_call_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (F.EBoundary (dummy_loc, F.TInt, None, call_to_call))))
    (FTAL.FT F.TInt, TAL.SConcrete [])



let test_factorial_f_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC factorial_f))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])

let test_factorial_t _ =
  assert_eint
    (snd (F.stepn 30 (empty, F.EApp (dummy_loc, factorial_t, [F.EInt (dummy_loc, 3)]))))
    6

let test_factorial_t_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC factorial_t))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])


let test_higher_order _ =
  assert_eint
    (snd (F.stepn 60 (empty, higher_order)))
    2



let test_higher_order_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC higher_order))
    (FTAL.FT F.TInt, TAL.SConcrete [])


let f_closures =
  F.(ELam (dummy_loc, [("x", TInt)],
                   EApp (dummy_loc, EBoundary (dummy_loc, TArrow ( [TInt], TInt), None,
                                    (dummy_loc, [TAL.Iprotect (dummy_loc, [], "z2");
                                      TAL.Iimport (dummy_loc, "rf", "_z", TAL.SAbstract ([], "z2"), TArrow ([TInt], TInt), ELam (dummy_loc, [("y", TInt)], EBinop (dummy_loc, EVar (dummy_loc, "x"), BMinus, EVar (dummy_loc, "y"))));
                                      TAL.Ihalt (dummy_loc, FTAL.tytrans (TArrow ([TInt], TInt)), TAL.SAbstract ([], "z2"), "rf")], [])),
                         [EInt (dummy_loc, 1)])))

let test_closures _ =
  assert_eint
    (snd (F.stepn 50 (empty, F.EApp (dummy_loc, f_closures, [F.EInt (dummy_loc, 3)]))))
    2

let test_closures_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (F.EApp (dummy_loc, f_closures, [F.EInt (dummy_loc, 3)]))))
    (FTAL.FT F.TInt, TAL.SConcrete [])

let test_blocks1 _ =
  assert_eint
    (snd (F.stepn 20 (empty, F.EApp (dummy_loc, blocks_1, [F.EInt (dummy_loc, 3)]))))
    5

let test_blocks1_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (F.EApp (dummy_loc, blocks_1, [F.EInt (dummy_loc, 3)]))))
    (FTAL.FT F.TInt, TAL.SConcrete [])


let test_blocks2 _ =
  assert_eint
    (snd (F.stepn 30 (empty, F.EApp (dummy_loc, blocks_2, [F.EInt (dummy_loc, 3)]))))
    5

let test_blocks2_ty _ =
  assert_equal
    (FTAL.tc
       (FTAL.default_context TAL.QOut)
       (FTAL.FC (F.EApp (dummy_loc, blocks_2, [F.EInt (dummy_loc, 3)]))))
    (FTAL.FT F.TInt, TAL.SConcrete [])

let test_ft_factorial_t_ty _ =
  let (l, h) = factorial_t' in
  let ((h',_,_),e) = FTAL.ft (F.TArrow ([F.TInt], F.TInt)) l (h,[],[]) in
  let context = FTAL.default_context TAL.QOut in
  let ht = List.map (fun (l,(m, p)) -> (l, (m, FTAL.tc_h_shallow context dummy_loc TAL.Box p))) h' in
  assert_equal
    (FTAL.tc
       (FTAL.set_heap context ht)
       (FTAL.FC e))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])

let test_examples _ =
  let assert_roundtrip_f fexpr =
    let reparsed = Parse.parse_string Parser.f_expression_eof (Ftal.F.show_exp fexpr) in
    let rereparsed = Parse.parse_string Parser.f_expression_eof (Ftal.F.show_exp reparsed) in
    assert_equal reparsed rereparsed in
  let assert_roundtrip_c comp =
    let show_comp comp =
      let doc = Ftal.TALP.p_component comp in
      let buf = Buffer.create 123 in
      PPrintEngine.ToBuffer.pretty 0.8 80 buf doc;
      Buffer.contents buf in
    let reparsed = Parse.parse_string Parser.component_eof (show_comp comp) in
    let rereparsed = Parse.parse_string Parser.component_eof (show_comp reparsed) in
    assert_equal reparsed rereparsed in
  assert_roundtrip_f Examples.factorial_f;
  assert_roundtrip_f Examples.factorial_t;
  assert_roundtrip_f Examples.blocks_1;
  assert_roundtrip_f Examples.blocks_2;
  assert_roundtrip_c Examples.call_to_call;
  assert_roundtrip_f Examples.higher_order;
  ()

let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "F: 1 + 1 : int" >:: test1_ty;
              "F: 1 + 1 = 2 (2)" >:: test2;
              "F: (lam x. x + x) 1 = 2" >:: test_f_app;
              "parse (5)" >:: test_parse5;
              "F: fact 3 = 6" >:: test_factorial_f;
              "F: fact : int -> int" >:: test_factorial_f_ty;
              "TAL: mv r1,1;halt r1 : int" >:: test_mv_ty;
              "TAL: mv r1,1; + r1,r1,1;halt r1 : int" >:: test_aop_ty;
              "TAL: aop exc : int" >:: test_aop_ty_exc;
              "TAL: aop exc : int" >:: test_aop_ty_exc2;
              "TAL: aop exc : int" >:: test_aop_ty_exc3;
              "TAL: import r1,1; halt r1 : int" >:: test_import_ty;
              "TAL: import exc" >:: test_import_ty_exc;
              "TAL: import exc" >:: test_import_ty_exc2;
              "TAL: import exc" >:: test_import_ty_exc3;
              "TAL: mv r1, 1; salloc 2; halt r1 : int" >:: test_salloc_ty;
              "TAL: import w/ stack mod : int" >:: test_import_stk_ty;
              "TAL: sst" >:: test_sst_ty;
              "TAL: sld" >:: test_sld_ty;
              "TAL: ld" >:: test_ld_ty;
              "TAL: ld" >:: test_ld2_ty;
              "TAL: st" >:: test_st_ty;
              "TAL: ralloc" >:: test_ralloc_ty;
              "TAL: balloc" >:: test_balloc_ty;
              "TAL: balloc exc" >:: test_balloc_ty_exc;
              "TAL: unpack" >:: test_unpack_ty;
              "TAL: unpack exc" >:: test_unpack_ty_exc;
              "TAL: unfold" >:: test_unfold_ty;
              "TAL: unfold exc" >:: test_unfold_ty_exc;
              "TAL: simple call = 10" >:: test_call_tl;
              "TAL: simple call : int" >:: test_call_tl_ty;
              "TAL: simple call exc" >:: test_call_tl_ty_exc;
              "TAL: simple call exc 2" >:: test_call_tl_ty_exc2;
              "TAL: simple call exc 3" >:: test_call_tl_ty_exc3;
              "TAL: simple call exc 4" >:: test_call_tl_ty_exc4;
              "TAL: nested call = 0" >:: test_call_st;
              "TAL: nested call : int" >:: test_call_st_ty;
              "TAL: nested call exc" >:: test_call_st_ty_exc;
              "TAL: nested call exc2" >:: test_call_st_ty_exc2;
              "TAL: nested call exc3" >:: test_call_st_ty_exc3;
              "TAL: call to call = 2" >:: test_call_to_call;
              "TAL: call to call : int" >:: test_call_to_call_ty;
              "TAL: fact 3 = 6" >:: test_factorial_t;
              "TAL: int -> int" >:: test_factorial_t_ty;
              "TAL: higher order = 2" >:: test_higher_order;
              "TAL: higher order : int" >:: test_higher_order_ty;
              "FTAL: (lam x. FT(TF(lam y. x - y)) 1) 3 = 2" >:: test_closures;
              "FTAL: (lam x. FT(TF(lam y. x - y)) 1) 3 : int" >:: test_closures_ty;
              "TAL(1block): (lam x. x + 2)3 = 5" >:: test_blocks1;
              "TAL(1block): (lam x. x + 2)3 : int" >:: test_blocks1_ty;
              "TAL(2blocks): (lam x. x + 2)3 = 5" >:: test_blocks2;
              "TAL(2blocks): (lam x. x + 2)3 : int" >:: test_blocks2_ty;
              "FT: factorial : int -> int" >:: test_ft_factorial_t_ty;
              "Example roundtrips" >:: test_examples;
            ]


let () =
  run_test_tt_main suite
