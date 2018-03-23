
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | VAR of (
# 30 "parser.mly"
       (string)
# 11 "parser.ml"
  )
    | OPEN_VAR
    | OPEN_VALIDITY
    | OPEN_SUM
    | OPEN_PRODUCT
    | OPEN_NUM
    | OPEN_NOT
    | OPEN_LESS_EQ
    | OPEN_LESS
    | OPEN_DISJUNCTION
    | OPEN_CONJUNCTION
    | OPEN_ATOM
    | NUM of (
# 29 "parser.mly"
       (int)
# 27 "parser.ml"
  )
    | EOF
    | CLOSE_VAR
    | CLOSE_VALIDITY
    | CLOSE_SUM
    | CLOSE_PRODUCT
    | CLOSE_NUM
    | CLOSE_NOT
    | CLOSE_LESS_EQ
    | CLOSE_LESS
    | CLOSE_DISJUNCTION
    | CLOSE_CONJUNCTION
    | CLOSE_ATOM
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState42
  | MenhirState31
  | MenhirState29
  | MenhirState23
  | MenhirState12
  | MenhirState11
  | MenhirState6
  | MenhirState4
  | MenhirState3
  | MenhirState2
  | MenhirState1

# 1 "parser.mly"
  
    
open Types


# 75 "parser.ml"

let rec _menhir_goto_literal : _menhir_env -> 'ttv_tail -> _menhir_state -> (Types.element) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState1 | MenhirState3 | MenhirState42 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (l : (Types.element))) = _menhir_stack in
        let _v : (Types.element) = 
# 49 "parser.mly"
                    ( l )
# 88 "parser.ml"
         in
        _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_NOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (l : (Types.element))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.element) = 
# 57 "parser.mly"
                                        ( Not l )
# 106 "parser.ml"
             in
            _menhir_goto_literal _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_elem : _menhir_env -> 'ttv_tail -> _menhir_state -> (Types.element) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState3 | MenhirState42 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_ATOM ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OPEN_CONJUNCTION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OPEN_DISJUNCTION ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OPEN_NOT ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | CLOSE_CONJUNCTION | CLOSE_DISJUNCTION ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_NOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Types.element))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.element) = 
# 48 "parser.mly"
                                     ( Not e )
# 156 "parser.ml"
             in
            _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_VALIDITY ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, (e : (Types.element))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.formula) = 
# 42 "parser.mly"
                                                ( Formula e )
# 179 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (f : (Types.formula)) = _v in
            let _v : (
# 33 "parser.mly"
       (Types.formula option)
# 187 "parser.ml"
            ) = 
# 37 "parser.mly"
                   ( Some f )
# 191 "parser.ml"
             in
            _menhir_goto_prog _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_num_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Types.num_type list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_PRODUCT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (nl : (Types.num_type list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.num_type) = 
# 93 "parser.mly"
                                                   ( Prod (nl) )
# 222 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (p : (Types.num_type)) = _v in
            let _v : (Types.num_type) = 
# 76 "parser.mly"
                    ( p )
# 230 "parser.ml"
             in
            _menhir_goto_num _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (n : (Types.num_type))), _, (nl : (Types.num_type list))) = _menhir_stack in
        let _v : (Types.num_type list) = 
# 85 "parser.mly"
                                ( n :: nl )
# 246 "parser.ml"
         in
        _menhir_goto_num_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_SUM ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (nl : (Types.num_type list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.num_type) = 
# 89 "parser.mly"
                                           ( Sum (nl) )
# 264 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (s : (Types.num_type)) = _v in
            let _v : (Types.num_type) = 
# 75 "parser.mly"
                ( s )
# 272 "parser.ml"
             in
            _menhir_goto_num _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_constr : _menhir_env -> 'ttv_tail -> (Types.constraint_n) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CLOSE_ATOM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), (c : (Types.constraint_n))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Types.element) = 
# 58 "parser.mly"
                                        ( Atom  c )
# 306 "parser.ml"
         in
        _menhir_goto_literal _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_elem_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Types.element list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_CONJUNCTION ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (el : (Types.element list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.element) = 
# 46 "parser.mly"
                                                           ( Conjunction el )
# 335 "parser.ml"
             in
            _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Types.element))), _, (el : (Types.element list))) = _menhir_stack in
        let _v : (Types.element list) = 
# 52 "parser.mly"
                                 ( e :: el )
# 351 "parser.ml"
         in
        _menhir_goto_elem_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_DISJUNCTION ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (el : (Types.element list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.element) = 
# 47 "parser.mly"
                                                           ( Disjunction el )
# 369 "parser.ml"
             in
            _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Types.num_type list) = 
# 86 "parser.mly"
                    ( [] )
# 386 "parser.ml"
     in
    _menhir_goto_num_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_num : _menhir_env -> 'ttv_tail -> _menhir_state -> (Types.num_type) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState11 | MenhirState23 | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_NUM ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | OPEN_PRODUCT ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | OPEN_SUM ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | OPEN_VAR ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | CLOSE_PRODUCT | CLOSE_SUM ->
            _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_NUM ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState29
        | OPEN_PRODUCT ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState29
        | OPEN_SUM ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState29
        | OPEN_VAR ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState29
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (n1 : (Types.num_type))), _, (n2 : (Types.num_type))) = _menhir_stack in
        let _v : (Types.less_equal) = 
# 71 "parser.mly"
                            ( LessEq (n1, n2) )
# 437 "parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_LESS_EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, (np : (Types.less_equal))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.constraint_n) = 
# 63 "parser.mly"
                                                       ( Constraint (0, np) )
# 454 "parser.ml"
             in
            _menhir_goto_constr _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NUM _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (n : (
# 29 "parser.mly"
       (int)
# 475 "parser.ml"
            )) = _v in
            let _v : (Types.num_type) = 
# 82 "parser.mly"
                ( Num (n - 1) )
# 480 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (n2 : (Types.num_type)) = _v in
            let (_menhir_stack, _menhir_s, (n1 : (Types.num_type))) = _menhir_stack in
            let _v : (Types.less_equal) = 
# 67 "parser.mly"
                              ( LessEq (n1, n2) )
# 489 "parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | CLOSE_LESS ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _, (np : (Types.less_equal))) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : (Types.constraint_n) = 
# 62 "parser.mly"
                                              ( Constraint (0, np) )
# 506 "parser.ml"
                 in
                _menhir_goto_constr _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Types.element list) = 
# 53 "parser.mly"
                    ( [] )
# 529 "parser.ml"
     in
    _menhir_goto_elem_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VAR _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (v : (
# 30 "parser.mly"
       (string)
# 546 "parser.ml"
        )) = _v in
        let _v : (string) = 
# 109 "parser.mly"
                ( v )
# 551 "parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_VAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), (v : (string))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.num_type) = 
# 101 "parser.mly"
                                        ( Var v )
# 568 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (v : (Types.num_type)) = _v in
            let _v : (Types.num_type) = 
# 78 "parser.mly"
                ( v )
# 576 "parser.ml"
             in
            _menhir_goto_num _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_NUM ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | OPEN_PRODUCT ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | OPEN_SUM ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | OPEN_VAR ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | CLOSE_SUM ->
        _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_NUM ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | OPEN_PRODUCT ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | OPEN_SUM ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | OPEN_VAR ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | CLOSE_PRODUCT ->
        _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | NUM _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (n : (
# 29 "parser.mly"
       (int)
# 647 "parser.ml"
        )) = _v in
        let _v : (int) = 
# 105 "parser.mly"
                ( n )
# 652 "parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CLOSE_NUM ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), (c : (int))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Types.num_type) = 
# 97 "parser.mly"
                                        ( Num c )
# 669 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (n : (Types.num_type)) = _v in
            let _v : (Types.num_type) = 
# 77 "parser.mly"
                    ( n )
# 677 "parser.ml"
             in
            _menhir_goto_num _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_ATOM ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | OPEN_CONJUNCTION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | OPEN_DISJUNCTION ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | OPEN_NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState2
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_ATOM ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | OPEN_CONJUNCTION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | OPEN_DISJUNCTION ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | OPEN_NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | CLOSE_DISJUNCTION ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState3
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_ATOM ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | OPEN_CONJUNCTION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | OPEN_DISJUNCTION ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | OPEN_NOT ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | CLOSE_CONJUNCTION ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState4
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OPEN_LESS ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_NUM ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | OPEN_PRODUCT ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | OPEN_SUM ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | OPEN_VAR ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState31
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31)
    | OPEN_LESS_EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_NUM ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | OPEN_PRODUCT ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | OPEN_SUM ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | OPEN_VAR ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_prog : _menhir_env -> 'ttv_tail -> (
# 33 "parser.mly"
       (Types.formula option)
# 849 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 33 "parser.mly"
       (Types.formula option)
# 857 "parser.ml"
    )) = _v in
    Obj.magic _1

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 33 "parser.mly"
       (Types.formula option)
# 876 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = () in
        let _v : (
# 33 "parser.mly"
       (Types.formula option)
# 897 "parser.ml"
        ) = 
# 38 "parser.mly"
            ( None )
# 901 "parser.ml"
         in
        _menhir_goto_prog _menhir_env _menhir_stack _v
    | OPEN_VALIDITY ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OPEN_ATOM ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState1
        | OPEN_CONJUNCTION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState1
        | OPEN_DISJUNCTION ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1
        | OPEN_NOT ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR)

# 112 "parser.mly"
  
# 929 "parser.ml"

# 219 "/home/bojan/.opam/system/lib/menhir/standard.mly"
  


# 935 "parser.ml"
