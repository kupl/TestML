
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | WITH
    | UNDERBAR
    | UID of (
# 19 "parser.mly"
       (string)
# 13 "parser.ml"
  )
    | TYPE
    | TUnit
    | TString
    | TRUE
    | TList
    | TInt
    | THEN
    | TBool
    | STRINGCONCAT
    | STRING of (
# 21 "parser.mly"
       (string)
# 27 "parser.ml"
  )
    | STRCON
    | STAR
    | SHOLE
    | SEMI
    | RPAREN
    | REC
    | RBRACKET
    | RBRACE
    | RAISE
    | PLUS
    | PIPE
    | OR
    | OF
    | NOTEQ
    | NOT
    | MOD
    | MINUS
    | MATCH
    | LPAREN
    | LISTTL
    | LISTSORT
    | LISTREVMAP
    | LISTREVAPD
    | LISTREV
    | LISTNTH
    | LISTMEMQ
    | LISTMEM
    | LISTMAPI
    | LISTMAP
    | LISTLENGTH
    | LISTHD
    | LISTFORALL
    | LISTFOLDR
    | LISTFOLDL
    | LISTFIND
    | LISTFILTER
    | LISTEXISTS
    | LISTASSOC
    | LISTAPPEND
    | LID of (
# 18 "parser.mly"
       (string)
# 71 "parser.ml"
  )
    | LET
    | LESSEQ
    | LESS
    | LBRACKET
    | LBRACE
    | LARGEREQ
    | LARGER
    | INT of (
# 20 "parser.mly"
       (int)
# 83 "parser.ml"
  )
    | IN
    | IF
    | IDENT
    | HOLE
    | FUNCTION
    | FUN
    | FATARR
    | FALSE
    | EXCEPTION
    | EQ
    | EOF
    | END
    | ELSE
    | DOUBLECOLON
    | DIVIDE
    | DEFAND
    | COMMA
    | COLON
    | BEGIN
    | AT
    | ARR
    | AND
    | AHOLE
  
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
  | MenhirState372
  | MenhirState370
  | MenhirState368
  | MenhirState366
  | MenhirState364
  | MenhirState362
  | MenhirState360
  | MenhirState358
  | MenhirState356
  | MenhirState354
  | MenhirState353
  | MenhirState352
  | MenhirState349
  | MenhirState348
  | MenhirState347
  | MenhirState342
  | MenhirState340
  | MenhirState331
  | MenhirState329
  | MenhirState324
  | MenhirState314
  | MenhirState313
  | MenhirState312
  | MenhirState310
  | MenhirState307
  | MenhirState302
  | MenhirState300
  | MenhirState295
  | MenhirState294
  | MenhirState292
  | MenhirState290
  | MenhirState288
  | MenhirState287
  | MenhirState286
  | MenhirState280
  | MenhirState276
  | MenhirState274
  | MenhirState272
  | MenhirState270
  | MenhirState262
  | MenhirState261
  | MenhirState260
  | MenhirState254
  | MenhirState251
  | MenhirState249
  | MenhirState247
  | MenhirState245
  | MenhirState243
  | MenhirState241
  | MenhirState239
  | MenhirState236
  | MenhirState235
  | MenhirState233
  | MenhirState231
  | MenhirState230
  | MenhirState228
  | MenhirState227
  | MenhirState226
  | MenhirState224
  | MenhirState222
  | MenhirState220
  | MenhirState218
  | MenhirState216
  | MenhirState214
  | MenhirState212
  | MenhirState209
  | MenhirState208
  | MenhirState206
  | MenhirState204
  | MenhirState202
  | MenhirState200
  | MenhirState196
  | MenhirState191
  | MenhirState187
  | MenhirState184
  | MenhirState183
  | MenhirState181
  | MenhirState179
  | MenhirState177
  | MenhirState175
  | MenhirState173
  | MenhirState171
  | MenhirState169
  | MenhirState167
  | MenhirState165
  | MenhirState163
  | MenhirState161
  | MenhirState159
  | MenhirState156
  | MenhirState155
  | MenhirState153
  | MenhirState151
  | MenhirState148
  | MenhirState147
  | MenhirState146
  | MenhirState143
  | MenhirState141
  | MenhirState140
  | MenhirState138
  | MenhirState131
  | MenhirState130
  | MenhirState129
  | MenhirState124
  | MenhirState122
  | MenhirState119
  | MenhirState117
  | MenhirState115
  | MenhirState110
  | MenhirState107
  | MenhirState100
  | MenhirState98
  | MenhirState97
  | MenhirState96
  | MenhirState93
  | MenhirState88
  | MenhirState83
  | MenhirState74
  | MenhirState72
  | MenhirState69
  | MenhirState64
  | MenhirState59
  | MenhirState57
  | MenhirState55
  | MenhirState54
  | MenhirState53
  | MenhirState48
  | MenhirState47
  | MenhirState46
  | MenhirState43
  | MenhirState42
  | MenhirState40
  | MenhirState39
  | MenhirState38
  | MenhirState34
  | MenhirState33
  | MenhirState31
  | MenhirState9
  | MenhirState7
  | MenhirState1
  | MenhirState0

# 1 "parser.mly"
  
open Lang

exception Internal_error of string

let rec appify (e:lexp) (es:lexp list) : lexp =
  match es with
  | [] -> e
  | e'::es -> appify (gen_label(),EApp (e, e')) es

let rec binding_args : arg list -> lexp -> lexp
= fun args e ->
  match args with
  | [] -> e
  | hd::tl -> (gen_label(),EFun (hd, binding_args tl e))

# 282 "parser.ml"

let rec _menhir_goto_value_semi_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.value list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState314 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (v : (Lang.value))), _, (vs : (Lang.value list))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.value list) = 
# 658 "parser.mly"
    ( v::vs )
# 296 "parser.ml"
         in
        _menhir_goto_value_semi_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState312 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (v : (Lang.value))), _, (vs : (Lang.value list))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.value) = 
# 642 "parser.mly"
    ( VList (v::vs) )
# 314 "parser.ml"
             in
            _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce205 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.value list) = 
# 654 "parser.mly"
    ( [] )
# 331 "parser.ml"
     in
    _menhir_goto_value_semi_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run313 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | INT _v ->
        _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
    | LBRACKET ->
        _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | LPAREN ->
        _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | MINUS ->
        _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | STRING _v ->
        _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
    | TRUE ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | UID _v ->
        _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.value list) = 
# 656 "parser.mly"
    ( [] )
# 364 "parser.ml"
         in
        _menhir_goto_value_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313

and _menhir_goto_value_comma_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.value list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState307 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (vs : (Lang.value list)) = _v in
        let (_menhir_stack, _menhir_s, (v : (Lang.value))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.value) = 
# 624 "parser.mly"
    ( VTuple (v::vs) )
# 384 "parser.ml"
         in
        _menhir_goto_value _menhir_env _menhir_stack _menhir_s _v
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (cl : (Lang.value list)) = _v in
        let (_menhir_stack, _menhir_s, (c : (Lang.value))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.value list) = 
# 664 "parser.mly"
    ( c::cl )
# 396 "parser.ml"
         in
        _menhir_goto_value_comma_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_value : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.value) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState312
        | RBRACKET ->
            _menhir_reduce205 _menhir_env (Obj.magic _menhir_stack) MenhirState312
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState312)
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState314
        | RBRACKET ->
            _menhir_reduce205 _menhir_env (Obj.magic _menhir_stack) MenhirState314
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState314)
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (v : (Lang.value))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.value) = 
# 650 "parser.mly"
    ( v )
# 447 "parser.ml"
             in
            _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (i : (Lang.input))), _, (o : (Lang.value))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : (Lang.input * Lang.value) = 
# 614 "parser.mly"
    ( (i,o) )
# 471 "parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState329 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState329 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState329 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState329 _v
            | RBRACE ->
                _menhir_reduce46 _menhir_env (Obj.magic _menhir_stack) MenhirState329
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState329)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pat_semi_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (p : (Lang.pat))), _, (ps : (Lang.pat list))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.pat list) = 
# 600 "parser.mly"
    ( p::ps )
# 587 "parser.ml"
         in
        _menhir_goto_pat_semi_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (p : (Lang.pat))), _, (ps : (Lang.pat list))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.pat) = 
# 590 "parser.mly"
    ( PList (p::ps) )
# 605 "parser.ml"
             in
            _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_value_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.value) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState294 | MenhirState300 | MenhirState313 | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState307
            | INT _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
            | LBRACKET ->
                _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState307
            | LPAREN ->
                _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState307
            | MINUS ->
                _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState307
            | STRING _v ->
                _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
            | TRUE ->
                _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState307
            | UID _v ->
                _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState307)
        | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (c : (Lang.value))) = _menhir_stack in
            let _v : (Lang.value) = 
# 626 "parser.mly"
    ( c )
# 657 "parser.ml"
             in
            _menhir_goto_value _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState310 | MenhirState307 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState310
            | INT _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _v
            | LBRACKET ->
                _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState310
            | LPAREN ->
                _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState310
            | MINUS ->
                _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState310
            | STRING _v ->
                _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _v
            | TRUE ->
                _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState310
            | UID _v ->
                _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState310 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState310)
        | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (c : (Lang.value))) = _menhir_stack in
            let _v : (Lang.value list) = 
# 662 "parser.mly"
    ( [c] )
# 702 "parser.ml"
             in
            _menhir_goto_value_comma_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState295 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 717 "parser.ml"
        ))), _, (v : (Lang.value))) = _menhir_stack in
        let _v : (Lang.value) = 
# 646 "parser.mly"
    ( VCtor (c, [v]) )
# 722 "parser.ml"
         in
        _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce138 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * (Lang.binding) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s), _, (d : (Lang.binding))) = _menhir_stack in
    let _1 = () in
    let _v : (Lang.decl) = 
# 206 "parser.mly"
    ( DLet d )
# 735 "parser.ml"
     in
    _menhir_goto_letbind_block _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce139 : _menhir_env -> (('ttv_tail * _menhir_state) * _menhir_state) * _menhir_state * (Lang.binding) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s), _), _, (d : (Lang.binding))) = _menhir_stack in
    let _2 = () in
    let _1 = () in
    let _v : (Lang.decl) = 
# 206 "parser.mly"
    ( DLet d )
# 747 "parser.ml"
     in
    _menhir_goto_letbind_block _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_letbind_block : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (l : (Lang.decl)) = _v in
    let _v : (Lang.decl) = 
# 156 "parser.mly"
    ( l )
# 759 "parser.ml"
     in
    _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce167 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.pat list) = 
# 596 "parser.mly"
    ( [] )
# 768 "parser.ml"
     in
    _menhir_goto_pat_semi_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run130 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.pat list) = 
# 598 "parser.mly"
    ( [] )
# 805 "parser.ml"
         in
        _menhir_goto_pat_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130

and _menhir_run295 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 19 "parser.mly"
       (string)
# 816 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState295
    | INT _v ->
        _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState295 _v
    | LBRACKET ->
        _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState295
    | LPAREN ->
        _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState295
    | MINUS ->
        _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState295
    | STRING _v ->
        _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState295 _v
    | TRUE ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState295
    | UID _v ->
        _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState295 _v
    | COMMA | RBRACKET | RPAREN | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 844 "parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.value) = 
# 644 "parser.mly"
    ( VCtor (c, []) )
# 849 "parser.ml"
         in
        _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState295

and _menhir_run296 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.value) = 
# 634 "parser.mly"
    ( VBool true )
# 865 "parser.ml"
     in
    _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run297 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "parser.mly"
       (string)
# 872 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 21 "parser.mly"
       (string)
# 880 "parser.ml"
    )) = _v in
    let _v : (Lang.value) = 
# 638 "parser.mly"
    ( VString c )
# 885 "parser.ml"
     in
    _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run298 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (
# 20 "parser.mly"
       (int)
# 902 "parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.value) = 
# 648 "parser.mly"
    ( VInt (-c))
# 909 "parser.ml"
         in
        _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run300 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState300
    | INT _v ->
        _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState300 _v
    | LBRACKET ->
        _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState300
    | LPAREN ->
        _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState300
    | MINUS ->
        _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState300
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState300 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.value) = 
# 630 "parser.mly"
    ( VUnit )
# 946 "parser.ml"
         in
        _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
    | STRING _v ->
        _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState300 _v
    | TRUE ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState300
    | UID _v ->
        _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState300 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState300

and _menhir_run302 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState302
    | INT _v ->
        _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _v
    | LBRACKET ->
        _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState302
    | LPAREN ->
        _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState302
    | MINUS ->
        _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState302
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState302 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.value) = 
# 640 "parser.mly"
    ( VList [] )
# 987 "parser.ml"
         in
        _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v
    | STRING _v ->
        _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _v
    | TRUE ->
        _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState302
    | UID _v ->
        _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState302 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState302

and _menhir_run304 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "parser.mly"
       (int)
# 1004 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 20 "parser.mly"
       (int)
# 1012 "parser.ml"
    )) = _v in
    let _v : (Lang.value) = 
# 632 "parser.mly"
    ( VInt c )
# 1017 "parser.ml"
     in
    _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run305 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.value) = 
# 636 "parser.mly"
    ( VBool false )
# 1029 "parser.ml"
     in
    _menhir_goto_value_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_exp_semi_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState262 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))), _, (es : (Lang.lexp list))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp list) = 
# 516 "parser.mly"
    ( e::es )
# 1045 "parser.ml"
         in
        _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))), _, (es : (Lang.lexp list))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.lexp) = 
# 454 "parser.mly"
    ( (gen_label(), EList (e::es)) )
# 1063 "parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_letbind : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.binding) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run227 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState226)
    | MenhirState286 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run227 _menhir_env (Obj.magic _menhir_stack) MenhirState290
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce138 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState290)
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run227 _menhir_env (Obj.magic _menhir_stack) MenhirState364
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce138 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState364)
    | _ ->
        _menhir_fail ()

and _menhir_reduce136 : _menhir_env -> (('ttv_tail * _menhir_state) * _menhir_state * (Lang.binding)) * _menhir_state * (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s), _, (d : (Lang.binding))), _, (ds : (Lang.binding list))) = _menhir_stack in
    let _1 = () in
    let _v : (Lang.decl) = 
# 202 "parser.mly"
    ( DBlock (false, d::ds) )
# 1126 "parser.ml"
     in
    _menhir_goto_letbind_block _menhir_env _menhir_stack _menhir_s _v

and _menhir_run239 : _menhir_env -> (('ttv_tail * _menhir_state) * _menhir_state * (Lang.binding)) * _menhir_state * (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239

and _menhir_goto_letrec_bind : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.binding) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState53
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState53)
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState288
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState288)
    | MenhirState353 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState354)
    | _ ->
        _menhir_fail ()

and _menhir_reduce137 : _menhir_env -> ((('ttv_tail * _menhir_state) * _menhir_state) * _menhir_state * (Lang.binding)) * _menhir_state * (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((((_menhir_stack, _menhir_s), _), _, (d : (Lang.binding))), _, (ds : (Lang.binding list))) = _menhir_stack in
    let _2 = () in
    let _1 = () in
    let _v : (Lang.decl) = 
# 204 "parser.mly"
    ( DBlock (true, d::ds) )
# 1274 "parser.ml"
     in
    _menhir_goto_letbind_block _menhir_env _menhir_stack _menhir_s _v

and _menhir_run212 : _menhir_env -> ((('ttv_tail * _menhir_state) * _menhir_state) * _menhir_state * (Lang.binding)) * _menhir_state * (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState212
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState212

and _menhir_run196 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.branch list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState196 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState196 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState196 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState196

and _menhir_goto_pat_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ps : (Lang.pat list)) = _v in
        let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.pat list) = 
# 545 "parser.mly"
    ( p::ps )
# 1412 "parser.ml"
         in
        _menhir_goto_pat_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ps : (Lang.pat list)) = _v in
        let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.pat) = 
# 537 "parser.mly"
    ( Pats (p :: ps) )
# 1424 "parser.ml"
         in
        _menhir_goto_pat _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_pat : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState129
        | RBRACKET ->
            _menhir_reduce167 _menhir_env (Obj.magic _menhir_stack) MenhirState129
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129)
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | RBRACKET ->
            _menhir_reduce167 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (p : (Lang.pat))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.pat) = 
# 592 "parser.mly"
    ( p )
# 1475 "parser.ml"
             in
            _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState254 | MenhirState196 | MenhirState98 | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_datatype_and_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState349 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ds : (Lang.decl list)) = _v in
        let ((_menhir_stack, _menhir_s), _, (d : (Lang.decl))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.decl list) = 
# 178 "parser.mly"
    ( d::ds )
# 1601 "parser.ml"
         in
        _menhir_goto_datatype_and_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState347 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ds : (Lang.decl list)) = _v in
        let (_menhir_stack, _menhir_s, (d : (Lang.decl))) = _menhir_stack in
        let _v : (Lang.decl) = 
# 166 "parser.mly"
    ( TBlock (d::ds) )
# 1612 "parser.ml"
         in
        _menhir_goto_datatype_block _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_datatype_block : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (d : (Lang.decl)) = _v in
    let _v : (Lang.decl) = 
# 154 "parser.mly"
    ( d )
# 1626 "parser.ml"
     in
    _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v

and _menhir_run348 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run271 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState348

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t1 : (Lang.typ))), _, (t2 : (Lang.typ))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.typ) = 
# 278 "parser.mly"
    ( TArr (t1, t2) )
# 1655 "parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (t : (Lang.typ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.typ) = 
# 308 "parser.mly"
    ( t )
# 1673 "parser.ml"
             in
            _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _), _, (t : (Lang.typ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Lang.arg) = 
# 326 "parser.mly"
    ( ArgUnder t )
# 1699 "parser.ml"
             in
            _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (
# 18 "parser.mly"
       (string)
# 1720 "parser.ml"
            ))), _, (t : (Lang.typ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.arg) = 
# 330 "parser.mly"
    ( ArgOne (x, t) )
# 1728 "parser.ml"
             in
            _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState208
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState249
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState249)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState274 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 2151 "parser.ml"
        ))), _, (t : (Lang.typ))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.ctor) = 
# 198 "parser.mly"
    ( (c, [t]) )
# 2157 "parser.ml"
         in
        _menhir_goto_ctor _menhir_env _menhir_stack _menhir_s _v
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (d : (
# 18 "parser.mly"
       (string)
# 2166 "parser.ml"
        ))), _, (t : (Lang.typ))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.decl) = 
# 182 "parser.mly"
    ( DEqn (d, t) )
# 2172 "parser.ml"
         in
        _menhir_goto_datatype_bind _menhir_env _menhir_stack _menhir_s _v
    | MenhirState360 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState362 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState362 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState362 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState362
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState362 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState362)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState370 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState372 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState372 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState372 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState372
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState372 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState372)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.input) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState329 | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FATARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run305 _menhir_env (Obj.magic _menhir_stack) MenhirState294
            | INT _v ->
                _menhir_run304 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
            | LBRACKET ->
                _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState294
            | LPAREN ->
                _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState294
            | MINUS ->
                _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState294
            | STRING _v ->
                _menhir_run297 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
            | TRUE ->
                _menhir_run296 _menhir_env (Obj.magic _menhir_stack) MenhirState294
            | UID _v ->
                _menhir_run295 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState294)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState324 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.lexp))), _, (el : (Lang.input))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.input) = 
# 620 "parser.mly"
    ( e::el )
# 2430 "parser.ml"
         in
        _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce114 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.lexp list) = 
# 512 "parser.mly"
    ( [] )
# 2441 "parser.ml"
     in
    _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run261 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState261 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState261 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState261 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState261
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState261 _v
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp list) = 
# 514 "parser.mly"
    ( [] )
# 2540 "parser.ml"
         in
        _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState261

and _menhir_reduce135 : _menhir_env -> ((((('ttv_tail * _menhir_state * (Lang.let_bind)) * _menhir_state * (Lang.arg list))) * _menhir_state * (Lang.typ))) * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((((_menhir_stack, _menhir_s, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))) = _menhir_stack in
    let _5 = () in
    let _3 = () in
    let _v : (Lang.binding) = 
# 264 "parser.mly"
    ( (x, false, args, t, e) )
# 2556 "parser.ml"
     in
    _menhir_goto_letbind _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce134 : _menhir_env -> ((('ttv_tail * _menhir_state * (Lang.let_bind)) * _menhir_state * (Lang.arg list))) * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))) = _menhir_stack in
    let _3 = () in
    let _v : (Lang.binding) = 
# 262 "parser.mly"
    ( (x, false, args, fresh_tvar (), e) )
# 2567 "parser.ml"
     in
    _menhir_goto_letbind _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_let_and_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))), _, (ds : (Lang.binding list))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.binding list) = 
# 216 "parser.mly"
    ( (x, false, args, fresh_tvar(), e)::ds )
# 2584 "parser.ml"
         in
        _menhir_goto_let_and_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))), _, (ds : (Lang.binding list))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.binding list) = 
# 214 "parser.mly"
    ( (x, false, args, t, e)::ds )
# 2597 "parser.ml"
         in
        _menhir_goto_let_and_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState290 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce136 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState364 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce136 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_run227 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState227
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState227
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227

and _menhir_reduce145 : _menhir_env -> ((((('ttv_tail * _menhir_state * (Lang.let_bind)) * _menhir_state * (Lang.arg list))) * _menhir_state * (Lang.typ))) * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((((_menhir_stack, _menhir_s, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))) = _menhir_stack in
    let _5 = () in
    let _3 = () in
    let _v : (Lang.binding) = 
# 270 "parser.mly"
    ( (x, true, args, t, e) )
# 2659 "parser.ml"
     in
    _menhir_goto_letrec_bind _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce144 : _menhir_env -> ((('ttv_tail * _menhir_state * (Lang.let_bind)) * _menhir_state * (Lang.arg list))) * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))) = _menhir_stack in
    let _3 = () in
    let _v : (Lang.binding) = 
# 268 "parser.mly"
    ( (x, true, args, fresh_tvar (), e) )
# 2670 "parser.ml"
     in
    _menhir_goto_letrec_bind _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_letrec_and_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.binding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))), _, (ds : (Lang.binding list))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.binding list) = 
# 226 "parser.mly"
    ( (x, true, args, fresh_tvar(), e)::ds )
# 2687 "parser.ml"
         in
        _menhir_goto_letrec_and_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))), _, (ds : (Lang.binding list))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.binding list) = 
# 224 "parser.mly"
    ( (x, true, args,t,e)::ds )
# 2700 "parser.ml"
         in
        _menhir_goto_letrec_and_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState288 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce137 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce137 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_run54 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54

and _menhir_goto_branches : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.branch list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | PIPE ->
            _menhir_run196 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (bs : (Lang.branch list))) = _menhir_stack in
            let _1 = () in
            let _v : (Lang.lexp) = 
# 368 "parser.mly"
    ( (gen_label(), EFun(ArgOne("__fun__",fresh_tvar()),(gen_label(),EMatch((gen_label(),EVar "__fun__"),bs)))) )
# 2772 "parser.ml"
             in
            _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState254 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | PIPE ->
            _menhir_run196 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))), _, (bs : (Lang.branch list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.lexp) = 
# 364 "parser.mly"
    ( (gen_label(),EMatch (e, bs)) )
# 2796 "parser.ml"
             in
            _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pat_comma_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ps : (Lang.pat list)) = _v in
        let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.pat list) = 
# 558 "parser.mly"
    ( p::ps )
# 2820 "parser.ml"
         in
        _menhir_goto_pat_comma_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ps : (Lang.pat list)) = _v in
        let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.pat) = 
# 552 "parser.mly"
    ( PTuple (p::ps))
# 2832 "parser.ml"
         in
        _menhir_goto_pat_tuple _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_pat_tuple : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState254 | MenhirState196 | MenhirState98 | MenhirState138 | MenhirState107 | MenhirState130 | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | PIPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | INT _v ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
            | LBRACKET ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | LID _v ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
            | LPAREN ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | MINUS ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | PLUS ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | TRUE ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | UID _v ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
            | UNDERBAR ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState115
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115)
        | ARR | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
            let _v : (Lang.pat) = 
# 539 "parser.mly"
    ( p )
# 2882 "parser.ml"
             in
            _menhir_goto_pat _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState117 | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | PIPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | INT _v ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
            | LBRACKET ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | LID _v ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
            | LPAREN ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | MINUS ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | PLUS ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | TRUE ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | UID _v ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
            | UNDERBAR ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState117
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState117)
        | ARR | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
            let _v : (Lang.pat list) = 
# 543 "parser.mly"
    ( [p] )
# 2931 "parser.ml"
             in
            _menhir_goto_pat_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run119 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119

and _menhir_goto_arg_comma_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.arg list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (Lang.arg))), _, (xs : (Lang.arg list))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.arg) = 
# 332 "parser.mly"
    ( ArgTuple (x::xs) )
# 2993 "parser.ml"
             in
            _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Lang.arg))), _, (xs : (Lang.arg list))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.arg list) = 
# 340 "parser.mly"
    ( x::xs )
# 3010 "parser.ml"
         in
        _menhir_goto_arg_comma_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_decls : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState340 in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (ds : (Lang.decl list))) = _menhir_stack in
        let _2 = () in
        let _v : (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 3032 "parser.ml"
        ) = 
# 126 "parser.mly"
    ( ([],(List.rev ds)) )
# 3036 "parser.ml"
         in
        _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
    | EXCEPTION ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState340
    | LET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState340 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _v
        | LPAREN ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState352
        | REC ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState352 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState353 _v
            | LPAREN ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState353
            | UNDERBAR ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState353
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState353)
        | UNDERBAR ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState352
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState352)
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState340 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | EOF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState342 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (ds : (Lang.decl list))), _) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _v : (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 3102 "parser.ml"
                ) = 
# 128 "parser.mly"
    ( ([],(List.rev ds)) )
# 3106 "parser.ml"
                 in
                _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
            | EXCEPTION ->
                _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LET ->
                _menhir_run286 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | TYPE ->
                _menhir_run270 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState342)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | TYPE ->
        _menhir_run270 _menhir_env (Obj.magic _menhir_stack) MenhirState340
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState340

and _menhir_goto_datatype_bind : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState270 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (d : (Lang.decl))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.decl) = 
# 172 "parser.mly"
    ( d )
# 3220 "parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run348 _menhir_env (Obj.magic _menhir_stack) MenhirState347
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (d : (Lang.decl))) = _menhir_stack in
            let _v : (Lang.decl) = 
# 168 "parser.mly"
    ( d )
# 3235 "parser.ml"
             in
            _menhir_goto_datatype_block _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState347)
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run348 _menhir_env (Obj.magic _menhir_stack) MenhirState349
        | EOF | EXCEPTION | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (d : (Lang.decl))) = _menhir_stack in
            let _1 = () in
            let _v : (Lang.decl list) = 
# 176 "parser.mly"
    ( [d] )
# 3256 "parser.ml"
             in
            _menhir_goto_datatype_and_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState349)
    | _ ->
        _menhir_fail ()

and _menhir_goto_star_typ_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ts : (Lang.typ list)) = _v in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.typ list) = 
# 292 "parser.mly"
    ( t::ts )
# 3278 "parser.ml"
         in
        _menhir_goto_star_typ_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ts : (Lang.typ list)) = _v in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.typ) = 
# 286 "parser.mly"
    ( TTuple (t::ts) )
# 3290 "parser.ml"
         in
        _menhir_goto_typ_star _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_typ_star : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | LID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
        | LPAREN ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | TBool ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | TInt ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | TString ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | TUnit ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
    | DEFAND | EOF | EQ | EXCEPTION | LET | PIPE | RPAREN | SEMI | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ) = 
# 280 "parser.mly"
    ( t )
# 3332 "parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run71 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
    let _2 = () in
    let _v : (Lang.typ) = 
# 304 "parser.mly"
    ( TList t )
# 3351 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_exp_comma_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (es : (Lang.lexp list)) = _v in
        let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp list) = 
# 360 "parser.mly"
    ( e::es )
# 3367 "parser.ml"
         in
        _menhir_goto_exp_comma_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (es : (Lang.lexp list)) = _v in
        let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
        let _v : (Lang.lexp) = 
# 352 "parser.mly"
    ( (gen_label(),ETuple (e::es)) )
# 3378 "parser.ml"
         in
        _menhir_goto_exp_tuple _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_tuple : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Lang.lexp)) = _v in
    let _v : (Lang.lexp) = 
# 348 "parser.mly"
    ( e )
# 3392 "parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (xs : (Lang.arg list))), _, (e : (Lang.lexp))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 366 "parser.mly"
    ( binding_args xs e )
# 3405 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (p : (Lang.pat))), _, (e : (Lang.lexp))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.branch) = 
# 533 "parser.mly"
    ( (p, e) )
# 3416 "parser.ml"
         in
        (match _menhir_s with
        | MenhirState138 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (b : (Lang.branch)) = _v in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _1 = () in
            let _v : (Lang.branch list) = 
# 527 "parser.mly"
    ( [b] )
# 3428 "parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _menhir_s _v
        | MenhirState196 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (b : (Lang.branch)) = _v in
            let (_menhir_stack, _menhir_s, (bs : (Lang.branch list))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.branch list) = 
# 529 "parser.mly"
    ( bs@[b] )
# 3440 "parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _menhir_s _v
        | MenhirState254 | MenhirState98 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (b : (Lang.branch)) = _v in
            let _v : (Lang.branch list) = 
# 525 "parser.mly"
    ( [b] )
# 3450 "parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | EOF | EXCEPTION | IN | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.binding list) = 
# 222 "parser.mly"
    ( [(x, true, args, fresh_tvar(), e)] )
# 3470 "parser.ml"
             in
            _menhir_goto_letrec_and_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState204)
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState209
        | EOF | EXCEPTION | IN | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.binding list) = 
# 220 "parser.mly"
    ( [(x, true, args,t,e)] )
# 3493 "parser.ml"
             in
            _menhir_goto_letrec_and_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209)
    | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _), _, (d : (Lang.binding))), _, (ds : (Lang.binding list))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 380 "parser.mly"
    ( (gen_label(), EBlock (true, d::ds, e2)) )
# 3510 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState218)
        | DEFAND | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce144 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState218 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _), _, (f : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 376 "parser.mly"
    ( (gen_label(), ELet (f, true, args, fresh_tvar(), e1, e2) ))
# 3628 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState224)
        | DEFAND | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce145 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((((_menhir_stack, _menhir_s), _), _, (f : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _9 = () in
        let _7 = () in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 372 "parser.mly"
    ( (gen_label(), ELet (f, true, args, t, e1, e2)) )
# 3747 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run227 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | EOF | EXCEPTION | IN | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e : (Lang.lexp))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.binding list) = 
# 212 "parser.mly"
    ( [(x, false, args, fresh_tvar(), e)] )
# 3765 "parser.ml"
             in
            _menhir_goto_let_and_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState231)
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DEFAND ->
            _menhir_run227 _menhir_env (Obj.magic _menhir_stack) MenhirState236
        | EOF | EXCEPTION | IN | LET | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e : (Lang.lexp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _1 = () in
            let _v : (Lang.binding list) = 
# 210 "parser.mly"
    ( [(x, false, args,t,e)] )
# 3788 "parser.ml"
             in
            _menhir_goto_let_and_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState236)
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (d : (Lang.binding))), _, (ds : (Lang.binding list))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 378 "parser.mly"
    ( (gen_label(), EBlock (false, d::ds, e2)) )
# 3804 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState245
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState245)
        | DEFAND | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce134 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _, (f : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 374 "parser.mly"
    ( (gen_label(), ELet (f, false, args, fresh_tvar(), e1, e2)) )
# 3921 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState251
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251)
        | DEFAND | EOF | EXCEPTION | LET | SEMI | TYPE ->
            _menhir_reduce135 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _, (f : (Lang.let_bind))), _, (args : (Lang.arg list))), _, (t : (Lang.typ))), _, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _8 = () in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 370 "parser.mly"
    ( (gen_label(), ELet (f, false, args, t, e1, e2)) )
# 4039 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | INT _v ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState254 _v
            | LBRACKET ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | LID _v ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState254 _v
            | LPAREN ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | MINUS ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | PIPE ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | PLUS ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | TRUE ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | UID _v ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState254 _v
            | UNDERBAR ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState254
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState254)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.lexp) = 
# 460 "parser.mly"
    ( e )
# 4099 "parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
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
        | SEMI ->
            _menhir_run261 _menhir_env (Obj.magic _menhir_stack) MenhirState260
        | RBRACKET ->
            _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState260
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState260)
    | MenhirState261 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            _menhir_run261 _menhir_env (Obj.magic _menhir_stack) MenhirState262
        | RBRACKET ->
            _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState262
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState262)
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.lexp) = 
# 458 "parser.mly"
    ( e )
# 4149 "parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState329 | MenhirState324 | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState324 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState324 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState324 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState324
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState324 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState324)
        | FATARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
            let _v : (Lang.input) = 
# 618 "parser.mly"
    ( [e] )
# 4260 "parser.ml"
             in
            _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState342 | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
        let _v : (Lang.decl) = 
# 230 "parser.mly"
    ( DLet (BindUnder, false, [], fresh_tvar(), e))
# 4276 "parser.ml"
         in
        (match _menhir_s with
        | MenhirState0 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (e : (Lang.decl)) = _v in
            let _v : (Lang.decl list) = 
# 144 "parser.mly"
    ( [e] )
# 4286 "parser.ml"
             in
            _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
        | MenhirState342 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (e : (Lang.decl)) = _v in
            let ((_menhir_stack, _menhir_s, (ds : (Lang.decl list))), _) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _v : (Lang.decl list) = 
# 150 "parser.mly"
    ( e::ds )
# 4299 "parser.ml"
             in
            _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState358 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce144 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState362 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce145 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState368 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce134 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState372 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce135 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_run147 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147

and _menhir_goto_bind_comma_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.let_bind list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Lang.let_bind list)) = _v in
        let ((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.let_bind list) = 
# 250 "parser.mly"
    ( x::xs )
# 4424 "parser.ml"
         in
        _menhir_goto_bind_comma_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Lang.let_bind list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Lang.let_bind))) = _menhir_stack in
        let _v : (Lang.let_bind) = 
# 242 "parser.mly"
    ( BindTuple (x::xs) )
# 4435 "parser.ml"
         in
        _menhir_goto_bind_tuple _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_bind_tuple : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.let_bind) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (Lang.let_bind)) = _v in
    let _v : (Lang.let_bind) = 
# 238 "parser.mly"
    ( x )
# 4449 "parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.let_bind) = 
# 258 "parser.mly"
    ( x )
# 4468 "parser.ml"
             in
            _menhir_goto_bind_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
    | MenhirState287 | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228)
    | MenhirState286 | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241)
    | MenhirState353 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState356 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState356
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState356
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState356
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState356)
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState366 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState366
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState366
        | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState366
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState366)
    | _ ->
        _menhir_fail ()

and _menhir_run47 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47

and _menhir_goto_pat_op : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState254 | MenhirState196 | MenhirState98 | MenhirState138 | MenhirState107 | MenhirState130 | MenhirState110 | MenhirState115 | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | INT _v ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
            | LBRACKET ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | LID _v ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
            | LPAREN ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | MINUS ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | PLUS ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | TRUE ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | UID _v ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
            | UNDERBAR ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
        | DOUBLECOLON ->
            _menhir_run119 _menhir_env (Obj.magic _menhir_stack)
        | ARR | PIPE | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
            let _v : (Lang.pat) = 
# 550 "parser.mly"
    ( p )
# 4645 "parser.ml"
             in
            _menhir_goto_pat_tuple _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOUBLECOLON ->
            _menhir_run119 _menhir_env (Obj.magic _menhir_stack)
        | ARR | COMMA | PIPE | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (p1 : (Lang.pat))), _, (p2 : (Lang.pat))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.pat) = 
# 562 "parser.mly"
    ( PCons (p1::[p2]) )
# 4668 "parser.ml"
             in
            _menhir_goto_pat_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState124 | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FALSE ->
                _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | INT _v ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
            | LBRACKET ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | LID _v ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
            | LPAREN ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | MINUS ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | PLUS ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | TRUE ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | UID _v ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
            | UNDERBAR ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState124)
        | DOUBLECOLON ->
            _menhir_run119 _menhir_env (Obj.magic _menhir_stack)
        | ARR | PIPE | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (p : (Lang.pat))) = _menhir_stack in
            let _v : (Lang.pat list) = 
# 556 "parser.mly"
    ( [p] )
# 4719 "parser.ml"
             in
            _menhir_goto_pat_comma_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_arg : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.arg) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
            | LPAREN ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | UNDERBAR ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState88
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (x : (Lang.arg))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Lang.arg) = 
# 334 "parser.mly"
    ( x )
# 4765 "parser.ml"
             in
            _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | LPAREN ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | UNDERBAR ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Lang.arg))) = _menhir_stack in
            let _v : (Lang.arg list) = 
# 338 "parser.mly"
    ( [x] )
# 4800 "parser.ml"
             in
            _menhir_goto_arg_comma_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState366 | MenhirState356 | MenhirState241 | MenhirState228 | MenhirState214 | MenhirState55 | MenhirState191 | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | UNDERBAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | ARR | COLON | EQ ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191)
    | _ ->
        _menhir_fail ()

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState342 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (Lang.decl)) = _v in
        let ((_menhir_stack, _menhir_s, (ds : (Lang.decl list))), _) = _menhir_stack in
        let _3 = () in
        let _2 = () in
        let _v : (Lang.decl list) = 
# 148 "parser.mly"
    ( d::ds )
# 4842 "parser.ml"
         in
        _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (Lang.decl)) = _v in
        let (_menhir_stack, _menhir_s, (ds : (Lang.decl list))) = _menhir_stack in
        let _v : (Lang.decl list) = 
# 146 "parser.mly"
    ( d::ds )
# 4853 "parser.ml"
         in
        _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (Lang.decl)) = _v in
        let _v : (Lang.decl list) = 
# 142 "parser.mly"
    ( [d] )
# 4863 "parser.ml"
         in
        _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_ctors : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.ctor list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UID _v ->
            _menhir_run273 _menhir_env (Obj.magic _menhir_stack) MenhirState280 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState280)
    | DEFAND | EOF | EXCEPTION | LET | SEMI | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (d : (
# 18 "parser.mly"
       (string)
# 4892 "parser.ml"
        ))), _, (cs : (Lang.ctor list))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.decl) = 
# 184 "parser.mly"
    ( DData (d, List.rev cs) )
# 4898 "parser.ml"
         in
        _menhir_goto_datatype_bind _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_typ_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState370 | MenhirState360 | MenhirState272 | MenhirState274 | MenhirState247 | MenhirState233 | MenhirState220 | MenhirState206 | MenhirState83 | MenhirState59 | MenhirState64 | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState72
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
        | TList ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack)
        | ARR | DEFAND | EOF | EQ | EXCEPTION | LET | PIPE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 284 "parser.mly"
    ( t )
# 4948 "parser.ml"
             in
            _menhir_goto_typ_star _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState74 | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState74
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74)
        | TList ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack)
        | ARR | DEFAND | EOF | EQ | EXCEPTION | LET | PIPE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 290 "parser.mly"
    ( [t] )
# 4993 "parser.ml"
             in
            _menhir_goto_star_typ_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_struct : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState372 | MenhirState368 | MenhirState362 | MenhirState358 | MenhirState342 | MenhirState0 | MenhirState329 | MenhirState324 | MenhirState292 | MenhirState7 | MenhirState261 | MenhirState31 | MenhirState38 | MenhirState39 | MenhirState251 | MenhirState249 | MenhirState245 | MenhirState243 | MenhirState239 | MenhirState235 | MenhirState230 | MenhirState224 | MenhirState222 | MenhirState218 | MenhirState216 | MenhirState212 | MenhirState208 | MenhirState96 | MenhirState140 | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
            let _v : (Lang.lexp) = 
# 354 "parser.mly"
    ( e )
# 5022 "parser.ml"
             in
            _menhir_goto_exp_tuple _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146)
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
            let _1 = () in
            let _v : (Lang.lexp list) = 
# 358 "parser.mly"
    ( [e] )
# 5043 "parser.ml"
             in
            _menhir_goto_exp_comma_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148)
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState202)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))), _, (e3 : (Lang.lexp))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 382 "parser.mly"
    ( (gen_label(), IF (e1, e2, e3)) )
# 5264 "parser.ml"
         in
        _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run151 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151

and _menhir_run153 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState153

and _menhir_run159 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159

and _menhir_run173 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState173

and _menhir_run161 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161

and _menhir_run165 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165

and _menhir_run175 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175

and _menhir_run177 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState177

and _menhir_run179 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179

and _menhir_run181 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState181

and _menhir_run183 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState183 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AHOLE ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | BEGIN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | HOLE ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | INT _v ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
        | LBRACKET ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LID _v ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
        | LISTAPPEND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTASSOC ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTEXISTS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTFILTER ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTFIND ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTFOLDL ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTFOLDR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTFORALL ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTHD ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTLENGTH ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTMAP ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTMAPI ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTMEM ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTMEMQ ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTNTH ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTREV ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTREVAPD ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTREVMAP ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTSORT ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LISTTL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | MINUS ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | NOT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | RAISE ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | SHOLE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | STRING _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
        | STRINGCONCAT ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | TRUE ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState184
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState184)
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183

and _menhir_run167 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167

and _menhir_run163 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState163

and _menhir_run169 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState169

and _menhir_run187 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187

and _menhir_goto_exp_app_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (es : (Lang.lexp list)) = _v in
        let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
        let _v : (Lang.lexp list) = 
# 436 "parser.mly"
    ( e::es )
# 6594 "parser.ml"
         in
        _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (es : (Lang.lexp list)) = _v in
        let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
        let _v : (Lang.lexp) = 
# 428 "parser.mly"
    ( appify e es )
# 6605 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_bind_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.let_bind) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState352 | MenhirState353 | MenhirState286 | MenhirState287 | MenhirState40 | MenhirState227 | MenhirState42 | MenhirState54 | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | COLON | EQ | LID _ | LPAREN | RPAREN | UNDERBAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Lang.let_bind))) = _menhir_stack in
            let _v : (Lang.let_bind) = 
# 244 "parser.mly"
    ( x )
# 6628 "parser.ml"
             in
            _menhir_goto_bind_tuple _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46)
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | COLON | EQ | LID _ | LPAREN | RPAREN | UNDERBAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (x : (Lang.let_bind))) = _menhir_stack in
            let _1 = () in
            let _v : (Lang.let_bind list) = 
# 248 "parser.mly"
    ( [x] )
# 6649 "parser.ml"
             in
            _menhir_goto_bind_comma_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48)
    | _ ->
        _menhir_fail ()

and _menhir_reduce156 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 19 "parser.mly"
       (string)
# 6662 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 6668 "parser.ml"
    ))) = _menhir_stack in
    let _v : (Lang.pat) = 
# 586 "parser.mly"
    ( PCtor (c, []) )
# 6673 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_pat_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState254 | MenhirState196 | MenhirState98 | MenhirState138 | MenhirState107 | MenhirState130 | MenhirState110 | MenhirState115 | MenhirState117 | MenhirState122 | MenhirState124 | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (p : (Lang.pat)) = _v in
        let _v : (Lang.pat) = 
# 566 "parser.mly"
    ( p )
# 6687 "parser.ml"
         in
        _menhir_goto_pat_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ps : (Lang.pat)) = _v in
        let (_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 6697 "parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.pat) = 
# 564 "parser.mly"
    ( PCtor (c, [ps]) )
# 6702 "parser.ml"
         in
        _menhir_goto_pat_op _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_args : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.arg list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState191 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Lang.arg))), _, (xs : (Lang.arg list))) = _menhir_stack in
        let _v : (Lang.arg list) = 
# 320 "parser.mly"
    ( x :: xs)
# 6946 "parser.ml"
         in
        _menhir_goto_args _menhir_env _menhir_stack _menhir_s _v
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState233
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState243
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState243)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState356 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState360 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState360
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState360)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState358 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState358 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState358 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState358
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState358 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState358)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState370 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState370)
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | FUN ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | FUNCTION ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | IF ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LET ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | MATCH ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState368
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState368)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce1 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _1 = () in
    let _v : (Lang.arg) = 
# 324 "parser.mly"
    ( ArgUnder (fresh_tvar ()) )
# 7584 "parser.ml"
     in
    _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce3 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 18 "parser.mly"
       (string)
# 7591 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (x : (
# 18 "parser.mly"
       (string)
# 7597 "parser.ml"
    ))) = _menhir_stack in
    let _v : (Lang.arg) = 
# 328 "parser.mly"
    ( ArgOne (x, fresh_tvar ()) )
# 7602 "parser.ml"
     in
    _menhir_goto_arg _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_ctor : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.ctor) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState276 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (Lang.ctor)) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.ctor list) = 
# 190 "parser.mly"
    ( [c] )
# 7618 "parser.ml"
         in
        _menhir_goto_ctors _menhir_env _menhir_stack _menhir_s _v
    | MenhirState280 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (Lang.ctor)) = _v in
        let (_menhir_stack, _menhir_s, (cs : (Lang.ctor list))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.ctor list) = 
# 192 "parser.mly"
    ( cs@[c] )
# 7630 "parser.ml"
         in
        _menhir_goto_ctors _menhir_env _menhir_stack _menhir_s _v
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (Lang.ctor)) = _v in
        let _v : (Lang.ctor list) = 
# 188 "parser.mly"
    ( [c] )
# 7640 "parser.ml"
         in
        _menhir_goto_ctors _menhir_env _menhir_stack _menhir_s _v
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (Lang.ctor)) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.decl) = 
# 162 "parser.mly"
    ( DExcept c )
# 7652 "parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (Lang.decl)) = _v in
        let _v : (Lang.decl) = 
# 158 "parser.mly"
    ( d )
# 7660 "parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run60 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.typ) = 
# 300 "parser.mly"
    ( TUnit )
# 7674 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run61 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.typ) = 
# 298 "parser.mly"
    ( TString)
# 7686 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run62 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.typ) = 
# 296 "parser.mly"
    ( TInt )
# 7698 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run63 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.typ) = 
# 306 "parser.mly"
    ( TBool )
# 7710 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run64 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | LID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v
    | LPAREN ->
        _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | TBool ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | TInt ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | TString ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | TUnit ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64

and _menhir_run65 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 7742 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (d : (
# 18 "parser.mly"
       (string)
# 7750 "parser.ml"
    )) = _v in
    let _v : (Lang.typ) = 
# 302 "parser.mly"
    ( TBase d )
# 7755 "parser.ml"
     in
    _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (s : (
# 18 "parser.mly"
       (string)
# 7772 "parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.typ) = 
# 310 "parser.mly"
    ( TVar s )
# 7779 "parser.ml"
         in
        _menhir_goto_typ_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_exp_op : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState372 | MenhirState368 | MenhirState362 | MenhirState358 | MenhirState342 | MenhirState0 | MenhirState329 | MenhirState324 | MenhirState292 | MenhirState7 | MenhirState261 | MenhirState31 | MenhirState38 | MenhirState39 | MenhirState251 | MenhirState249 | MenhirState245 | MenhirState243 | MenhirState239 | MenhirState235 | MenhirState230 | MenhirState224 | MenhirState222 | MenhirState218 | MenhirState216 | MenhirState212 | MenhirState208 | MenhirState96 | MenhirState97 | MenhirState200 | MenhirState202 | MenhirState140 | MenhirState143 | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LARGER ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LARGEREQ ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQ ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | NOTEQ ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AHOLE ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | BEGIN ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | FALSE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | HOLE ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | INT _v ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
            | LBRACKET ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
            | LISTAPPEND ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTASSOC ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTEXISTS ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTFILTER ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTFIND ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTFOLDL ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTFOLDR ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTFORALL ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTHD ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTLENGTH ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTMAP ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTMAPI ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTMEM ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTMEMQ ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTNTH ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTREV ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTREVAPD ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTREVMAP ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTSORT ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LISTTL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | MINUS ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | NOT ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | RAISE ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | SHOLE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | STRING _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
            | STRINGCONCAT ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | TRUE ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState171
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.lexp))) = _menhir_stack in
            let _v : (Lang.lexp) = 
# 384 "parser.mly"
    ( e )
# 7920 "parser.ml"
             in
            _menhir_goto_exp_struct _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 424 "parser.mly"
    ( (gen_label(), STRCON (e1,e2)) )
# 7957 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.lexp) = 
# 392 "parser.mly"
    ( (gen_label(), MUL (e1, e2)) )
# 7974 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | COMMA | DEFAND | DOUBLECOLON | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | MINUS | NOTEQ | OR | PIPE | PLUS | RBRACKET | RPAREN | SEMI | STRCON | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 388 "parser.mly"
    ( (gen_label(), ADD (e1, e2)) )
# 7995 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.lexp) = 
# 396 "parser.mly"
    ( (gen_label(), MOD (e1, e2)) )
# 8012 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
        let _2 = () in
        let _v : (Lang.lexp) = 
# 394 "parser.mly"
    ( (gen_label(), DIV (e1, e2)) )
# 8023 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | COMMA | DEFAND | DOUBLECOLON | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | MINUS | NOTEQ | OR | PIPE | PLUS | RBRACKET | RPAREN | SEMI | STRCON | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 390 "parser.mly"
    ( (gen_label(), SUB (e1, e2)) )
# 8044 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | AND | AT | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | STRCON | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 422 "parser.mly"
    ( (gen_label(), DOUBLECOLON (e1, e2)) )
# 8077 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState169 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 420 "parser.mly"
    ( (gen_label(), AT (e1, e2)) )
# 8114 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LARGER ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LARGEREQ ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQ ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | NOTEQ ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 402 "parser.mly"
    ( (gen_label(), OR (e1, e2)) )
# 8165 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 418 "parser.mly"
    ( (gen_label(), NOTEQ (e1, e2)) )
# 8202 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 410 "parser.mly"
    ( (gen_label(), LESSEQ (e1, e2)) )
# 8239 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 406 "parser.mly"
    ( (gen_label(), LESS (e1, e2)) )
# 8276 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 412 "parser.mly"
    ( (gen_label(), LARGEREQ (e1, e2)) )
# 8313 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 408 "parser.mly"
    ( (gen_label(), LARGER (e1, e2)) )
# 8350 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState184 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 416 "parser.mly"
    ( (gen_label(), EQUAL (e1, e2)) )
# 8388 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | NOTEQ | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 414 "parser.mly"
    ( (gen_label(), EQUAL (e1, e2)) )
# 8425 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AT ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | DIVIDE ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | DOUBLECOLON ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LARGER ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LARGEREQ ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQ ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | MOD ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | NOTEQ ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | STRCON ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | AND | COMMA | DEFAND | ELSE | END | EOF | EXCEPTION | FATARR | IN | LET | OR | PIPE | RBRACKET | RPAREN | SEMI | THEN | TYPE | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Lang.lexp))), _, (e2 : (Lang.lexp))) = _menhir_stack in
            let _2 = () in
            let _v : (Lang.lexp) = 
# 404 "parser.mly"
    ( (gen_label(), AND (e1, e2)) )
# 8474 "parser.ml"
             in
            _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 400 "parser.mly"
    ( (gen_label(), MINUS e) )
# 8491 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 398 "parser.mly"
    ( (gen_label(), NOT e) )
# 8502 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce50 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.lexp list) = 
# 434 "parser.mly"
    ( [] )
# 8513 "parser.ml"
     in
    _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run271 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 8520 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | LID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState272 _v
        | LPAREN ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | PIPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState272 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | UID _v ->
                _menhir_run273 _menhir_env (Obj.magic _menhir_stack) MenhirState276 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState276)
        | TBool ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | TInt ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | TString ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | TUnit ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | UID _v ->
            _menhir_run273 _menhir_env (Obj.magic _menhir_stack) MenhirState272 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState272)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_prog : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 8575 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 8583 "parser.ml"
    )) = _v in
    Obj.magic _1

and _menhir_goto_examples : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.examples) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EOF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (es : (Lang.examples))) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 8611 "parser.ml"
                ) = 
# 130 "parser.mly"
    ( (es, []) )
# 8615 "parser.ml"
                 in
                _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
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
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.input * Lang.value))), _, (es : (Lang.examples))) = _menhir_stack in
        let _v : (Lang.examples) = 
# 610 "parser.mly"
    ( e::es)
# 8637 "parser.ml"
         in
        _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce60 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 19 "parser.mly"
       (string)
# 8646 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 8652 "parser.ml"
    ))) = _menhir_stack in
    let _v : (Lang.lexp) = 
# 456 "parser.mly"
    ( (gen_label(), ECtor (c, [])) )
# 8657 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 19 "parser.mly"
       (string)
# 8664 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.let_bind) = 
# 254 "parser.mly"
    ( BindUnder )
# 8679 "parser.ml"
     in
    _menhir_goto_bind_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_run44 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 8703 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 18 "parser.mly"
       (string)
# 8711 "parser.ml"
    )) = _v in
    let _v : (Lang.let_bind) = 
# 256 "parser.mly"
    ( BindOne x )
# 8716 "parser.ml"
     in
    _menhir_goto_bind_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run99 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.pat) = 
# 584 "parser.mly"
    ( PUnder )
# 8728 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run100 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 19 "parser.mly"
       (string)
# 8735 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | UID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState100 in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        _menhir_reduce156 _menhir_env (Obj.magic _menhir_stack)
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | ARR | COMMA | DOUBLECOLON | PIPE | RBRACKET | RPAREN | SEMI ->
        _menhir_reduce156 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100

and _menhir_run102 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.pat) = 
# 578 "parser.mly"
    ( PBool true )
# 8781 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run103 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (
# 20 "parser.mly"
       (int)
# 8798 "parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.pat) = 
# 576 "parser.mly"
    ( PInt c )
# 8805 "parser.ml"
         in
        _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run138 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138

and _menhir_run105 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c : (
# 20 "parser.mly"
       (int)
# 8859 "parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.pat) = 
# 574 "parser.mly"
    ( PInt (-c) )
# 8866 "parser.ml"
         in
        _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run107 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState107 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.pat) = 
# 570 "parser.mly"
    ( PUnit )
# 8907 "parser.ml"
         in
        _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 8924 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 18 "parser.mly"
       (string)
# 8932 "parser.ml"
    )) = _v in
    let _v : (Lang.pat) = 
# 582 "parser.mly"
    ( PVar x )
# 8937 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run110 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState110 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.pat) = 
# 588 "parser.mly"
    ( PList [] )
# 8972 "parser.ml"
         in
        _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110

and _menhir_run112 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "parser.mly"
       (int)
# 8989 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 20 "parser.mly"
       (int)
# 8997 "parser.ml"
    )) = _v in
    let _v : (Lang.pat) = 
# 572 "parser.mly"
    ( PInt (c) )
# 9002 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run113 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.pat) = 
# 580 "parser.mly"
    ( PBool false )
# 9014 "parser.ml"
     in
    _menhir_goto_pat_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.arg list) = 
# 318 "parser.mly"
    ( [] )
# 9023 "parser.ml"
     in
    _menhir_goto_args _menhir_env _menhir_stack _menhir_s _v

and _menhir_run56 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState57 in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState83
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83)
        | COMMA | RPAREN ->
            _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | LPAREN ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState57
    | UNDERBAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState57 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | LID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | TBool ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | TInt ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | TString ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | TUnit ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
        | COMMA | RPAREN ->
            _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 9125 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run273 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 19 "parser.mly"
       (string)
# 9135 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | LID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState274 _v
        | LPAREN ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | TBool ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | TInt ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | TString ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | TUnit ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState274
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState274)
    | DEFAND | EOF | EXCEPTION | LET | PIPE | SEMI | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 9170 "parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.ctor) = 
# 196 "parser.mly"
    ( (c, []) )
# 9175 "parser.ml"
         in
        _menhir_goto_ctor _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.lexp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState372 | MenhirState368 | MenhirState362 | MenhirState358 | MenhirState342 | MenhirState0 | MenhirState329 | MenhirState324 | MenhirState292 | MenhirState7 | MenhirState261 | MenhirState31 | MenhirState33 | MenhirState34 | MenhirState38 | MenhirState39 | MenhirState251 | MenhirState249 | MenhirState245 | MenhirState243 | MenhirState239 | MenhirState235 | MenhirState230 | MenhirState224 | MenhirState222 | MenhirState218 | MenhirState216 | MenhirState212 | MenhirState208 | MenhirState96 | MenhirState97 | MenhirState200 | MenhirState202 | MenhirState140 | MenhirState143 | MenhirState147 | MenhirState171 | MenhirState187 | MenhirState183 | MenhirState184 | MenhirState181 | MenhirState179 | MenhirState177 | MenhirState175 | MenhirState173 | MenhirState151 | MenhirState169 | MenhirState167 | MenhirState165 | MenhirState159 | MenhirState163 | MenhirState161 | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AHOLE ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | BEGIN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | HOLE ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | INT _v ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | LBRACKET ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LID _v ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | LISTAPPEND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTASSOC ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTEXISTS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTFILTER ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTFIND ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTFOLDL ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTFOLDR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTFORALL ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTHD ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTLENGTH ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTMAP ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTMAPI ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTMEM ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTMEMQ ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTNTH ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTREV ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTREVAPD ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTREVMAP ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTSORT ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LISTTL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | SHOLE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | STRING _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | STRINGCONCAT ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | TRUE ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | UID _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | AND | AT | COMMA | DEFAND | DIVIDE | DOUBLECOLON | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | MINUS | MOD | NOTEQ | OR | PIPE | PLUS | RBRACKET | RPAREN | SEMI | STAR | STRCON | THEN | TYPE | WITH ->
            _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155)
    | MenhirState156 | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AHOLE ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | BEGIN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | HOLE ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | INT _v ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | LBRACKET ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LID _v ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | LISTAPPEND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTASSOC ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTEXISTS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTFILTER ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTFIND ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTFOLDL ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTFOLDR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTFORALL ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTHD ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTLENGTH ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTMAP ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTMAPI ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTMEM ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTMEMQ ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTNTH ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTREV ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTREVAPD ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTREVMAP ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTSORT ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LISTTL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | SHOLE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | STRING _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | STRINGCONCAT ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | TRUE ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | UID _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | AND | AT | COMMA | DEFAND | DIVIDE | DOUBLECOLON | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | MINUS | MOD | NOTEQ | OR | PIPE | PLUS | RBRACKET | RPAREN | SEMI | STAR | STRCON | THEN | TYPE | WITH ->
            _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156)
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Lang.lexp))) = _menhir_stack in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 426 "parser.mly"
    ( (gen_label(), Raise e) )
# 9351 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (c : (
# 19 "parser.mly"
       (string)
# 9360 "parser.ml"
        ))), _, (e : (Lang.lexp))) = _menhir_stack in
        let _v : (Lang.lexp) = 
# 430 "parser.mly"
    ( (gen_label(), ECtor (c, [e])) )
# 9365 "parser.ml"
         in
        _menhir_goto_exp_op _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run270 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run271 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState270

and _menhir_goto_empty_decls : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (ds : (Lang.decl list))) = _menhir_stack in
        let _2 = () in
        let _v : (
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 9399 "parser.ml"
        ) = 
# 126 "parser.mly"
    ( ([],(List.rev ds)) )
# 9403 "parser.ml"
         in
        _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run286 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState286 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState286
    | REC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState286 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
        | LPAREN ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState287
        | UNDERBAR ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState287
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState287)
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState286
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState286

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState372 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState370 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState368 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState364 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState362 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState360 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState358 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState356 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState353 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState349 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState347 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState342 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState329 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState324 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState314 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState312 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState310 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState307 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState295 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState292 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState290 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState288 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState286 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState280 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState276 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState274 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState270 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState262 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState261 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState254 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState218 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState196 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState191 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState184 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState169 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce46 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.examples) = 
# 608 "parser.mly"
    ( [] )
# 10015 "parser.ml"
     in
    _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 19 "parser.mly"
       (string)
# 10022 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState1
    | UID _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState1 _v
    | AND | AT | COMMA | DEFAND | DIVIDE | DOUBLECOLON | ELSE | END | EOF | EQ | EXCEPTION | FATARR | IN | LARGER | LARGEREQ | LESS | LESSEQ | LET | MINUS | MOD | NOTEQ | OR | PIPE | PLUS | RBRACKET | RPAREN | SEMI | STAR | STRCON | THEN | TYPE | WITH ->
        _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 446 "parser.mly"
    ( (gen_label(), TRUE) )
# 10110 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 508 "parser.mly"
    ( (gen_label(), EVar "__string_concat__") )
# 10122 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "parser.mly"
       (string)
# 10129 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 21 "parser.mly"
       (string)
# 10137 "parser.ml"
    )) = _v in
    let _v : (Lang.lexp) = 
# 444 "parser.mly"
    ( (gen_label(), String c) )
# 10142 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 466 "parser.mly"
    ( (gen_label(), SStr (Lang.gen_const ())) )
# 10154 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState9
    | UID _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState7 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 450 "parser.mly"
    ( (gen_label(), EUnit) )
# 10583 "parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 470 "parser.mly"
    ( (gen_label(), (EVar "__list_tl__")) )
# 10609 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 492 "parser.mly"
    ( (gen_label(), (EVar "__list_sort__")) )
# 10621 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 494 "parser.mly"
    ( (gen_label(), (EVar "__list_rev_map__")) )
# 10633 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 498 "parser.mly"
    ( (gen_label(), (EVar "__list_rev_append__")) )
# 10645 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 486 "parser.mly"
    ( (gen_label(), (EVar "__list_rev__")) )
# 10657 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 484 "parser.mly"
    ( (gen_label(), (EVar "__list_nth__")) )
# 10669 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 496 "parser.mly"
    ( (gen_label(), (EVar "__list_memq__")) )
# 10681 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 474 "parser.mly"
    ( (gen_label(), (EVar "__list_mem__")) )
# 10693 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 500 "parser.mly"
    ( (gen_label(), (EVar "__list_map_i__")) )
# 10705 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 472 "parser.mly"
    ( (gen_label(), (EVar "__list_map__")) )
# 10717 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run20 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 482 "parser.mly"
    ( (gen_label(), (EVar "__list_length__")) )
# 10729 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 468 "parser.mly"
    ( (gen_label(), (EVar "__list_hd__")) )
# 10741 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 502 "parser.mly"
    ( (gen_label(), (EVar "__list_for_all__")) )
# 10753 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 490 "parser.mly"
    ( (gen_label(), (EVar "__list_foldr__")) )
# 10765 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 488 "parser.mly"
    ( (gen_label(), (EVar "__list_foldl__")) )
# 10777 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run25 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 504 "parser.mly"
    ( (gen_label(), (EVar "__list_find__")) )
# 10789 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 478 "parser.mly"
    ( (gen_label(), (EVar "__list_filter__")) )
# 10801 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 476 "parser.mly"
    ( (gen_label(), (EVar "__list_exists__")) )
# 10813 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 506 "parser.mly"
    ( (gen_label(), (EVar "__list_assoc__")) )
# 10825 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 480 "parser.mly"
    ( (gen_label(), (EVar "__list_append__")) )
# 10837 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 18 "parser.mly"
       (string)
# 10844 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 18 "parser.mly"
       (string)
# 10852 "parser.ml"
    )) = _v in
    let _v : (Lang.lexp) = 
# 442 "parser.mly"
    ( (gen_label(), EVar x) )
# 10857 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | LPAREN ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | REC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState40 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
        | LPAREN ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | UNDERBAR ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | UNDERBAR ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState31 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Lang.lexp) = 
# 452 "parser.mly"
    ( (gen_label(), EList []) )
# 10984 "parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "parser.mly"
       (int)
# 11005 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 20 "parser.mly"
       (int)
# 11013 "parser.ml"
    )) = _v in
    let _v : (Lang.lexp) = 
# 440 "parser.mly"
    ( (gen_label(), Const c) )
# 11018 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run97 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState97
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 462 "parser.mly"
    ( (gen_label(), Lang.gen_hole()) )
# 11123 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run98 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT _v ->
        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | LBRACKET ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | LPAREN ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | MINUS ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | PIPE ->
        _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | PLUS ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | TRUE ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | UID _v ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | UNDERBAR ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98

and _menhir_run141 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | LPAREN ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | UNDERBAR ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | ARR ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 448 "parser.mly"
    ( (gen_label(), FALSE) )
# 11187 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run331 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | UID _v ->
        _menhir_run273 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState331

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LET ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run144 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Lang.lexp) = 
# 464 "parser.mly"
    ( (gen_label(), SInt (Lang.gen_const ())) )
# 11305 "parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

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
# 120 "parser.mly"
      (Lang.examples * Lang.prog)
# 11324 "parser.ml"
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
    | AHOLE ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BEGIN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EXCEPTION ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FUN ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FUNCTION ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | HOLE ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | IF ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | INT _v ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AHOLE ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | BEGIN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | FUN ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | FUNCTION ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | HOLE ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | IF ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | INT _v ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState292 _v
        | LBRACKET ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LET ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LID _v ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState292 _v
        | LISTAPPEND ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTASSOC ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTEXISTS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTFILTER ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTFIND ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTFOLDL ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTFOLDR ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTFORALL ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTHD ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTLENGTH ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTMAP ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTMAPI ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTMEM ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTMEMQ ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTNTH ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTREV ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTREVAPD ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTREVMAP ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTSORT ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LISTTL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | MATCH ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | MINUS ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | NOT ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | RAISE ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | SHOLE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | STRING _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState292 _v
        | STRINGCONCAT ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | TRUE ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState292 _v
        | RBRACE ->
            _menhir_reduce46 _menhir_env (Obj.magic _menhir_stack) MenhirState292
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState292)
    | LBRACKET ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LET ->
        _menhir_run286 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LISTAPPEND ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTASSOC ->
        _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTEXISTS ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTFILTER ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTFIND ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTFOLDL ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTFOLDR ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTFORALL ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTHD ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTLENGTH ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTMAP ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTMAPI ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTMEM ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTMEMQ ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTNTH ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTREV ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTREVAPD ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTREVMAP ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTSORT ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LISTTL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MATCH ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MINUS ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NOT ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | RAISE ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _2 = () in
            let _1 = () in
            let _v : (Lang.decl list) = 
# 138 "parser.mly"
    ( [] )
# 11524 "parser.ml"
             in
            _menhir_goto_empty_decls _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | SHOLE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | STRING _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | STRINGCONCAT ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | TRUE ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | TYPE ->
        _menhir_run270 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _v : (Lang.decl list) = 
# 136 "parser.mly"
    ( [] )
# 11551 "parser.ml"
         in
        _menhir_goto_empty_decls _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 233 "/Users/prl/.opam/system/lib/menhir/standard.mly"
  

# 11562 "parser.ml"
