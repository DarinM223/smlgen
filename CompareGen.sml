structure CompareGen =
struct
  open BuildAst Utils MutRecTy

  datatype env =
    Env of
      { c: int ref
      , vars: Token.t list ref
      , usesList: bool ref
      , env: MutRecTy.env
      }
  fun fresh (Env {c, vars, ...}) t =
    let
      val i = !c before c := !c + 1
      val tok = appendTokens t (mkToken (Int.toString i))
    in
      (vars := tok :: !vars; tok)
    end

  fun mkCompare t =
    let
      val (prefix, t) =
        (Substring.splitr (fn ch => ch <> #".") o Substring.full
         o Token.toString) t
      val prependedShow =
        case Substring.string t of
          "t" => "compare"
        | t => "compare" ^ capitalize t
    in
      mkToken (Substring.string prefix ^ prependedShow)
    end

  val tTok = mkToken "t"

  fun tyPat env (Ty.Var _) =
        Pat.Const (fresh env tTok)
    | tyPat env (Ty.Record {elems, ...}) =
        destructRecordPat' (List.map (fn {lab, ty, ...} => (lab, tyPat env ty))
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Tuple {elems, ...}) =
        destructTuplePat (List.map (tyPat env)
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Con _) =
        Pat.Const (fresh env tTok)
    | tyPat _ (Ty.Arrow _) = wildPat
    | tyPat env (Ty.Parens {ty, ...}) = tyPat env ty
  and tyPat' (env as Env {vars, ...}) ty =
    let
      val pat1 = tyPat env ty
      val vars1 = !vars before vars := []
      val pat2 = tyPat env ty
      val vars2 = !vars
      fun interleave (build, x :: xs, y :: ys) =
            interleave (x :: y :: build, xs, ys)
        | interleave (_, _ :: _, _) = raise Fail "Lists are different sizes"
        | interleave (_, _, _ :: _) = raise Fail "Lists are different sizes"
        | interleave (build, [], []) = build
    in
      (vars := interleave ([], vars1, vars2); destructTuplePat [pat1, pat2])
    end

  fun caseChainExp (_: Exp.exp list) : Exp.exp = raise Fail "caseChainExp"

  fun tyCon _ e "string" [] =
        appExp [Const (mkToken "String.compare"), e]
    | tyCon _ e "int" [] =
        appExp [Const (mkToken "Int.compare"), e]
    | tyCon (env as Env {usesList, ...}) e "list" [a] =
        ( usesList := true
        ; appExp [Const (mkToken "compareList"), parensExp (tyExp' env a), e]
        )
    | tyCon (env as Env {env = env', ...}) e (s: string) (args: Ty.ty list) =
        let
          val con = Const
            (if tyconIsGeneratedFix env' s then mkToken s
             else mkCompare (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, e]
        end
  and tyExp' (env as Env {c, vars, ...}) ty =
    ( c := 0
    ; vars := []
    ; case (tyPat' env ty, tyExp env ty) of
        ( pat as Pat.Tuple {elems, ...}
        , exp as App {left, right = Tuple {elems = elems', ...}, ...}
        ) =>
          let
            val elems = ArraySlice.foldr (op::) [] elems
            val elems' = ArraySlice.foldr (op::) [] elems'
          in
            case (elems, elems') of
              ([Pat.Const a, Pat.Const b], [Const a', Const b']) =>
                if Token.same (a, a') andalso Token.same (b, b') then left
                else singleFnExp pat exp
            | _ => singleFnExp pat exp
          end
      | (pat, exp) => singleFnExp pat exp
    )
  and tyExp (Env {vars = vars as ref (a :: b :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), tupleExp [Const a, Const b]])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        caseChainExp (List.map (tyExp env o #ty)
          (ArraySlice.foldr (op::) [] elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        caseChainExp (List.map (tyExp env) (ArraySlice.foldr (op::) [] elems))
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          fun con e =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, e]
            | NONE => tyCon env e id (syntaxSeqToList args)
        in
          case !vars of
            a :: b :: t => (vars := t; con (tupleExp [Const a, Const b]))
          | _ => raise Fail "No vars in con"
        end
    | tyExp _ (Ty.Arrow _) = raise Fail "Cannot compare functions"
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genTypebind ({elems, ...}: typbind) = raise Fail "typebind"

  fun genSimpleDatabind (env, ty, vars, constrs) = raise Fail "simple databind"
  fun genRecursiveDatabind (env, tycons, tys, vars) =
    raise Fail "recursive databind"

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
