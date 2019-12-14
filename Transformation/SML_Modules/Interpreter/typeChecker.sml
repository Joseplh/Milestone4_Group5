(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)


exception model_error;
fun error msg = (print msg; raise model_error);

fun typeOf( itree(inode("Expression",_), 
                [
                    ExprOr0
                ]), 
            m0
        ) = typeOf(ExprOr0, m0)
        
  | typeOf( itree(inode("ExprOr",_), 
                [
                    ExprOr0,
                    itree(inode("or",_),[]),
                    ExprAnd0
                ]), 
            m0
        ) = 
        let
            val t0 = typeOf(ExprOr0, m0)
            val t1 = typeOf(ExprAnd0, m0)
        in
            if t0 = BOOL andalso t0 = t1
            then BOOL
            else ERROR
        end

  | typeOf( itree(inode("ExprOr",_), 
                [
                    ExprAnd0
                ]), 
            m0
        ) = typeOf(ExprAnd0, m0)

  | typeOf( itree(inode("ExprAnd",_), 
                [
                    ExprAnd0,
                    itree(inode("and",_),[]),
                    ExprBoolComp0
                ]), 
            m0
        ) = 
        let
            val t0 = typeOf(ExprAnd0, m0)
            val t1 = typeOf(ExprBoolComp0, m0)
        in
            if t0 = BOOL andalso t0 = t1
            then BOOL
            else ERROR
        end

  | typeOf( itree(inode("ExprAnd",_), 
                [
                    ExprBoolComp0
                ]), 
            m0
        ) = typeOf(ExprBoolComp0, m0)
        
  | typeOf( itree(inode("ExprBoolComp",_), 
                [
                    ExprBoolComp0,
                    itree(inode("!=",_),[]),
                    ExprIntComp0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprBoolComp0, m0)
            val t1 = typeOf(ExprIntComp0, m0)
        in
            if t1 <> ERROR andalso t0 = t1
            then BOOL
            else ERROR
        end
 
  | typeOf( itree(inode("ExprBoolComp",_), 
                [
                    ExprBoolComp0,
                    itree(inode("==",_),[]),
                    ExprIntComp0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprBoolComp0, m0)
            val t1 = typeOf(ExprIntComp0, m0)
        in
            if t1 <> ERROR andalso t0 = t1
            then BOOL
            else ERROR
        end
        
  | typeOf( itree(inode("ExprBoolComp",_), 
                [
                    ExprIntComp0
                ]), 
            m0
        ) = typeOf(ExprIntComp0, m0)     

  | typeOf( itree(inode("ExprIntComp",_), 
                [
                    ExprIntComp0,
                    itree(inode("<",_),[]),
                    ExprAddSub0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprIntComp0, m0)
            val t1 = typeOf(ExprAddSub0, m0)
        in
            if t0 = INT andalso t0 = t1
            then BOOL
            else ERROR
        end

  | typeOf( itree(inode("ExprIntComp",_), 
                [
                    ExprIntComp0,
                    itree(inode(">",_),[]),
                    ExprAddSub0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprIntComp0, m0)
            val t1 = typeOf(ExprAddSub0, m0)
        in
            if t0 = INT andalso t0 = t1
            then BOOL
            else ERROR
        end

  | typeOf( itree(inode("ExprIntComp",_), 
                [
                    ExprAddSub0
                ]), 
            m0
        ) = typeOf(ExprAddSub0, m0)

  | typeOf( itree(inode("ExprAddSub",_), 
                [
                    ExprAddSub0,
                    itree(inode("+",_),[]),
                    ExprMulDivMod0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprAddSub0, m0)
            val t1 = typeOf(ExprMulDivMod0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end
        
  | typeOf( itree(inode("ExprAddSub",_), 
                [
                    ExprAddSub0,
                    itree(inode("-",_),[]),
                    ExprMulDivMod0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprAddSub0, m0)
            val t1 = typeOf(ExprMulDivMod0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end        
        
  | typeOf( itree(inode("ExprAddSub",_), 
                [
                    ExprMulDivMod0
                ]), 
            m0
        ) = typeOf(ExprMulDivMod0, m0)
        
  | typeOf( itree(inode("ExprMulDivMod",_), 
                [
                    ExprMulDivMod0,
                    itree(inode("*",_),[]),
                    ExprNeg0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprMulDivMod0, m0)
            val t1 = typeOf(ExprNeg0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end

  | typeOf( itree(inode("ExprMulDivMod",_), 
                [
                    ExprMulDivMod0,
                    itree(inode("/",_),[]),
                    ExprNeg0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprMulDivMod0, m0)
            val t1 = typeOf(ExprNeg0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end
        
  | typeOf( itree(inode("ExprMulDivMod",_), 
                [
                    ExprMulDivMod0,
                    itree(inode("MOD",_),[]),
                    ExprNeg0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprMulDivMod0, m0)
            val t1 = typeOf(ExprNeg0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end    

  | typeOf( itree(inode("ExprMulDivMod",_), 
                [
                    ExprNeg0
                ]), 
            m0
        ) = typeOf(ExprNeg0, m0)

  | typeOf( itree(inode("ExprNeg",_), 
                [
                    itree(inode("~",_),[]),
                    ExprNeg0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprNeg0, m0)
        in
            if t0 = INT
            then INT
            else ERROR
        end
        
  | typeOf( itree(inode("ExprNeg",_), 
                [
                    itree(inode("not",_),[]),
                    ExprNeg0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprNeg0, m0)
        in
            if t0 = BOOL
            then BOOL
            else ERROR
        end        
        
  | typeOf( itree(inode("ExprNeg",_), 
                [
                    ExprExp0
                ]), 
            m0
        ) = typeOf(ExprExp0, m0)  
        
  | typeOf( itree(inode("ExprExp",_), 
                [
                    ExprBase0,
                    itree(inode("^",_),[]),
                    ExprExp0
                ]), 
            m0
        ) =
        let
            val t0 = typeOf(ExprBase0, m0)
            val t1 = typeOf(ExprExp0, m0)
        in
            if t0 = INT andalso t0 = t1
            then INT
            else ERROR
        end
                
  | typeOf( itree(inode("ExprExp",_), 
                [
                    ExprBase0
                ]), 
            m0
        ) = typeOf(ExprBase0, m0)    
        
  | typeOf( itree(inode("ExprBase",_), 
                [
                    Interger0 as itree(inode("Integer",_), children)
                ]), 
            m0
        ) = INT         

  | typeOf( itree(inode("ExprBase",_), 
                [
                    Boolean0 as itree(inode("true",_), children)
                ]), 
            m0
        ) = BOOL     

  | typeOf( itree(inode("ExprBase",_), 
                [
                    Boolean0 as itree(inode("false",_), children)
                ]), 
            m0
        ) = BOOL     

  | typeOf( itree(inode("ExprBase",_), 
                [
                    Variable0 as itree(inode("Variable",_), children)
                ]), 
            m0
        ) = getType(accessEnv(getLeaf(Variable0), m0))

  | typeOf( itree(inode("ExprBase",_), 
                [
                    Increment0 as itree(inode("Increment",_), children)
                ]), 
            m0
        ) = typeOf(Increment0, m0)

  | typeOf( itree(inode("Increment",_), 
                [
                    itree(inode("++",_),[]),
                    Variable0
                ]), 
            m0
        ) = 
        let
            val t0 = getType(accessEnv(getLeaf(Variable0), m0))
        in
            if t0 = INT
            then INT
            else ERROR
        end
        
    | typeOf( itree(inode("Increment",_), 
                [
                    itree(inode("--",_),[]),
                    Variable0
                ]), 
            m0
        ) = 
        let
            val t0 = getType(accessEnv(getLeaf(Variable0), m0))
        in
            if t0 = INT
            then INT
            else ERROR
        end

    | typeOf( itree(inode("Increment",_), 
                [
                    Variable0,
                    itree(inode("++",_),[])
                ]), 
            m0
        ) = 
        let
            val t0 = getType(accessEnv(getLeaf(Variable0), m0))
        in
            if t0 = INT
            then INT
            else ERROR
        end

    | typeOf( itree(inode("Increment",_), 
                [
                    Variable0,
                    itree(inode("--",_),[])
                ]), 
            m0
        ) = 
        let
            val t0 = getType(accessEnv(getLeaf(Variable0), m0))
        in
            if t0 = INT
            then INT
            else ERROR
        end
        
    | typeOf( itree(inode("ExprBase",_), 
                [
                    itree(inode("(",_),[]),
                    Expression0,
                    itree(inode(")",_),[])
                ]), 
            m0
        ) = typeOf(Expression0, m0)
        
    | typeOf( itree(inode("ExprBase",_), 
                [
                    itree(inode("|",_),[]),
                    Expression0,
                    itree(inode("|",_),[])
                ]), 
            m0
        ) = 
        let
            val t0 = typeOf(Expression0, m0)    
        in
            if t0 = INT
            then INT
            else ERROR
        end
        
  | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  
  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")

fun typeCheck( itree(inode("prog",_), 
                    [ 
                        StatementList0 
                    ] ), 
                m0 
            ) = typeCheck(StatementList0, m0)
            
  | typeCheck( itree(inode("StatementList",_), 
                    [ 
                        Statement0,
                        itree(inode(";",_),[]),
                        StatementList0
                    ] ), 
                m0 
            ) = 
            let
                val m1 = typeCheck(Statement0, m0)
                val m2 = typeCheck(StatementList0, m1)
            in
                m2
            end
            
  | typeCheck( itree(inode("StatementList",_), 
                    [ 
                        Epsilon0
                    ] ), 
                m0 
            ) = m0
            
  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Declaration0 as itree(inode("Declaration",_), children)
                    ] ), 
                m0 
            ) = typeCheck(Declaration0, m0)

  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Assignment0 as itree(inode("Assignment",_), children)
                    ] ), 
                m0 
            ) = typeCheck(Assignment0, m0)
            
  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Conditional0 as itree(inode("Conditional",_), children)
                    ] ), 
                m0 
            ) = typeCheck(Conditional0, m0)

  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Increment0 as itree(inode("Increment",_), children)
                    ] ), 
                m0 
            ) = 
            let
                val t0 = typeOf(Increment0, m0)
            in
                if t0 = INT
                then m0
                else raise model_error
            end
            
  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Print0 as itree(inode("Print",_), children)
                    ] ), 
                m0 
            ) = typeCheck(Print0, m0)
            
  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        Block0 as itree(inode("Block",_), children)
                    ] ), 
                m0 
            ) = typeCheck(Block0, m0)

  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        ForLoop0 as itree(inode("ForLoop",_), children)
                    ] ), 
                m0 
            ) = typeCheck(ForLoop0, m0)
            
  | typeCheck( itree(inode("Statement",_), 
                    [ 
                        WhileLoop0 as itree(inode("WhileLoop",_), children)
                    ] ), 
                m0 
            ) = typeCheck(WhileLoop0, m0)
            
  | typeCheck( itree(inode("Declaration",_), 
                    [ 
                        itree(inode("INTEGER",_),[]),
                        Variable0
                    ] ), 
                m0 
            ) = updateEnv(getLeaf(Variable0), INT, m0)

  | typeCheck( itree(inode("Declaration",_), 
                    [ 
                        itree(inode("BOOLEAN",_),[]),
                        Variable0
                    ] ), 
                m0 
            ) = updateEnv(getLeaf(Variable0), BOOL, m0)
            
  | typeCheck( itree(inode("Assignment",_), 
                    [ 
                        Variable0,
                        itree(inode("=",_),[]),
                        Expression0
                    ] ), 
                m0 
            ) =
            let
                val t0 = getType(accessEnv(getLeaf(Variable0), m0))
                val t1 = typeOf(Expression0, m0)
            in
                if t0 = t1 
                then m0
                else error "Assignment Error"
            end
            
  | typeCheck( itree(inode("Assignment",_), 
                    [ 
                        itree(inode("INTEGER",_),[]),
                        Variable0,
                        itree(inode("=",_),[]),
                        Expression0
                    ] ), 
                m0 
            ) = 
            let
                val m1 = updateEnv(getLeaf(Variable0), INT, m0)
                val t0 = typeOf(Expression0, m0)
            in
                if t0 = INT
                then m1
                else raise model_error
            end
  
  | typeCheck( itree(inode("Assignment",_), 
                    [ 
                        itree(inode("BOOLEAN",_),[]),
                        Variable0,
                        itree(inode("=",_),[]),
                        Expression0
                    ] ), 
                m0 
            ) = 
            let
                val m1 = updateEnv(getLeaf(Variable0), BOOL, m0)
                val t0 = typeOf(Expression0, m0)
            in
                if t0 = BOOL
                then m1
                else raise model_error
            end

  | typeCheck( itree(inode("Conditional",_), 
                    [ 
                        itree(inode("if",_),[]),
                        itree(inode("(",_),[]),
                        Expression0,
                        itree(inode(")",_),[]),
                        Block0
                    ] ), 
                m0 
            ) =
            let
                val t0 = typeOf(Expression0, m0)
                val m1 = typeCheck(Block0, m0)
            in
                if t0 = BOOL
                then m0
                else raise model_error
            end

  | typeCheck( itree(inode("Conditional",_), 
                    [ 
                        itree(inode("if",_),[]),
                        itree(inode("(",_),[]),
                        Expression0,
                        itree(inode(")",_),[]),
                        Block0,
                        itree(inode("else",_),[]),
                        Block1
                    ] ), 
                m0 
            ) =
            let
                val t0 = typeOf(Expression0, m0)
                val m1 = typeCheck(Block0, m0)
                val m2 = typeCheck(Block1, m0)
            in
                if t0 = BOOL
                then m0
                else raise model_error
            end
          
  | typeCheck( itree(inode("WhileLoop",_), 
                    [ 
                        itree(inode("while",_),[]),
                        itree(inode("(",_),[]),
                        Expression0,
                        itree(inode(")",_),[]),
                        Block0
                    ] ), 
                m0 
            ) =
            let
                val t0 = typeOf(Expression0, m0)
                val m1 = typeCheck(Block0, m0)
            in
                if t0 = BOOL
                then m0
                else raise model_error
            end

  | typeCheck( itree(inode("ForLoop",_), 
                    [ 
                        itree(inode("for",_),[]),
                        itree(inode("(",_),[]),
                        Assignment0,
                        itree(inode(";",_),[]),
                        Expression0,
                        itree(inode(";",_),[]),
                        Increment0,
                        itree(inode(")",_),[]),
                        Block0
                    ] ), 
                m0 
            ) =
            let
                val m1 = typeCheck(Assignment0, m0)
                val t = typeOf(Expression0, m1)
                val m2 = typeOf(Increment0, m1)
                val m3 = typeCheck(Block0, m1)
            in
                if t = BOOL
                then m1
                else raise model_error
            end

  | typeCheck( itree(inode("Print",_), 
                    [ 
                        itree(inode("print",_),[]),
                        itree(inode("(",_),[]),
                        Expression0,
                        itree(inode(")",_),[])
                    ] ), 
                m0 
            ) =
            let
                val t0 = typeOf(Expression0, m0)
            in
                if t0 = ERROR
                then raise model_error
                else m0
            end
            
  | typeCheck( itree(inode("Block",_), 
                    [ 
                        itree(inode("{",_),[]),
                        StatementList0,
                        itree(inode("}",_),[])
                    ] ), 
                m0 
            ) =
            let
                val (env0, next0, s0) = m0
                val (env1, next1, s1) = typeCheck(StatementList0, m0)
            in
                (env0, next0, s1)
            end
       
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








