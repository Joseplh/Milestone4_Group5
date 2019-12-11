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

fun typeOf (itree(inode("Increment",_),[itree(inode("++",_),[]),id]),m) = 
    let
        val t = typeOf (id,m)
    in
        if t = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("Increment",_),[itree(inode("--",_),[]),id]),m) = 
    let
        val t = typeOf (id,m)
    in
        if t = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("Increment",_),[id,itree(inode("++",_),[])]),m) = 
    let
        val t = typeOf (id,m)
    in
        if t = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("Increment",_),[id,itree(inode("--",_),[])]),m) = 
    let
        val t = typeOf (id,m)
    in
        if t = INT
        then INT
        else ERROR
    end

|   typeOf (itree(inode("Expr",_),[Expr,itree(inode("||",_),[]),AndExpr]),m) =
    let
        val t1 = typeOf (Expr,m)
        val t2 = typeOf (AndExpr,m)
    in
        if t1 = t2 andalso t1 = BOOL 
        then BOOL
        else ERROR
    end

|   typeOf (itree(inode("Expr",_),[AndExpr]),m) = typeOf (AndExpr,m)

|   typeOf (itree(inode("AndExpr",_),[AndExpr,itree(inode("&&",_),[]),EqualityExpr]),m) =
    let
        val t1 = typeOf (AndExpr,m)
        val t2 = typeOf (EqualityExpr,m)
    in
        if t1 = t2 andalso t1 = BOOL
        then BOOL
        else ERROR
    end

|   typeOf (itree(inode("AndExpr",_),[EqualityExpr]),m) = typeOf (EqualityExpr,m)

|   typeOf (itree(inode("EqualityExpr",_),[EqualityExpr,itree(inode("!=",_),[]),ComparisonExpr]),m) =
    let
        val t1 = typeOf (EqualityExpr,m)
        val t2 = typeOf (ComparisonExpr,m)
    in 
        if t1 = t2 andalso t1 <> ERROR
        then BOOL
        else ERROR
    end
    
|   typeOf (itree(inode("EqualityExpr",_),[EqualityExpr,itree(inode("==",_),[]),ComparisonExpr]),m) =
    let
        val t1 = typeOf (EqualityExpr,m)
        val t2 = typeOf (ComparisonExpr,m)
    in 
        if t1 = t2 andalso t1 <> ERROR
        then BOOL
        else ERROR
    end
    
|   typeOf (itree(inode("EqualityExpr",_),[ComparisonExpr]),m) = typeOF (ComparisonExpr,m)

|   typeOf (itree(inode("ComparisonExpr",_),[ComparisonExpr,itree(inode("<",_),[]),AddSubExpr]),m) =
    let
        val t1 = typeOf (ComparisonExpr,m)
        val t2 = typeOf (AddSubExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then BOOL
        else ERROR
    end

|   typeOf (itree(inode("ComparisonExpr",_),[ComparisonExpr,itree(inode(">",_),[]),AddSubExpr]),m) =
    let
        val t1 = typeOf (ComparisonExpr,m)
        val t2 = typeOf (AddSubExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then BOOL
        else ERROR
    end

|   typeOf (itree(inode("ComparisonExpr",_),[AddSubExpr]),m) = typeOf (AddSubExpr,m)

|   typeOf (itree(inode("AddSubExpr",_),[AddSubExpr,itree(inode("+",_),[]),MultDivModExpr]),m) =
    let
        val t1 = typeOf (AddSubExpr,m)
        val t2 = typeOf (MultDivModExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("AddSubExpr",_),[AddSubExpr,itree(inode("-",_),[]),MultDivModExpr]),m) =
    let
        val t1 = typeOf (AddSubExpr,m)
        val t2 = typeOf (MultDivModExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("AddSubExpr",_),[MultDivModExpr]),m) = typeOf (MultDivModExpr,m)

|   typeOf (itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("*",_),[]),UnaryExpr]),m) =
    let
        val t1 = typeOf (MultDivModExpr,m)
        val t2 = typeOf (UnaryExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("DIV",_),[]),UnaryExpr]),m) =
    let
        val t1 = typeOf (MultDivModExpr,m)
        val t2 = typeOf (UnaryExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("MOD",_),[]),UnaryExpr]),m) =
    let
        val t1 = typeOf (MultDivModExpr,m)
        val t2 = typeOf (UnaryExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("MultDivModExpr",_),[UnaryExpr]),m) = typeOf (UnaryExpr,m)

|   typeOf (itree(inode("UnaryExpr",_),[itree(inode("!",_),[]),UnaryExpr]),m) =
    let
        val t1 = typeOf (UnaryExpr,m)
    in 
        if t1 = BOOL
        then BOOL
        else ERROR
    end
    
|   typeOf (itree(inode("UnaryExpr",_),[itree(inode("-",_),[]),ExpExpr]),m) =
    let
        val t1 = typeOf (ExpExpr,m)
    in 
        if t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("UnaryExpr",_),[ExpExpr]),m) = typeOf (ExpExpr,m)
    
|   typeOf (itree(inode("ExpExpr",_),[BaseExpr,itree(inode("^",_),[]),ExpExpr]),m) =
    let
        val t1 = typeOf (BaseExpr,m)
        val t2 = typeOf (ExpExpr,m)
    in 
        if t1 = t2 andalso t1 = INT
        then INT
        else ERROR
    end
    
|   typeOf (itree(inode("ExpExpr",_),[BaseExpr]),m) = typeOf (BaseExpr,m)

|   typeOf (itree(inode("BaseExpr",_),[Increment]),m) = typeOf (Increment,m)

|   typeOf (itree(inode("BaseExpr",_),[itree(inode("(",_),[]),Expr,itree(inode(")",_),[])]),m) = typeOf (Expr,m)

|   typeOf (itree(inode("BaseExpr",_),[itree(inode("|",_),[]),Expr,itree(inode("|",_),[])]),m) = 
    let
        val t = typeOf (Expr,m)
    in
        if t = INT
        then INT
        else ERROR
    end

|   typeOf (itree(inode("BaseExpr",_),[id]),m) = typeOf (id,m)

|   typeOf (itree(inode("BaseExpr",_),[integer]),m) = typeOf (integer,m)

|   typeOf (itree(inode("BaseExpr",_),[bool]),m) = typeOf (bool,m)

|   typeOf (itree(inode("id",_),[node_id]),m) = getType(accessEnv(getLeaf(node_id),m))

|   typeOf (itree(inode("integer",_),[integerNum]),m) = INT

|   typeOf (itree(inode("bool",_),[boolVal]),m) = BOOL

|   typeCheck (itree(inode(x_root,_),children),_) = raise General.Fail ("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")

|   typeCheck _ = raise Fail ("Error in Model.typeCheck - this should never occur")

    

fun typeCheck (itree(inode("Program",_),[StatementList]),m) = typeCheck (StatementList,m)

|   typeCheck (itree(inode("StatementList",_),[Statement, StatementList]),m0) =
    let
        val m1 = typeCheck (Statement,m0)
        val m2 = typeCheck (StatementList,m1)
    in
        m2
    end
    
|   typeCheck (itree(inode("StatementList",_),[epsilon]),m) = typeCheck (epsilon,m)

|   typeCheck (itree(inode("epsilon",_),[]),m) = m

|   typeCheck (itree(inode("Statement",_),[stmt1,itree(inode(";",_),[])]),m0) =
    let
        val m1 = typeCheck (stmt1,m0)
    in
        m1
    end
    
|   typeCheck (itree(inode("Statement",_),[stmt2]),m0) =
    let
        val m1 = typeCheck (stmt2,m0)
    in
        m1
    end
   
|   typeCheck (itree(inode("Declaration",_),[itree(inode("INT",_),[]),node_id]),m0) =
    let
        val id = getLeaf(node_id)
        val (_,n,_) = m
    in
        updateEnv(id,INT,n,m)
    end
    
|   typeCheck (itree(inode("Declaration",_),[itree(inode("BOOL",_),[]),node_id]),m0) =
    let
        val id = getLeaf(node_id)
        val (_,n,_) = m
    in
        updateEnv(id,BOOL,n,m)
    end

|   typeCheck (itree(inode("Declaration",_),[AssignDec]),m) = typeCheck (AssignDec,m)

|   typeCheck (itree(inode("AssignDec",_),[itree(inode("INT",_),[]),node_id,itree(inode("=",_),[]),AddSubExpr]),m0) =
    let
        val id = getLeaf(node_id)
        val (_,n,_) = m0
        val t = typeOf(AddSubExpr,m0)
        val m1 = updateEnv(id,INT,n,m0)
    in
        if t = INT
        then m1
        else raise model_error
    end
    
|   typeCheck (itree(inode("AssignDec",_),[itree(inode("BOOL",_),[]),node_id,itree(inode("=",_),[]),Expr]),m0) =
    let
        val id = getLeaf(node_id)
        val (_,n,_) = m0
        val t = typeOf(Expr,m0)
        val m1 = updateEnv(id,BOOL,n,m0)
    in
        if t = BOOL
        then m1
        else raise model_error
    end
    
|   typeCheck (itree(inode("Assignment",_),[node_id,itree(inode("=",_),[]),Expr]),m) =
    let
        val id = getLeaf(node_id)
        val t1 = getType(accessEnv(id,m))
        val t2 = typeOf(Expr,m)
    in
        if t1 = t2 andalso t1 <> ERROR
        then m
        else raise model_error
    end
    
|   typeCheck (itree(inode("Assignment",_),[Increment]),m) = 
    let
        val t = typeOf (Increment,m)
    in
        if t = ERROR 
        then raise model_error
        else m
    end
    
|   typeCheck (itree(inode("PrintSt",_),[itree(inode("print",_),[]),itree(inode("(",_),[]),Expr,itree(inode(")",_),[])]),m) =
    let
        val t = typeOf (Expr,m)
    in
        if t = ERROR
        then raise model_error
        else m
    end
    
|   typeCheck (itree(inode("Block",_),[itree(inode("{",_),[]),StatementList,itree(inode("}",_),[])]),m0) = 
    let
        val m1 = typeCheck (StatementList,m0)
    in
        m1
    end
    
|   typeCheck (itree(inode("CondStatement",_),[itree(inode("if",_),[]),itree(inode("(",_),[]),Expr,itree(inode(")",_),[]),Block]),m0) = 
    let
        val t = typeOf (Expr,m0)
        val m1 = typeCheck (Block, m0)
    in
        if t = BOOL
        then m0
        else raise model_error
    end

|   typeCheck (itree(inode("CondStatement",_),
        [
            itree(inode("if",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[]),
            Block1,
            itree(inode("else",_),[]),
            Block2
        ]),m0) = 
    let
        val t = typeOf (Expr,m0)
        val m1 = typeCheck (Block1, m0)
        val m2 = typeCheck (Block2, m0)
    in
        if t = BOOL
        then m0
        else raise model_error
    end
    
|   typeCheck (itree(inode("WhileLoop",_),
        [
            itree(inode("while",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[]),
            Block
        ]),m0) = 
    let
        val t = typeOf (Expr,m0)
        val m1 = typeCheck (Block,m0)
    in
        if t = BOOL
        then m0
        else raise model_error
    end
    
|   typeCheck (itree(inode("ForLoop",_),
        [
            itree(inode("for",_),[]),
            itree(inode("(",_),[]),
            AssignDec,
            itree(inode(";",_),[]),
            Expr,
            itree(inode(";",_),[]),
            Increment
            itree(inode(")",_),[]),
            Block
        ]),m0) = 
    let
        val m1 = typeCheck (AssignDec,m0)
        val t = typeOf (Expr,m1)
        val m2 = typeCheck (Block,m1)
        val m3 = typeCheck (Increment,m2)
    in
        if t = BOOL
        then m0
        else raise model_error
    end

|   typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")

|   typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








