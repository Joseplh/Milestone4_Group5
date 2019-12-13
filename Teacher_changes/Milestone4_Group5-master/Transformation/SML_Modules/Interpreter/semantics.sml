(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun varToString (Boolean(x)) = Bool.toString x
|   varToString (Integer(x)) = Int.toString x;

fun pow(x, 0) = 1
|   pow(x, n) = x * pow(x, n-1);

fun E(itree(inode("Increment",_),
                    [
                        itree(inode("++",_),[]),
                        node_id
                    ]
           )
      ,
      m0 ) =
    let
        val id  = getLeaf(node_id)
        val loc = getLoc(accessEnv(id,m0))
        val v   = accessStore(loc,m0)
        val x   = Integer(toInt(v) + 1)
        val m1  = updateStore(loc, x, m0)
    in
        (x,m1)
    end
    
|   E(itree(inode("Increment",_),[itree(inode("--",_),[]),node_id]),m0) =
    let
        val id = getLeaf(node_id)
        val loc = getLoc(accessEnv(id,m0))
        val v = accessStore(loc,m0)
        val x = Integer(toInt(v) - 1)
        val m1 = updateStore(loc,x,m0)
    in
        (x,m1)
    end

|   E(itree(inode("Increment",_),[node_id,itree(inode("++",_),[])]),m0) =
    let
        val id = getLeaf(node_id)
        val loc = getLoc(accessEnv(id,m0))
        val v = accessStore(loc,m0)
        val x = Integer(toInt(v) + 1)
        val m1 = updateStore(loc,x,m0)
    in
        (v,m1)
    end

|   E(itree(inode("Increment",_),[node_id,itree(inode("--",_),[])]),m0) =
    let
        val id = getLeaf(node_id)
        val loc = getLoc(accessEnv(id,m0))
        val v = accessStore(loc,m0)
        val x = Integer(toInt(v) - 1)
        val m1 = updateStore(loc,x,m0)
    in
        (v,m1)
    end
    
|   E(itree(inode("Expr",_),[Expr,itree(inode("||",_),[]),AndExpr]),m0) =
    let
        val (v1,m1) = E(Expr,m0)
    in
        if v1 
        then (Boolean true, m1)
        else
            let
                val (v2,m2) = E(AndExpr, m1)
            in
                if v2
                then (Boolean true, m2)
                else (Boolean false, m2)
            end
    end
    
|   E(itree(inode("Expr",_),[AndExpr]),m0) = E(AndExpr,m0)

|   E(itree(inode("AndExpr",_),[AndExpr,itree(inode("&&",_),[]),EqualityExpr]),m0) =
    let
        val (v1,m1) = E(AndExpr,m0)
    in
        if v1 
        then 
            let
                val (v2, m2) = E(EqualityExpr,m1)
            in
                if v2
                then (Boolean true,m2)
                else (Boolean false,m2)
            end
        else (Boolean false, m1)
    end
    
|   E(itree(inode("AndExpr",_),[EqualityExpr]),m0) = E(EqualityExpr,m0)

|   E(itree(inode("EqualityExpr",_),[EqualityExpr,itree(inode("!=",_),[]),ComparisonExpr]),m0) =
    let
        val (v1,m1) = E(EqualityExpr,m0)
        val (v2,m2) = E(ComparisonExpr,m1)
    in
        if v1 = v2
        then (Boolean false, m2)
        else (Boolean true, m2)
    end
    
|   E(itree(inode("EqualityExpr",_),[EqualityExpr,itree(inode("==",_),[]),ComparisonExpr]),m0) =
    let
        val (v1,m1) = E(EqualityExpr,m0)
        val (v2,m2) = E(ComparisonExpr,m1)
    in
        if v1 = v2
        then (Boolean true, m2)
        else (Boolean false, m2)
    end
    
|   E(itree(inode("EqualityExpr",_),[ComparisonExpr]),m0) = E(ComparisonExpr,m0)

|   E(itree(inode("ComparisonExpr",_),[ComparisonExpr,itree(inode("<",_),[]),AddSubExpr]),m0) =
    let
        val (v1,m1) = E(ComparisonExpr,m0)
        val (v2,m2) = E(AddSubExpr,m1)
    in
        if v1 < v2
        then (Boolean true, m2)
        else (Boolean false, m2)
    end
    
|   E(itree(inode("ComparisonExpr",_),[ComparisonExpr,itree(inode(">",_),[]),AddSubExpr]),m0) =
    let
        val (v1,m1) = E(ComparisonExpr,m0)
        val (v2,m2) = E(AddSubExpr,m1)
    in
        if v1 > v2
        then (Boolean true, m2)
        else (Boolean false, m2)
    end
    
|   E(itree(inode("ComparisonExpr",_),[AddSubExpr]),m0) = E(AddSubExpr,m0)

|   E(itree(inode("AddSubExpr",_),[AddSubExpr,itree(inode("+",_),[]),MultDivModExpr]),m0) =
    let
        val (v1,m1) = E(AddSubExpr,m0)
        val (v2,m2) = E(MultDivModExpr,m1)
        val v3 = v1 + v2
    in
        (v3,m2)
    end
    
|   E(itree(inode("AddSubExpr",_),[AddSubExpr,itree(inode("-",_),[]),MultDivModExpr]),m0) =
    let
        val (v1,m1) = E(AddSubExpr,m0)
        val (v2,m2) = E(MultDivModExpr,m1)
        val v3 = v1 - v2
    in
        (v3,m2)
    end
    
|   E(itree(inode("AddSubExpr",_),[MultDivModExpr]),m0) = E(MultDivModExpr,m0)

|   E(itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("*",_),[]),UnaryExpr]),m0) =
    let
        val (v1,m1) = E(MultDivModExpr,m0)
        val (v2,m2) = E(UnaryExpr,m1)
        val v3 = v1 * v2
    in
        (v3,m2)
    end
    
|   E(itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("DIV",_),[]),UnaryExpr]),m0) =
    let
        val (v1,m1) = E(MultDivModExpr,m0)
        val (v2,m2) = E(UnaryExpr,m1)
        val v3 = v1 div v2
    in
        (v3,m2)
    end
    
|   E(itree(inode("MultDivModExpr",_),[MultDivModExpr,itree(inode("MOD",_),[]),UnaryExpr]),m0) =
    let
        val (v1,m1) = E(MultDivModExpr,m0)
        val (v2,m2) = E(UnaryExpr,m1)
        val v3 = v1 mod v2
    in
        (v3,m2)
    end
    
|   E(itree(inode("MultDivModExpr",_),[UnaryExpr]),m0) = E(UnaryExpr,m0)

|   E(itree(inode("UnaryExpr",_),[itree(inode("!",_),[]),UnaryExpr]),m0) =
    let
        val (v1,m1) = E(UnaryExpr, m0)
    in
        (Boolean(not(v1)),m1)
    end
    
|   E(itree(inode("UnaryExpr",_),[itree(inode("-",_),[]),ExpExpr]),m0) =
    let
        val (v1,m1) = E(ExpExpr, m0)
    in
        (Integer(~(toInt(v1))), m1)
    end
    
|   E(itree(inode("UnaryExpr",_),[ExpExpr]),m0) = E(ExpExpr, m0)

|   E(itree(inode("ExpExpr",_),[BaseExpr,itree(inode("^",_),[]),ExpExpr]),m0) =
    let
        val (v1,m1) = E(BaseExpr,m0)
        val (v2,m2) = E(ExpExpr, m1)
        val v3 = Integer( pow(toInt v1, toInt v2) )
    in
        (v3,m2)
    end
    
|   E(itree(inode("ExpExpr",_),[BaseExpr]),m0) = E(BaseExpr,m0)

|   E(itree(inode("BaseExpr",_),[itree(inode("(",_),[]),Expr,itree(inode(")",_),[])]),m0) = E(Expr,m0)

|   E(itree(inode("BaseExpr",_),[itree(inode("|",_),[]),Expr,itree(inode("|",_),[])]),m0) = 
    let
        val (v1,m1) = E(Expr,m0)
    in
        (Integer(Int.abs(toInt(v1))), m1)
    end

|   E(itree(inode("BaseExpr",_),[singleChild]),m0) = E(singleChild,m0)  

    (*VW
|   E(itree(inode("BaseExpr",_),[Increment]),m0) = E(Increment,m0)    
|   E(itree(inode("BaseExpr",_),[id]),m0) = E(id,m0)

|   E(itree(inode("BaseExpr",_),[integer]),m0) = E(integer,m0)

|   E(itree(inode("BaseExpr",_),[bool]),m0) = E(bool,m0) 
    *)

|   E(itree(inode("id",_),[node_id]),m) =
    let
        val id  = getLeaf(node_id)
        val loc = getLoc(accessEnv(id,m))
        val v   = accessStore(loc,m)
    in
        (v,m)
    end
    
|   E(itree(inode("bool",_),[boolVal]),m) = 
    let
        val v = getLeaf(boolVal)
        val x = valOf(Bool.fromString(v))
    in
        (Boolean x, m)
    end
    
|   E(itree(inode("integer",_),[integerNum]),m) = 
    let
        val v = getLeaf(integerNum)
        val x = valOf(Int.fromString(v))
    in
        (Integer x, m)
    end
    
|   E(itree(inode(x_root,_),children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
|   E _ = raise Fail("error in Semantics.E - this should never occur")


fun M(itree(inode("Program",_),[stmt_list]),m) = M(StatementList,m)

|   M(itree(inode("StatementList",_),[Statement,StatementList]),m0) =
    let
        val m1 = M(Statement, m0)
        val m2 = M(StatementList, m2)
    in
        m2
    end
    
|   M(itree(inode("StatementList",_),[epsilon]),m) = m

|   M(itree(inode("Statement",_),[stmt,itree(inode(";",_),[])]),m) = M(stmt,m)

|   M(itree(inode("Statement",_),[stmt]),m) = M(stmt,m)

|   M(itree(inode("Declaration",_),[itree(inode("INT",_),[]),node_id]),(env,n,s)) =
    let
        val id = getLeaf(node_id)
    in
        updateEnv(id,INT,n,(env,n,s))
    end
    
|   M(itree(inode("Declaration",_),[itree(inode("BOOL",_),[]),node_id]),(env,n,s)) =
    let
        val id = getLeaf(node_id)
    in
        updateEnv(id,BOOL,n,(env,n,s))
    end
    
|   M(itree(inode("Declaration",_),[AssignDec]),m) = M(AssignDec,m)

|   M(itree(inode("AssignDec",_),
        [
            itree(inode("INT",_),[]),
            node_id,
            itree(inode("=",_),[]),
            AddSubExpr
        ]),m0) =
    let
        val id = getLeaf(node_id)
        val (v, m1) = E(AddSubExpr,m0)
        val (_,n,_) = m1
        val m2 = updateEnv(id,INT,n,m1)
        val loc = getLoc(accessEnv(id,m2))
        val m3 = updateStore(loc,v,m2)
    in
        m3
    end
    
|   M(itree(inode("AssignDec",_),
        [
            itree(inode("BOOL",_),[]),
            node_id,
            itree(inode("=",_),[]),
            Expr
        ]),m0) =
    let
        val id = getLeaf(node_id)
        val (v,m1) = E(Expr,m0)
        val (_,n,_) = m1
        val m2 = updateEnv(id,BOOL,n,m1)
        val loc = getLoc(accessEnv(id,m2))
        val m3 = updateStore(loc,v,m2)
    in
        m3
    end
    
|   M(itree(inode("Assignment",_),[node_id,itree(inode("=",_),[]),Expr]),m0) =
    let
        val id = getLeaf(node_id)
        val (v,m1) = E(Expr,m0)
        val loc = getLoc(accessEnv(id,m1))
        val m2 = updateStore(loc,v,m1)
    in
        m2
    end
    
|   M(itree(inode("Assignment",_),[Increment]),m0) = 
    let
        val (_,m1) = E(Increment, m0)
    in
        m1
    end

|   M(itree(inode("PrintSt",_),
        [
            itree(inode("print",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[])
        ]),m0) =
    let
        val (v,m1) = E(Expr,m0)
        val str = varToString(v)
    in
        (print(str^"\n"); m1)
    end
    
|   M(itree(inode("Block",_),[itree(inode("{",_),[]),StatementList,itree(inode("}",_),[])]),(env0,n0,s0)) =
    let
        val(_,n1,s1) = M(StatementList,(env0,n0,s0))
        val m = (env0,n1,s1)
    in
        m
    end
    
|   M(itree(inode("CondStatement",_),
        [
            itree(inode("if",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[]),
            Block
        ]),m0) =
    let
        val (v,m1) = E(Expr,m0)
    in
        if v 
        then M(Block,m1)
        else m1
    end
    
|   M(itree(inode("CondStatement",_),
        [
            itree(inode("if",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[]),
            Block1
            itree(inode("else",_),[]),
            Block2
        ]),m0) =
    let
        val (v,m1) = E(Expr,m0)
    in
        if v 
        then M(Block1,m1)
        else M(Block2,m1)
    end
    
|   M(itree(inode("WhileLoop",_),
        [
            itree(inode("while",_),[]),
            itree(inode("(",_),[]),
            Expr,
            itree(inode(")",_),[]),
            Block
        ]),m0) =
    let
        fun aux(m1) =
            let
                val (v,m2) = E(Expr,m1)
            in
                if v
                then
                    let
                        val m3 = M(Block,m2)
                        val m4 = aux(m3)
                    in
                        m4
                    end
                else m2
            end
    in
        aux(m0)
    end
    
|   M(itree(inode("ForLoop",_),
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
        val m1 = M(AssignDec,m0)
        
        fun aux(m2) =
            let
                val (v,m3) = E(Expr,m2)
            in
                if v
                then 
                    let
                        val m4 = M(Block,m3)
                        val m5 = M(Increment, m4)
                        val m6 = aux(m5)
                    in
                        m6
                    end
                else m3
            end
    in
        aux(m1)
    end
     
|   M(itree(inode(x_root,_),children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
|   M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








