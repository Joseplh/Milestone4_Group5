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

fun E(itree(inode("Increment",_), 
                [ 
                    itree(inode("++",_),[]),
                    Variable0
                ] 
             ), 
        m0
    ) = 
    let
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m0))
        val v0 = accessStore(l0, m0)
        val v1 = add(v0, Integer 1)
        val m1 = updateStore(l0, Integer v1, m0)
    in
        (Integer v1, m1)
    end
    
 |  E(itree(inode("Increment",_), 
                [ 
                    itree(inode("--",_),[]),
                    Variable0
                ] 
             ), 
        m0
    ) = 
    let
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m0))
        val v0 = accessStore(l0, m0)
        val v1 = add(v0, Integer (~1))
        val m1 = updateStore(l0, Integer v1, m0)
    in
        (Integer v1, m1)
    end
    
 |  E(itree(inode("Increment",_), 
                [ 
                    Variable0,
                    itree(inode("++",_),[])
                ] 
             ), 
        m0
    ) = 
    let
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m0))
        val v0 = accessStore(l0, m0)
        val v1 = add(v0, Integer 1)
        val m1 = updateStore(l0, Integer v1, m0)
    in
        (v0, m1)
    end    
    
 |  E(itree(inode("Increment",_), 
                [ 
                    Variable0,
                    itree(inode("--",_),[])
                ] 
             ), 
        m0
    ) = 
    let
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m0))
        val v0 = accessStore(l0, m0)
        val v1 = add(v0, Integer (~1))
        val m1 = updateStore(l0, Integer v1, m0)
    in
        (v0, m1)
    end 

 |  E(itree(inode("Expression",_), 
                [ 
                    ExprOr0
                ] 
             ), 
        m0
    ) = E(ExprOr0, m0)

 |  E(itree(inode("ExprOr",_), 
                [ 
                    ExprOr0,
                    itree(inode("or",_), []),
                    ExprAnd0
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(ExprOr0, m0)
    in
        if toBool(v0)
        then (Boolean(toBool(v0)), m1)
        else
            let
                val (v1, m2) = E(ExprAnd0, m1)
            in
                (Boolean(toBool(v1)), m2)
            end
    end

 |  E(itree(inode("ExprOr",_), 
                [ 
                    ExprAnd0
                ] 
             ), 
        m0
    ) = E(ExprAnd0, m0)

 |  E(itree(inode("ExprAnd",_), 
                [ 
                    ExprAnd0,
                    itree(inode("and",_), []),
                    ExprBoolComp0
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(ExprAnd0, m0)
    in
        if toBool(v0)
        then
            let
                val (v1, m2) = E(ExprBoolComp0, m1)
            in
                (Boolean(toBool(v1)), m2)
            end
        else (Boolean(toBool(v0)), m1)
    end

 |  E(itree(inode("ExprAnd",_), 
                [ 
                    ExprBoolComp0
                ] 
             ), 
        m0
    ) = E(ExprBoolComp0, m0)   

 |  E(itree(inode("ExprBoolComp",_), 
                [ 
                    ExprBoolComp0,
                    itree(inode("==",_), []),
                    ExprIntComp0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprBoolComp0, m0)
        val (v1, m2) = E(ExprIntComp0, m1)
    in
        (Boolean(v0 = v1), m2)
    end

 |  E(itree(inode("ExprBoolComp",_), 
                [ 
                    ExprBoolComp0,
                    itree(inode("!=",_), []),
                    ExprIntComp0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprBoolComp0, m0)
        val (v1, m2) = E(ExprIntComp0, m1)
    in
        (Boolean(v0 <> v1), m2)
    end

 |  E(itree(inode("ExprBoolComp",_), 
                [ 
                    ExprIntComp0
                ] 
             ), 
        m0
    ) = E(ExprIntComp0, m0)  

 |  E(itree(inode("ExprIntComp",_), 
                [ 
                    ExprIntComp0,
                    itree(inode("<",_), []),
                    ExprAddSub0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprIntComp0, m0)
        val (v1, m2) = E(ExprAddSub0, m1)
    in
        (Boolean(toInt(v0) < toInt(v1)), m2)
    end

 |  E(itree(inode("ExprIntComp",_), 
                [ 
                    ExprIntComp0,
                    itree(inode(">",_), []),
                    ExprAddSub0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprIntComp0, m0)
        val (v1, m2) = E(ExprAddSub0, m1)
    in
        (Boolean(toInt(v0) > toInt(v1)), m2)
    end

 |  E(itree(inode("ExprIntComp",_), 
                [ 
                    ExprAddSub0
                ] 
             ), 
        m0
    ) = E(ExprAddSub0, m0)  

 |  E(itree(inode("ExprAddSub",_), 
                [ 
                    ExprAddSub0,
                    itree(inode("+",_), []),
                    ExprMulDivMod0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprAddSub0, m0)
        val (v1, m2) = E(ExprMulDivMod0, m1)
        val v2 = Integer(toInt(v0) + toInt(v1))
    in
        (v2, m2)
    end

 |  E(itree(inode("ExprAddSub",_), 
                [ 
                    ExprAddSub0,
                    itree(inode("-",_), []),
                    ExprMulDivMod0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprAddSub0, m0)
        val (v1, m2) = E(ExprMulDivMod0, m1)
        val v2 = Integer(toInt(v0) - toInt(v1))
    in
        (v2, m2)
    end
 
 |  E(itree(inode("ExprAddSub",_), 
                [ 
                    ExprMulDivMod0
                ] 
             ), 
        m0
    ) = E(ExprMulDivMod0, m0)  

 |  E(itree(inode("ExprMulDivMod",_), 
                [ 
                    ExprMulDivMod0,
                    itree(inode("*",_), []),
                    ExprNeg0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprMulDivMod0, m0)
        val (v1, m2) = E(ExprNeg0, m1)
        val v2 = Integer(toInt(v0) * toInt(v1))
    in
        (v2, m2)
    end

 |  E(itree(inode("ExprMulDivMod",_), 
                [ 
                    ExprMulDivMod0,
                    itree(inode("/",_), []),
                    ExprNeg0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprMulDivMod0, m0)
        val (v1, m2) = E(ExprNeg0, m1)
        val v2 = Integer(toInt(v0) div toInt(v1))
    in
        (v2, m2)
    end

 |  E(itree(inode("ExprMulDivMod",_), 
                [ 
                    ExprMulDivMod0,
                    itree(inode("MOD",_), []),
                    ExprNeg0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprMulDivMod0, m0)
        val (v1, m2) = E(ExprNeg0, m1)
        val v2 = Integer(toInt(v0) mod toInt(v1))
    in
        (v2, m2)
    end

 |  E(itree(inode("ExprMulDivMod",_), 
                [ 
                    ExprNeg0
                ] 
             ), 
        m0
    ) = E(ExprNeg0, m0)  

 |  E(itree(inode("ExprNeg",_), 
                [ 
                    itree(inode("~",_), []),
                    ExprNeg0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprNeg0, m0)
        val v1 = toInt(v0)
        val v2 = Integer(~v1)
    in
        (v2, m1)
    end

 |  E(itree(inode("ExprNeg",_), 
                [ 
                    itree(inode("not",_), []),
                    ExprNeg0
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(ExprNeg0, m0)
        val v1 = toBool(v0)
        val v2 = Boolean(not v1)
    in
        (v2, m1)
    end

 |  E(itree(inode("ExprNeg",_), 
                [ 
                    ExprExpr0
                ] 
             ), 
        m0
    ) = E(ExprExpr0, m0)  

 |  E(itree(inode("ExprExp",_), 
                [ 
                    ExprBase0,
                    itree(inode("^",_), []),
                    ExprExp0
                ] 
             ), 
        m0
    ) =
    let
            fun power(a, b) = 
                let
                    fun aux(x, i) =
                        if i = b 
                        then x
                        else aux(x * a, i + 1)
                in
                    aux(1, 0)
                end
                
            val (v0, m1) = E(ExprExp0, m0)
            val (v1, m2) = E(ExprBase0, m1)
            val v2 = Integer(power(toInt(v0), toInt(v1)))
        in
            (v2, m2)
        end

 |  E(itree(inode("ExprExp",_), 
                [ 
                    ExprBase0
                ] 
             ), 
        m0
    ) = E(ExprBase0, m0)        

 |  E(itree(inode("ExprBase",_), 
                [ 
                    Integer0 as itree(inode("Integer",_), children)
                ] 
             ), 
        m0
    ) = 
    let
        fun getInt(input) = 
            valOf(Int.fromString input);
        val v0 = getInt(getLeaf(Integer0))
    in
        (Integer v0, m0)
    end

 |  E(itree(inode("ExprBase",_), 
                [ 
                    Boolean0 as itree(inode("true",_), children)
                ] 
             ), 
        m0
    ) = 
    let
        fun getBool(input) = 
            valOf(Bool.fromString input);
        val v0 = getBool(getLeaf(Boolean0))
    in
        (Boolean v0, m0)
    end

 |  E(itree(inode("ExprBase",_), 
                [ 
                    Boolean0 as itree(inode("false",_), children)
                ] 
             ), 
        m0
    ) = 
    let
        fun getBool(input) = 
            valOf(Bool.fromString input);
        val v0 = getBool(getLeaf(Boolean0))
    in
        (Boolean v0, m0)
    end

 |  E(itree(inode("ExprBase",_), 
                [ 
                    Variable0 as itree(inode("Variable",_), children)
                ] 
             ), 
        m0
    ) = 
    let
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m0))
        val v0 = accessStore(l0, m0)
    in
        (v0, m0)
    end

 |  E(itree(inode("ExprBase",_), 
                [ 
                    itree(inode("(",_), []),
                    Expression0,
                    itree(inode(")",_), [])
                ] 
             ), 
        m0
    ) = E(Expression0, m0)

 |  E(itree(inode("ExprBase",_), 
                [ 
                    itree(inode("|",_), []),
                    Expression0,
                    itree(inode("|",_), [])
                ] 
             ), 
        m0
    ) =
    let
        val (v0, m1) = E(Expression0, m0)
        val v1 = toInt(v0)
        
        fun aux (x) =
            if x < 0 
            then Integer(x * (~1))
            else Integer(x)
    in
        (aux(v1), m1)
    end

 |  E(itree(inode("ExprBase",_), 
                [ 
                    Increment0
                ] 
             ), 
        m0
    ) = E(Increment0, m0) 

 |  E(itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
 |  E _ = raise Fail("error in Semantics.E - this should never occur")

(*
<Assignment>        ::= "INTEGER" Variable "=" <Expression>
                      | "BOOLEAN" Variable "=" <Expression>                                 .
<Conditional>       ::= "if" "(" <Expression> ")" <Block> 
                      | "if" "(" <Expression> ")" <Block> "else" <Block>                    .
<WhileLoop>         ::= "while" "(" <Expression> ")" <Block>                                .
<ForLoop>           ::= "for" "(" <Assignment> ";" <Expression> ";" <Increment> ")" <Block>  .
<Print>             ::= "print" "(" <Expression> ")"                                        .
<Block>             ::= "{" <StatementList> "}"                                             .                                               .                                                  .                                                   .
*) 



fun M(itree(inode("prog",_), 
                [ 
                    StatementList0
                ] 
             ), 
        m0
    ) = M(StatementList0, m0)
    
 |  M(itree(inode("StatementList",_), 
                [ 
                    Statement0,
                    itree(inode(";",_),[]),
                    StatementList0
                ] 
             ), 
        m0
    ) = 
    let
        val m1 = M(Statement0, m0)
        val m2 = M(StatementList0, m1)
    in
        m2
    end
    
 |  M(itree(inode("StatementList",_), 
                [ 
                    Epsilon
                ] 
             ), 
        m0
    ) = m0
    
 |  M(itree(inode("Statement",_), 
                [ 
                    Declaration0 as itree(inode("Declaration",_), children)
                ] 
             ), 
        m0
    ) = M(Declaration0, m0)    
    
 |  M(itree(inode("Statement",_), 
                [ 
                    Assignment0 as itree(inode("Assignment",_), children)
                ] 
             ), 
        m0
    ) = M(Assignment0, m0)       
 
 |  M(itree(inode("Statement",_), 
                [ 
                    Conditional0 as itree(inode("Conditional",_), children)
                ] 
             ), 
        m0
    ) = M(Conditional0, m0)    
    
 |  M(itree(inode("Statement",_), 
                [ 
                    Increment0 as itree(inode("Increment",_), children)
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(Increment0, m0)    
    in
        m1
    end
    
 |  M(itree(inode("Statement",_), 
                [ 
                    Print0 as itree(inode("Print",_), children)
                ] 
             ), 
        m0
    ) = M(Print0, m0)    
    
 |  M(itree(inode("Statement",_), 
                [ 
                    Block0 as itree(inode("Block",_), children)
                ] 
             ), 
        m0
    ) = M(Block0, m0)    
    
 |  M(itree(inode("Statement",_), 
                [ 
                    ForLoop0 as itree(inode("ForLoop",_), children)
                ] 
             ), 
        m0
    ) = M(ForLoop0, m0)    
    
  |  M(itree(inode("Statement",_), 
                [ 
                    WhileLoop0 as itree(inode("WhileLoop",_), children)
                ] 
             ), 
        m0
    ) = M(WhileLoop0, m0)   
    
 |  M(itree(inode("Declaration",_), 
                [ 
                    itree(inode("INTEGER",_), []),
                    Variable0
                ] 
             ), 
        m0
    ) = updateEnv(getLeaf(Variable0), INT, m0) 
    
 |  M(itree(inode("Declaration",_), 
                [ 
                    itree(inode("BOOLEAN",_), []),
                    Variable0
                ] 
             ), 
        m0
    ) = updateEnv(getLeaf(Variable0), BOOL, m0)     

 |  M(itree(inode("Assignment",_), 
                [ 
                    Variable0,
                    itree(inode("=",_), []),
                    Expression0
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(Expression0, m0)
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m1))
        val m2 = updateStore(l0, v0, m1)
    in
        m2
    end
    
 |  M(itree(inode("Assignment",_), 
                [ 
                    itree(inode("INTEGER",_), []),
                    Variable0,
                    itree(inode("=",_), []),
                    Expression0
                ] 
             ), 
        m0
    ) = 
    let
        val m1 = updateEnv(getLeaf(Variable0), INT, m0)
        val (v0, m2) = E(Expression0, m1)
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m2))
        val m3 = updateStore(l0, v0, m2)
    in
        m3
    end

 |  M(itree(inode("Assignment",_), 
                [ 
                    itree(inode("BOOLEAN",_), []),
                    Variable0,
                    itree(inode("=",_), []),
                    Expression0
                ] 
             ), 
        m0
    ) = 
    let
        val m1 = updateEnv(getLeaf(Variable0), BOOL, m0)
        val (v0, m2) = E(Expression0, m1)
        val l0 = getLoc(accessEnv(getLeaf(Variable0), m2))
        val m3 = updateStore(l0, v0, m2)
    in
        m3
    end

 |  M(  itree(inode("Conditional",_), 
                [ 
                    itree(inode("if",_),[]),
                    itree(inode("(",_),[]),
                    Expression0,
                    itree(inode(")",_),[]),
                    Block0
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(Expression0, m0)
    in
        if toBool(v0)
        then M(Block0, m1)
        else m1
    end

 |  M(  itree(inode("Conditional",_), 
                [ 
                    itree(inode("if",_),[]),
                    itree(inode("(",_),[]),
                    Expression0,
                    itree(inode(")",_),[]),
                    Block0,
                    itree(inode("else",_),[]),
                    Block1
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(Expression0, m0)
    in
        if toBool(v0)
        then M(Block0, m1)
        else M(Block1, m1)
    end
    
 |  M(  itree(inode("WhileLoop",_), 
                [ 
                    itree(inode("while",_),[]),
                    itree(inode("(",_),[]),
                    Expression0,
                    itree(inode(")",_),[]),
                    Block0
                ] 
             ), 
        m0
    ) =
    let
        fun aux(nm0) =
            let
                val (v0, nm1) = E(Expression0, nm0)
            in
                if toBool(v0)
                then aux(M(Block0, nm1))
                else nm1
            end
    in
        aux(m0)
    end

 |  M(  itree(inode("ForLoop",_), 
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
                ] 
             ), 
        m0
    ) =
    let
        val m1 = M(Assignment0, m0)
        val (v0, m2) = E(Expression0, m1)
        
        fun nloop(nm0) =
            let
                val nm1 = M(Block0, nm0)
                val (v1, nm2) = E(Increment0, nm1)
                val (v2, nm3) = E(Expression0, nm2)
            in
                if toBool(v2)
                then nloop(nm3)
                else nm3
            end
    in
        if toBool(v0)
        then nloop(m2)
        else m2
    end

 |  M(  itree(inode("Print",_), 
                [ 
                    itree(inode("print",_),[]),
                    itree(inode("(",_),[]),
                    Expression0,
                    itree(inode(")",_),[])
                ] 
             ), 
        m0
    ) = 
    let
        val (v0, m1) = E(Expression0, m0)
        val str = printFormat(v0)
        val v1 = print(str ^ "\n")
    in
        m1
    end

 |  M(  itree(inode("Block",_), 
                [ 
                    itree(inode("{",_),[]),
                    StatementList0,
                    itree(inode("}",_),[])
                ] 
             ), 
        m0
    ) = 
    let
        val (env0, n0, s0) = m0
        val (env1, n1, s1) = M(StatementList0, m0)
        val m2 = (env0, n0, s1)
    in
        m2
    end

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








