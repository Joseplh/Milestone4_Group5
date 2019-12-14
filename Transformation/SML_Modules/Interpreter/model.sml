(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )


exception runtime_error;

fun error msg = (print msg; raise runtime_error);


fun toInt(Integer x) = x
  | toInt _ = error "Error in toInt";

fun toBool(Boolean true) = true
  | toBool(Boolean false) = false
  | toBool _ = error "Error in toBool";

fun printFormat(Integer x) = Int.toString(x)
  | printFormat(Boolean x) = Bool.toString(x);

fun add (Integer x, Integer y) = x + y
    | add _ = error "Error in add";

fun getLoc(t, loc) = loc;

fun getType(t, loc) = t;

fun accessEnv(id1,(env, next, s))=
    let           
        val msg = "Cannot access Environment => Variable : " ^ id1;
        fun aux [] = error msg
          | aux ((id2,t,loc)::env1) =
                if id1 = id2
                then (t, loc)
                else aux env1          
    in 
        aux env
    end;

fun accessStore(loc, (env, next ,s)) =
    let
        val msg = "Cannot Access Store => Location : " ^ Int.toString(loc);
        fun aux [] = error msg
          | aux ((loc1,dv1)::s) = 
                if loc1 = loc 
                then dv1 
                else aux s;
    in 
        aux s 
    end;
    
fun updateStore(loc, dv:denotable_value, (env, next, s))=
    let 
        fun aux [] = [(loc, dv)]
            | aux ((loc1, dv1)::s)=
                if loc1 = loc then (loc,dv)::s
                else (loc1, dv1)::aux s;
    in
        (env, next, aux s)
    end;
    
fun updateEnv(id0, t, (env, next, s))=
    let
        val msg = "Cannot update Environment => Variable : " ^ id0;
        fun aux [] = [(id0,t,next)]
          | aux ((id1,t1,loc1)::env) =
                if id1 = id0 
                then error msg
                else (id1,t1,loc1)::aux env;
    in
        (aux env, next+1, s)
    end;

(*-------------------------------------------*)
fun typeToString BOOL  = "bool"
  | typeToString INT   = "integer"
  | typeToString ERROR = "error";

fun envEntryToString (id,t,loc) = 
       "(" ^ id ^ "," ^ typeToString t ^ "," ^ Int.toString loc ^ ")"; 

fun showEnv [] = print "\n"
  | showEnv (entry::env) = ( 
                             print("\n" ^ envEntryToString entry);
                             showEnv env
                           );

fun varToString (Boolean(x)) = Bool.toString x
  | varToString (Integer(x)) = Int.toString x;

fun storeEntryToString (loc, v) = 
       "(" ^ Int.toString loc ^ "," ^ varToString v ^ ")"; 

fun showStore [] = print "\n"
  | showStore (entry::store) = ( 
                             print("\n" ^ storeEntryToString entry);
                             showStore store
                           );

fun showProgState (env,n,s) =   
    (
    print("ENVIRONMENT");
    showEnv env;
    
    print("\n");
    print("COUNTER\n");
    print(Int.toString n ^ "\n");
    
    print("\n");
    print("STORE");
    showStore s
 );
(*-------------------------------------------*)

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)












