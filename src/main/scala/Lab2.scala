//The directory switch worked
object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Samuel Volin>
   * 
   * Partner: <Cris Salazar>
   * Collaborators: <Alex Tsankov, Roger Klotz>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */
  //credit: http://stackoverflow.com/questions/9938098/
  def isAllDigits(x: String) = x forall Character.isDigit
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) return 1 else return 0 
      case S(s) => if (isAllDigits(s)) return s.toDouble else return Double.NaN
      case Undefined => return Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if (n.isNaN()) return false else return (n != 0) 
      case S(s) => if (s == "") return false else return true
      case Undefined => return false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString//if(n%1 ==0) return n.toInt.toString else return n.toString
      case B(b) => if(b) return "true" else return ""
      case Undefined => "undefined"
      //case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    		//println(env)
    e match {
      /* Base Cases */
      case N(n) => return e; //eval should return the expression if it is a terminal
      case B(b) => return e;
      case S(s) => return e; 
      case Undefined => return e ;
      /* Inductive Cases */
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Var(x) =>{ 
        get(env, x)
      }
      case ConstDecl(x, en, ed) =>{
         val envp = extend(env, x, eval(en))   
         //println("set" + envp.toString)
         return eval(envp, ed) 
        }
      case If(cond, t, f) => if(toBoolean(cond)) return eval(env, t) else return eval(env, f)
      case Unary(op, en) => op match
      {
        case Neg => return N(-1 * toNumber(eval(env, en))) //unary make negative
        case Not => return B(!toBoolean(eval(env, en)))
        case _ => throw new UnsupportedOperationException
      }
      case Binary(op, en, ed) => op match
      {

        case Plus => eval(env, en) match{//plus works on number and string types. If either type is a string, it concatenates one expresiion with the other
        //if the first argument is boolean, cast it as an integer, and try again  
        case B(a) => return eval(env, Binary(Plus, N(toNumber(en)), ed))
        //if its a number, 
        case N(a)=> eval(env, ed) match{
        	  //if the second argument is a number, recurse as well
        	case B(b) => return eval(env, Binary(Plus, en, N(toNumber(ed))))
            case N(b) => return N(a+b)
            case _=> return S(toStr(eval(env, en)).concat(toStr(eval(env, ed))))
          }
          case _=> return S(toStr(eval(env, en)).concat(toStr(eval(env, ed))))
          
        }

        //case Plus => return N(toNumber(eval(en)) + toNumber(eval(ed)))
        case Minus => return N(toNumber(eval(env, en)) - toNumber(eval(env, ed)))
        case Times => return N(toNumber(eval(env, en)) * toNumber(eval(env, ed)))
        case Div => { //binary divide
        	if (toNumber(eval(env, ed)) == 0) { //checks if we are dealing with a zero
        		if (toNumber(eval(env, en)) > 0) //if the numerator is greater than zero, return positive
        			return N(Double.PositiveInfinity)
        		else return N(Double.NegativeInfinity) //otherwise return neg infinity
        	} else return N(toNumber(eval(env, en)) / toNumber(eval(env, ed))) //otherwise return the actual division
        }
        case Eq => return B(toNumber(eval(env, en)) == toNumber(eval(env, ed))) //fix
        case Ne => return B(toNumber(eval(env, en)) != toNumber(eval(env, ed))) //fix
        case Lt => return B(toNumber(eval(env, en)) < toNumber(eval(env, ed)))
        case Le => return B(toNumber(eval(env, en)) <= toNumber(eval(env, ed)))
        case Gt => return B(toNumber(eval(env, en)) > toNumber(eval(env, ed)))
        case Ge => return B(toNumber(eval(env, en)) >= toNumber(eval(env, ed)))
        //case And => return B(toBoolean(eval(env, en)) && toBoolean(eval(env, ed)))
//        case And => eval(env, en) match{
//          case B(a) => eval(env, ed) match{
//            case B(b) => return B(a && b)
//            case _=> return eval(env, ed)
//          }
//          case _=> return eval(env, ed)
//        }
        case And =>{
          val a = eval(env, en)
          val b = eval(env, ed)
          if(toBoolean(a)) return b
          else return a
        }
        
        case Or =>{
          val b = eval(env, ed)
          val a = eval(env, en)
          if(toBoolean(a)) return a;
          else return b
        }

        case Seq =>{ eval(env, en) //sequential operator evaluates both statements and returns the last
          return eval(env, ed)
          }
        }
        case _ => throw new UnsupportedOperationException
      }
  }
//  println("fuck")
//    val e1 = N(3)
//    val e2 = Binary(Plus, Var("x"), N(1))
//    val e3 = ConstDecl("x", e1, e2)
//    val e4 = Binary(Plus, e3, N(5))
//    eval(e4)
//    val xxx = 10 - 3 << 1 //if << has precedence, evaluates 10 - (3 << 1) = 4
//    						//if - has precence, evaluates (10 - 3) << 1 = 14
//    val yyy = 2 << 2 - 1 //if << has precedence, evaluates to 8 - 1 = 7
//    						// if - has precedence, evaluates to (2 << 1) = 4
    
    
  
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}