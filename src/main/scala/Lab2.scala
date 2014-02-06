//The directory switch worked
object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Samuel Volin>
   * 
   * Partner: <Roberto Kingsly>
   * Collaborators: <Sam Volin, Alex Tsankov>
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
      case N(n) => if (n == 0) return false else return !n.isNaN() 
      case S(s) => if (s == "") return false else return true
      case Undefined => return false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => if(n%1 ==0) return n.toInt.toString else return n.toString
      case B(b) => if(b) return "true" else return "false"
      case Undefined => "undefined"
      //case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)

    e match {
      /* Base Cases */
      case N(n) => return e; //eval should return the expression if it is a terminal
      case B(b) => return e;
      case S(s) => return e; 
      case Undefined => return e ;
      /* Inductive Cases */
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Var(x) =>{ 
        //println(x); 
        return Undefined
        //return env(x)
      }
      case ConstDecl(x, en, ed) =>
        {val term = eval(en)
          return eval(env + (x -> term), ed)
        }
      case If(cond, t, f) => if(toBoolean(cond)) return eval(t) else return eval(f)
      case Unary(op, en) => op match
      {
        case Neg => return N(-1 * toNumber(eval(en))) //unary make negative
        case Not => return B(!toBoolean(eval(en)))
        case _ => throw new UnsupportedOperationException
      }
      case Binary(op, en, ed) => op match
      {

        case Plus => en match{//plus works on number and string types. If either type is a string, it concatenates one expresiion with the other
          case N(a) => ed match{
            case N(b) => return N(a+b)
            case _=> return S(toStr(eval(en)).concat(toStr(eval(ed))))
          }
          case _=> return S(toStr(eval(en)).concat(toStr(eval(ed))))
          
        }

        //case Plus => return N(toNumber(eval(en)) + toNumber(eval(ed)))
        case Minus => return N(toNumber(eval(en)) - toNumber(eval(ed)))
        case Times => return N(toNumber(eval(en)) * toNumber(eval(ed)))
        case Div => { //binary divide
        	if (toNumber(eval(ed)) == 0) { //checks if we are dealing with a zero
        		if (toNumber(eval(en)) > 0) //if the numerator is greater than zero, return positive
        			return N(Double.PositiveInfinity)
        		else return N(Double.NegativeInfinity) //otherwise return neg infinity
        	} else return N(toNumber(eval(en)) / toNumber(eval(ed))) //otherwise return the actual division
        }
        case Eq => return B((toNumber(eval(en)) == toNumber(eval(ed)))) //fix
        case Ne => return B((toNumber(eval(en)) != toNumber(eval(ed)))) //fix
        case Lt => return B((toNumber(eval(en)) < toNumber(eval(ed))))
        case Le => return B((toNumber(eval(en)) <= toNumber(eval(ed))))
        case Gt => return B((toNumber(eval(en)) > toNumber(eval(ed))))
        case Ge => return B((toNumber(eval(en)) >= toNumber(eval(ed))))
        case And => return B((toBoolean(eval(en)) && toBoolean(eval(ed))))
        case Or => return B((toBoolean(eval(en)) || toBoolean(eval(ed))))
        case Seq =>{ eval(en) //sequential operator evaluates both statements and returns the last
          return eval(ed)
          }
        }
        case _ => throw new UnsupportedOperationException
      }
  }
  println("fuck")
    val e1 = N(3)
    val e2 = Binary(Plus, Var("x"), N(1))
    val e3 = ConstDecl("x", e1, e2)
    val e4 = Binary(Plus, e3, N(5))
    eval(e4)
    
  
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