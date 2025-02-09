import scala.compiletime.ops.string
// CW 2
//======
// checking for changes  

// Rexps
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

// new regular expressions
case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp


// values - you might have to extend them 
// according to which values you want to create
// for the new regular expressions
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val


// convenience for typing regular expressions
import scala.language.implicitConversions

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}

given Conversion[String, Rexp] = (s => charlist2rexp(s.toList))

extension (r: Rexp) {
  def ~ (s: Rexp) = SEQ(r, s)
  def % = STAR(r)
  def | (s: Rexp) = ALT(r, s)
}

extension (s: String) {
  def $ (r: Rexp) = RECD(s, r)
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
}


// nullable (needs to be extended for new regular expressions)
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case RECD(_, r1) => nullable(r1)
}

// der (needs to be extended for new regular expressions)
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RANGE(s) => if (s contains c) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case NTIMES(r, n) => if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
  case RECD(_, r1) => der(c, r1)
}

// flatten (needs to work with all values) 
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// env (needs to work with all values) 
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// mkeps (needs to be extended for new regular expressions)
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case PLUS(r) => Sequ(mkeps(r), Stars(Nil))
  case OPTIONAL(r) => if (nullable(r)) Left(mkeps(r)) else Right(Empty)
  case NTIMES(r, n) => if (n == 0) Empty else Sequ(mkeps(r), mkeps(NTIMES(r, n - 1)))
  case RECD(x, r) => Rec(x, mkeps(r))
}

// inj (needs to be extended for new regular expressions)
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c)
  case (RANGE(s), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Sequ(inj(r, c, v1), Stars(vs))
  case (OPTIONAL(r), Empty) => Chr(c)
  case (NTIMES(r, n), Sequ(v1, v2)) => Sequ(inj(r, c, v1), v2)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}


// the simplification and rectification part
// can be left untouched

// rectification functions
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simp
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID) // this part handles all new regular expressions
}

// lexing generating a value
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

// lexing extracting a list of String-String pairs 
def lexing_simp(r: Rexp, s: String) : List[(String, String)] = 
  env(lex_simp(r, s.toList))

// Language specific code for the While Language 
// (you need to create the regular expressions - see CW2) 
val NONZERO : Rexp =  RANGE(Set('1', '2', '3', '4', '5', '6', '7', '8', '9'))
val KEYWORD : Rexp = SEQ(CHAR('f'), SEQ(CHAR('o'), CHAR('r'))) |
                     SEQ(CHAR('v'), SEQ(CHAR('a'), CHAR('l'))) |
                     SEQ(SEQ(CHAR('d'), CHAR('e')), CHAR('f')) |
                     SEQ(CHAR('i'), CHAR('f')) | 
                     SEQ(SEQ(CHAR('t'), CHAR('h')), SEQ(CHAR('e'), CHAR('n'))) |
                     SEQ(SEQ(CHAR('e'), CHAR('l')), SEQ(CHAR('s'), CHAR('e'))) |
                     SEQ(SEQ(CHAR('t'), CHAR('r')), SEQ(CHAR('u'), CHAR('e'))) |           
                     SEQ(SEQ(SEQ(SEQ(CHAR('f'), CHAR('a')), CHAR('l')), CHAR('s')), CHAR('e')) |
                     SEQ(SEQ(SEQ(SEQ(CHAR('w'), CHAR('h')), CHAR('i')), CHAR('l')), CHAR('e'))                      
                                                              
val RESFUNC : Rexp = SEQ(SEQ(SEQ(CHAR('p'), CHAR('r')), SEQ(CHAR('i'), CHAR('n'))), SEQ(CHAR('t'), SEQ(CHAR('_'), SEQ(CHAR('i'), SEQ(CHAR('n'), CHAR('t')))))) |  // print_int
                     SEQ(SEQ(SEQ(CHAR('p'), CHAR('r')), SEQ(CHAR('i'), CHAR('n'))), SEQ(CHAR('t'), SEQ(CHAR('_'), SEQ(CHAR('s'), SEQ(CHAR('t'), SEQ(CHAR('r'), SEQ(CHAR('i'), SEQ(CHAR('n'), CHAR('g'))))))))) |  // print_string
                     SEQ(SEQ(CHAR('n'), CHAR('e')), SEQ(CHAR('w'), SEQ(CHAR('_'), SEQ(CHAR('l'), SEQ(CHAR('i'), SEQ(CHAR('n'), CHAR('e'))))))) | // new_line
                     SEQ(SEQ(SEQ(CHAR('p'), CHAR('r')), SEQ(CHAR('i'), CHAR('n'))), SEQ(CHAR('t'), SEQ(CHAR('_'), SEQ(CHAR('c'), SEQ(CHAR('h'), SEQ(CHAR('a'), CHAR('r'))))))) | // print_char
                     SEQ(SEQ(CHAR('s'), CHAR('k')), SEQ(CHAR('i'), CHAR('p'))) 

val TYPE : Rexp = SEQ(SEQ(CHAR('I'), CHAR('n')), CHAR('t')) |  // Int
                  SEQ(SEQ(SEQ(SEQ(SEQ(CHAR('D'), CHAR('o')), CHAR('u')), CHAR('b')), CHAR('l')), CHAR('e')) |  // Double 
                  SEQ(SEQ(SEQ(CHAR('V'), CHAR('o')), CHAR('i')), CHAR('d'))  // Void
                  
val OP : Rexp = CHAR('+') | CHAR('-') | CHAR('*') | CHAR('%') | CHAR('/') | SEQ(CHAR('='), CHAR('=')) | SEQ(CHAR('!'), CHAR('=')) |
                CHAR('>') | CHAR ('<')| SEQ(CHAR('<'), CHAR('=')) | SEQ(CHAR('>'), CHAR('=')) | SEQ(CHAR(':'), CHAR('=')) | SEQ(CHAR('&'), CHAR('&')) |
                SEQ(CHAR('|'), CHAR('|')) | CHAR(':') | CHAR('=') | CHAR(',')

val ANY : Rexp = RANGE(Set.from((' ' to '~')))  // All printable ASCII characters
                
val LET: Rexp = RANGE(Set('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 
                          'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'))

val CAPS : Rexp = RANGE(Set('A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'))

val LOWERCASE : Rexp = RANGE(Set('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'))
                        
val SYM : Rexp = RANGE(Set('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 
                          'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0',
                        '.', '_', '>', '<', '=', ';', ',', '\\', ':', '+', '-', '/', ' ')) 

val PARENS : Rexp = CHAR('(') | CHAR(')') | CHAR('{') | CHAR('}')
val DIGIT : Rexp = RANGE(Set('0','1', '2', '3', '4', '5', '6', '7', '8', '9'))

val DOUBLE : Rexp = OPTIONAL("-") ~ (DIGIT | (RANGE("123456789".toSet) ~ DIGIT.%)) ~ "." ~ PLUS(DIGIT)

val CHAR_LIT : Rexp = SEQ(CHAR('\''),SEQ(ALT(SYM,SEQ(CHAR('\\'), CHAR('n'))),CHAR('\'')))

val SEMI : Rexp = CHAR(';')
val WHITESPACE : Rexp = ALT(ALT(PLUS(CHAR(' ')), CHAR('\n')), ALT(CHAR('\t'), CHAR('\r'))) 
val CONST : Rexp = SEQ(CAPS, STAR(ALT(ALT(LET, DIGIT), CHAR('_'))))
val ID : Rexp = SEQ(LOWERCASE, STAR(ALT(ALT(LET, DIGIT), CHAR('_'))))
val NUMBERS : Rexp = ALT(CHAR('0'), SEQ(NONZERO, STAR(DIGIT)))
val STRING : Rexp = SEQ(SEQ(CHAR('"'), STAR(ALT(ALT(ALT(SYM, DIGIT), ALT(PARENS, WHITESPACE)), SEQ(CHAR('\\'), CHAR('n'))))), CHAR('"'))
val COMMENT : Rexp = SEQ(SEQ(CHAR('/'), CHAR('/')), STAR(ANY))
val EOL : Rexp = ALT(CHAR('\n'), SEQ(CHAR('\r'), CHAR('\n')))

val WHILE_REGS = (("k" $ KEYWORD) |
                  ("rf" $ RESFUNC) | 
                  ("o" $ OP) |
                  ("t" $ TYPE) |   
                  ("str" $ STRING) |
                  ("p" $ PARENS) |
                  ("s" $ SEMI) | 
                  ("w" $ WHITESPACE) |
                  ("const" $ CONST) |
                  ("i" $ ID) |
                  ("d" $ DOUBLE) |
                  ("n" $ NUMBERS) |
                  ("char" $ CHAR_LIT) |
          ("c" $ COMMENT)).%

// Token
abstract class Token extends Serializable 
case class T_KEYWORD(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STRING(s: String) extends Token
case class T_PAREN(s: String) extends Token
case object T_SEMI extends Token
case class T_ID(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_TYPE(s: String) extends Token 
case class T_CONST(s: String) extends Token
case class T_DOUBLE(n: Double) extends Token
case class T_CHAR(n: Int) extends Token
case class T_RESFUNC(s: String) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KEYWORD(s)
  case ("o", s) => T_OP(s)
  case ("str", s) => T_STRING(s)
  case ("p", s) => T_PAREN(s)
  case ("s", _) => T_SEMI
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("t", s) => T_TYPE(s)
  case ("const", s) => T_CONST(s)
  case ("d", s) => T_DOUBLE(s.toDouble)
  case ("char", s) => {
    val c = if (s.length == 3) s(1) else '\n'
    T_CHAR(c.toInt)
  }
  case ("rf", s) => T_RESFUNC(s)
}

// Tokenise
def tokenise(s: String) : List[Token] = 
  lexing_simp(WHILE_REGS, s).collect(token)


def test(file: String) = {
  val contents = os.read(os.pwd / "examples" / file)
  println(s"Lex $file: ")
  println(tokenise(contents)) 
}


// CW5

import scala.language.implicitConversions    
import scala.language.reflectiveCalls


// Parser combinators
//    type parameter I needs to be of Seq-type
//
type IsSeq[I] = I => Seq[?]

abstract class Parser[I, T](using is: IsSeq[I])  {
  
  def parse(in: I): Set[(T, I)]
    
  def parse_all(in: I) : Set[T] =
    val results = parse(in)
    for ((hd, tl) <- parse(in); 
        if is(tl).isEmpty) yield hd

}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

// parser combinators

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

// more convenient syntax for parser combinators
extension [I : IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

def ListParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(using is: I => Seq[?]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)).map{ case (x:T) ~ (y:S) ~ (z:List[T]) => x :: z } ||
  (p.map[List[T]]{s => List(s)})
}

case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) : Parser[List[Token], Token] = TokParser(t)

extension (t: Token) {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def map[S] (f: => Token => S) = new MapParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_NUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object TypeParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_TYPE(s)::ts => Set((s, ts))
    case _ => Set()
  }
}

case object DoubleParser extends Parser[List[Token], Double] {
  def parse(ts: List[Token]) = ts match {
    case T_DOUBLE(n)::ts => Set((n, ts))
    case _ => Set()
  }
}

case object ConstParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_CONST(s)::ts => Set((s, ts))
    case _ => Set()
  }
}

case object StringParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_STRING(s)::ts => Set((s, ts))
    case _ => Set()
  }
}


case object CharParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_CHAR(n)::ts => Set((n, ts))
    case _ => Set()
 }
}

case object ResParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_RESFUNC(s)::ts => Set((s, ts))
    case _ => Set()
  }
}

// Abstract Syntax Trees for the typed Fun-language
// (this can be part of the parser file, if mor convenient)

abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String, String)], ty: String, body: Exp) extends Decl // done
case class Main(e: Exp) extends Decl
case class Const(name: String, v: Int) extends Decl // done
case class FConst(name: String, x: Double) extends Decl // done
case class StringDecl(name: String, value: String) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp // done
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp // done
case class Var(s: String) extends Exp // done
case class Num(i: Int) extends Exp  // integer numbers // done
case class FNum(i: Double) extends Exp  // float numbers // done
case class ChConst(c: Int) extends Exp  // character constants // done 
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp // done
case class Sequence(e1: Exp, e2: Exp) extends Exp  // expressions separated by semicolons
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp // done
case class StringInst(s: String) extends Exp

lazy val Arg: Parser[List[Token], (String, String)] = 
  (IdParser ~ T_OP(":") ~ TypeParser).map{ case id ~ _ ~ ty => (id, ty) }

lazy val EmptyExpList: Parser[List[Token], List[Exp]] =
  (T_PAREN("(") ~ T_PAREN(")")).map{ case _ ~ _ => List() }

lazy val Decl: Parser[List[Token], Decl] = 
  (T_KEYWORD("val") ~ ConstParser ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ NumParser).map{ case _ ~ name ~ _ ~ _ ~ _ ~ value => Const(name, value)} ||
  (T_KEYWORD("val") ~ ConstParser ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ DoubleParser).map{ case _ ~ name ~ _ ~ _ ~ _ ~ value => FConst(name, value)} ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ ListParser(Arg, T_OP(",")) ~ T_PAREN(")") ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ Exp).map{ case _ ~ name ~ _ ~ args ~ _ ~ _ ~ retType ~ _ ~ body => Def(name, args, retType, body) } ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ ListParser(Arg, T_OP(",")) ~ T_PAREN(")") ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ T_PAREN("{") ~ Exp ~ T_PAREN("}")).map{ case _ ~ name ~ _ ~ args ~ _ ~ _ ~ retType ~ _ ~ _ ~ body ~ _ => Def(name, args, retType, body)} ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ T_PAREN(")") ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ Exp).map{ case _ ~ name ~ _ ~ _ ~ _ ~ retType ~ _ ~ body => Def(name, List(), retType, body)} ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ T_PAREN(")") ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ T_PAREN("{") ~ Exp ~ T_PAREN("}")).map{ case _ ~ name ~ _ ~ _ ~ _ ~ retType ~ _ ~ _ ~ body ~ _  => Def(name, List(), retType, body)} 

lazy val Exp: Parser[List[Token], Exp] = 
  (T_KEYWORD("if") ~ BExp ~ T_KEYWORD("then") ~ T_PAREN("{") ~ Exp ~ T_PAREN("}") ~ T_KEYWORD("else") ~ Exp).map{ case _ ~ x ~ _ ~ _ ~ y ~ _ ~ _ ~ z => If(x, y, z) } ||
  (T_KEYWORD("if") ~ BExp ~ T_KEYWORD("then") ~ Exp ~ T_KEYWORD("else") ~ Exp).map{ case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z) } ||
  (T_KEYWORD("if") ~ BExp ~ T_KEYWORD("then") ~ Exp ~ T_KEYWORD("else") ~  T_PAREN("{") ~ Exp ~ T_PAREN("}")).map{ case _ ~ x ~ _ ~ y ~ _ ~ _ ~ z ~ _ => If(x, y, z) } ||
  (T_PAREN("{") ~ L ~ T_SEMI ~ Exp ~ T_PAREN("}")).map{ case _ ~ x ~ _ ~ y ~ _ => Sequence(x, y) } ||
  (L ~ T_SEMI ~ Exp).map{ case x ~ _ ~ y => Sequence(x, y) } || L
 
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp).map{ case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp).map{ case x ~ _ ~ z => Aop("-", x, z): Exp } || T  

lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T).map{ case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T).map{ case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T).map{ case x ~ _ ~ z => Aop("%", x, z): Exp } || F

lazy val F: Parser[List[Token], Exp] =
  (ResParser ~ (EmptyExpList || (T_PAREN("(") ~ ListParser(Exp, T_OP(",")) ~ T_PAREN(")")).map{ case _ ~ args ~ _ => args })).map{ case name ~ args => Call(name, args): Exp } ||
  (IdParser ~ (EmptyExpList || (T_PAREN("(") ~ ListParser(Exp, T_OP(",")) ~ T_PAREN(")")).map{ case _ ~ args ~ _ => args })).map{ case name ~ args => Call(name, args): Exp } ||
  (ResParser).map{ case x => Call(x, List())} ||
  (T_PAREN("(") ~ Exp ~ T_PAREN(")")).map{ case _ ~ y ~ _ => y: Exp } || 
  IdParser.map{ case x => Var(x): Exp } ||
  NumParser.map{ case x => Num(x): Exp } ||
  DoubleParser.map{ case x => FNum(x)} ||
  CharParser.map{ case x => ChConst(x)} ||
  ConstParser.map{case x => Var(x) : Exp} ||
  StringParser.map{ case x => StringInst(x) : Exp}


// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp).map{ case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp).map{ case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP("=>") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", z, x): BExp }  
  
lazy val Prog: Parser[List[Token], List[Decl]] =
  (Decl ~ T_SEMI ~ Prog).map{ case x ~ _ ~ z => x :: z } ||  
  (Decl ~ T_SEMI).map{ case x ~ _ => List(x) } ||            
  (Exp.map(e => List(Main(e))))                              

def parse_tks(tks: List[Token]) : Set[List[Decl]] = 
  Prog.parse_all(tks)

def test_parse(fname: String) : Unit = {
 val contents = os.read(os.pwd / "examples" / fname)
 val tks = tokenise(contents)
 println(parse_tks(tks).head)
}

def test_parse_ret(fname: String) : List[Decl] = {
  val contents = os.read(os.pwd / "examples" / fname)
  val tks = tokenise(contents)
  parse_tks(tks).head
}


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Extended KVal classes to include floating point and character support
abstract class KExp
abstract class KVal

case class KVar(s: String, ty: Ty = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(d: Double) extends KVal             // For floating point numbers
case class KChConst(c: Int) extends KVal            // For character constants
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(name: String, args: List[KVal]) extends KVal
case class KLoad(name: String, ty: String = "UNDEF") extends KVal
case class KString(s: String) extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}

case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}

case class KReturn(v: KVal) extends KExp

def CPS(e: Exp)(k: KVal => KExp): KExp = e match {
  case Var(s) => 
    if (s.head.isUpper) {
      val z = Fresh("tmp")
      KLet(z, KLoad(s), k(KVar(z)))
    } else k(KVar(s))
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case ChConst(c) => k(KChConst(c))
  case StringInst(s) => k(KString(s))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => {
        // Track intermediate calculation type
        val resType = y1 match {
          case KVar(_, "Double") => "Double"
          case KFNum(_) => "Double"
          case KVar(name, "UNDEF") => y2 match {
            case KVar(_, "Double") => "Double"
            case KFNum(_) => "Double"
            case _ => "UNDEF"
          }
          case _ => y2 match {
            case KVar(_, "Double") => "Double"
            case KFNum(_) => "Double"
            case _ => "UNDEF"
          }
        }
        // Store intermediate result with type
        KLet(z, Kop(o, y1, y2), k(KVar(z, resType)))
    }))
  }
  
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => {
        // Comparisons should stay as Int for boolean results
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))
      }))
  }

  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]): KExp = args match {
      case Nil => {
        val z = Fresh("tmp")
        KLet(z, KCall(name, vs), k(KVar(z)))
      }
      // Handle StringInst directly in aux
      case (s: StringInst)::es => aux(es, vs ::: List(KVar(s.s)))
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }

  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))

}



// Initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn(_))

// CPS translation for declarations
def CPSd(d: Decl): KExp = d match {
  case Main(e) => CPSi(e)
  
  case Def(name, args, retType, body) => {
    // Convert function body to CPS form
    CPSi(body)
  }
  
  case Const(name, value) => 
    KReturn(KNum(value))
    
  case FConst(name, value) => 
    KReturn(KFNum(value))
}

// typing
type Ty = String
type TyEnv = Map[String, Ty]

// initial typing environment
val initialEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
                                 "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void", "print_string" -> "Void")

val typeConversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")


type FuncEnv = Map[String, List[Ty]]
def initialFuncEnv = Map[String, List[Ty]]("print_int" -> List("Int"), 
                                    "print_char" -> List("Int"),
                                    "print_string" -> List("String"),
                                    "print_space" -> List(),
                                    "new_line" -> List(),
                                    "print_star" -> List(),
                                    "skip" -> List(),
                                  )  


type GlobalEnv = Map[String, Ty]
def initialGlobalEnv = Map[String, Ty]()

type ArgEnv = Map[String, Map[String, Ty]]
def intialArgEnv = Map[String, Map[String, Ty]]()

// Go through AST and find all String Declarations 
// Make copies of these string declarations 
// Somehow transform them into Decls to generate their globals 
// then handle them as declarations at the lower level.

def collectStrings(ast: List[Decl]): List[(String, String)] = {
  def collectFromExp(e: Exp): List[(String, String)] = e match {
    case StringInst(value) => List((Fresh("str"), value))
    case Sequence(e1, e2) => collectFromExp(e1) ++ collectFromExp(e2)
    case If(_, e1, e2) => collectFromExp(e1) ++ collectFromExp(e2)
    case Call(_, args) => args.flatMap(collectFromExp)
    case Aop(_, e1, e2) => collectFromExp(e1) ++ collectFromExp(e2)
    case _ => Nil
  }

  ast.flatMap {
    case Def(_, _, _, body) => collectFromExp(body)
    case Main(body) => collectFromExp(body)
    case _ => Nil
  }.distinct
}

def extractFunctions(decls: List[Decl]): FuncEnv = {
  decls.foldLeft(initialFuncEnv) { (env, decl) =>
    decl match {
      case Def(name, args, _, _) =>
        // Extract argument types (second element of the tuple)
        val argTypes = args.map(_._2)
        // Add the function to the environment
        env + (name -> argTypes)
      case _ => env // Ignore other types of declarations
    }
  }
}

// Function to extract return types from the AST
def extractReturnTypes(decls: List[Decl]): TyEnv = {
  decls.foldLeft(initialEnv) { (tyEnv, decl) =>
    decl match {
      case Def(name, _, returnType, _) =>
        // Add the function to the typing environment
        tyEnv + (name -> returnType)
      case _ => tyEnv // Ignore other types of declarations
    }
  }
}

def extractGlobals(decls: List[Decl]): GlobalEnv = {
  decls.foldLeft(Map.empty[String, Ty]) { (env, decl) =>
    decl match {
      case Const(name, _) => env + (name -> "Int")
      case FConst(name, _) => env + (name -> "Double")
      case _ => env  // Ignore other declarations
    }
  }
}

def extractArgs(decls: List[Decl]): ArgEnv = {
  decls.foldLeft(Map.empty[String, Map[String, Ty]]) { (env, decl) =>
    decl match {
      case Def(name, args, _, _) =>
        val argMap = args.map { case (argName, argType) => argName -> argType }.toMap
        env + (name -> argMap)
      case _ => env  // Ignore other declarations
    }
  }
}

def typ_val(v: KVal, ts: TyEnv, fe: FuncEnv, ge: GlobalEnv, argEnv: Map[String, Ty]): KVal = v match {
  case KNum(i) => KNum(i)
  case KFNum(d) => KFNum(d)
  case KChConst(c) => KChConst(c)
  case KLoad(name, _) => 
    KLoad(name, ge.getOrElse(name, "Int"))
  case KString(s) => KString(s)
  case KVar(x, "UNDEF") => 
    // Check argument types first, then fall back to other envs
    KVar(x, argEnv.getOrElse(x, ts.getOrElse(x, "Int")))  
  case KVar(x, ty) => KVar(x, ty)
    
  case Kop(op, v1, v2) => {
    val tv1 = typ_val(v1, ts, fe, ge, argEnv)
    val tv2 = typ_val(v2, ts, fe, ge, argEnv)
    
   // Keep the operation but update the operands
    Kop(op, tv1, tv2)  // Keep Kop, not create new KVar
  }
  
  case KCall(name, args) => {
    val currentEnv = fe(name)
    val zippedArgs = args.zip(currentEnv).map { case (arg, expected_ty) => 
      arg match {
        case v: KVar => KVar(v.s, expected_ty)
        case KNum(i) => KNum(i)  // Numbers stay as they are
        case KFNum(d) => KFNum(d)
        case KChConst(c) => KChConst(c)
        case _ => throw new Exception(s"Unexpected argument type in call to $name")
      }
    }
    KCall(name, zippedArgs)
  }
}


def getType(v: KVal, env: TyEnv, currentFuncArgs: Map[String, Ty]): String = v match {
  case KNum(_) => "Int"
  case KFNum(_) => "Double"
  case KChConst(_) => "Int"
  case KVar(name, ty) => 
    if (ty != "UNDEF") ty
    else env.getOrElse(name, currentFuncArgs.getOrElse(name, "Int"))
  case Kop(_, v1, v2) => 
    val t1 = getType(v1, env, currentFuncArgs)
    val t2 = getType(v2, env, currentFuncArgs)
    if (t1 == "Double" || t2 == "Double") "Double" else "Int"
  case KCall(name, _) => env.getOrElse(name, "Int")
  case KLoad(_, ty) => ty
}


def typ_exp(a: KExp, ts: TyEnv, fe: FuncEnv, ge: GlobalEnv, argEnv: Map[String, Ty]): KExp = a match {
  case KReturn(v) => {
    val tv = typ_val(v, ts, fe, ge, argEnv)
    val retType = tv match {
      case KNum(_) => "Int"
      case KFNum(_) => "Double"
      case KChConst(_) => "Int"
      case KVar(_, t) => t
      case KCall(name, _) => ts.getOrElse(name, "Int")  // Get return type from environment
      case Kop(_, v1, _) => v1 match {
        case KFNum(_) => "Double"
        case _ => "Int"
      }
      case _ => "Int"
    }
    v match {
      case KVar(x, _) => KReturn(KVar(x, retType))
      case _ => KReturn(tv)
    }
  }
    
 case KLet(x, v, e) => {
    val typedVal = typ_val(v, ts, fe, ge, argEnv)
    val valType = typedVal match {
      case KNum(_) => "Int"
      case KFNum(_) => "Double"
      case KChConst(_) => "Int"
      case KVar(_, t) => t
      case KCall(name, _) => ts.getOrElse(name, "Int")
      case Kop(_, v1, v2) => {
        // Use getType to properly determine the operation's type
        val t1 = getType(v1, ts, argEnv)
        val t2 = getType(v2, ts, argEnv)
        if (t1 == "Double" || t2 == "Double") "Double" else "Int"
      }
      case _ => "Int"
    }
    val newTs = ts + (x -> valType)
    KLet(x, typedVal, typ_exp(e, newTs, fe, ge, argEnv))
  }


  case KIf(x, e1, e2) => 
    KIf(x, typ_exp(e1, ts, fe, ge, argEnv), typ_exp(e2, ts, fe, ge, argEnv))
}

// prelude
val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_int = private constant [3 x i8] c"%d\00"
@.str_c = private constant [3 x i8] c"%c\00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_int, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @print_char(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_c, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x)
  ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILT-IN FUNCTIONS (prelude)
"""

def typ_decl(d: Decl, ts: TyEnv, fe: FuncEnv, ge: GlobalEnv, argEnv: Map[String, Ty]): (KExp, TyEnv) = d match {
  case Def(name, args, retType, body) => {
    // Add args to environment before type inference
    val newTs = ts ++ args.map{ case (name, ty) => name -> ty }
    val cpsBody = CPSi(body)
    val typedBody = typ_exp(cpsBody, newTs, fe, ge, argEnv)  // Use environment with args
    (typedBody, newTs)
  }
  case _ => (KReturn(KNum(0)), ts)
}

// String interpolation helpers
extension (sc: StringContext) {
  def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
  def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
  def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// Mathematical operations with types
def compile_op(op: String, ty: String) = (op, ty) match {
  case ("+", "Int") => "add i32 "
  case ("*", "Int") => "mul i32 "
  case ("-", "Int") => "sub i32 "
  case ("/", "Int") => "sdiv i32 "
  case ("%", "Int") => "srem i32 "
  case ("==", "Int") => "icmp eq i32 "
  case ("<=", "Int") => "icmp sle i32 "
  case ("<", "Int") => "icmp slt i32 "
  case ("!=", "Int") => "icmp ne i32 "  
  
  case ("+", "Double") => "fadd double "
  case ("*", "Double") => "fmul double "
  case ("-", "Double") => "fsub double "
  case ("/", "Double") => "fdiv double "
  case ("==", "Double") => "fcmp oeq double "
  case ("<=", "Double") => "fcmp ole double "
  case ("<", "Double") => "fcmp olt double "
  case ("!=", "Double") => "fcmp one double "
}

def compile_decl(d: Decl, retEnv: TyEnv, funcEnv: FuncEnv, globalEnv: GlobalEnv, argEnv: ArgEnv, stringEnv: StringEnv): String = d match {
  case Def(name, args, retType, body) => {
    val llvmRetType = typeConversion(retType)
    val argTypes = args.map { case (name, ty) => 
      s"${typeConversion(ty)} %$name"
    }.mkString(", ")
    
    val cpsBody = CPSi(body)
    val funcArgMap = argEnv(name)
    val typedBody = typ_exp(cpsBody, retEnv,funcEnv, globalEnv, funcArgMap)  // Just use retEnv
    m"define $llvmRetType @$name ($argTypes) {" ++
    compile_exp(typedBody, retEnv, funcArgMap, stringEnv) ++         // Just use retEnv
    m"}\n"
  }
  
  case Main(body) => {
    val cpsBody = CPS(body)(_ => KReturn(KNum(0)))
    val funcArgMap = Map[String, Ty]()
    val typedBody = typ_exp(cpsBody, retEnv, funcEnv, globalEnv, funcArgMap)
    
    m"define i32 @main() {" ++
    compile_exp(typedBody, retEnv, funcArgMap, stringEnv) ++
    m"}\n"
  }
  
  case Const(name, value) =>
    m"@$name = global i32 $value\n"
    
  case FConst(name, value) =>
    m"@$name = global double $value\n"

  case StringDecl(_, _) => ""
}


def compile_val(k: KVal, env: TyEnv, argEnv: Map[String, Ty], stringEnv: StringEnv): String = k match {
  case KNum(i) => s"$i"
  case KFNum(d) => s"$d"
  case KChConst(c) => s"$c"
  case KVar(s, ty) => s"%$s"
  case KLoad(name, ty) => s"load ${typeConversion(ty)}, ${typeConversion(ty)}* @$name"
  case KString(s) => s"@str_$s" 
  case Kop(op, x1, x2) => {
    def getLocalType(v: KVal): String = v match {
      case KVar(name, _) => 
        argEnv.getOrElse(name, getType(v, env, argEnv))
      case KFNum(_) => "Double"
      case KNum(_) => "Int"
      case KLoad(_, ty) => ty
      // Add this case to handle nested operations
      case Kop(_, v1, v2) => 
        val t1 = getLocalType(v1)
        val t2 = getLocalType(v2)
        if (t1 == "Double" || t2 == "Double") "Double" else "Int"
      case _ => getType(v, env, argEnv)
    }
    
    val type1 = getLocalType(x1)
    val type2 = getLocalType(x2)
   
    val resultType = if (type1 == "Double" || type2 == "Double") "Double" else "Int"
    s"${compile_op(op, resultType)} ${compile_val(x1, env, argEnv, stringEnv)}, ${compile_val(x2, env, argEnv, stringEnv)}"
  }
  
  case KCall("print_string", args) => {
    val stringVar = Fresh("t")
    val str = args.head match {
      case KString(s) => stringEnv(s)  // Get the number part from the name
      case KVar(s, "String") => stringEnv(s)  // Get the number part from the name
    }
    val len = str.length + 1
    s"%$stringVar = getelementptr [$len x i8], [$len x i8]* @$str, i32 0, i32 0\n" ++
    s"   call i32 (i8*, ...) @printf(i8* %$stringVar)"
  }

       
  case KCall(x1, args) => {
    val retType = env.getOrElse(x1, "should never happend")
    val argsWithTypes = args.map(arg => s"${typeConversion(getType(arg, env, argEnv))} ${compile_val(arg, env, argEnv, stringEnv)}")   
    if (retType == "Void") {
      s"call void @$x1(${argsWithTypes.mkString(", ")})"
    } else {
      s"call ${typeConversion(retType)} @$x1(${argsWithTypes.mkString(", ")})"
    }
  }   
}


type StringEnv = Map[String, String]

def compile_exp(k: KExp, env: TyEnv, argEnv: Map[String, Ty], stringEnv: StringEnv): String = k match {
  case KReturn(v) => {
    val ty = getType(v, env, argEnv)
    if (ty == "Void") {
      i"ret void"
    } else {
      i"ret ${typeConversion(ty)} ${compile_val(v, env, argEnv, stringEnv)}"
    }
  }
    
  case KLet(x, v, e) => {
    val dbg = getType(v, env, argEnv)
    if (getType(v, env, argEnv) == "Void") {
      i"${compile_val(v, env, argEnv, stringEnv)}" ++ compile_exp(e, env, argEnv, stringEnv)
    } else {
      i"%$x = ${compile_val(v, env, argEnv, stringEnv)}" ++ compile_exp(e, env, argEnv, stringEnv)
    }
  }
  
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1, env, argEnv, stringEnv) ++
    l"\n$else_br" ++ 
    compile_exp(e2, env, argEnv, stringEnv)
  }
}

def generateStringConst(name: String, value: String): String = {
  val stripped = value.stripPrefix("\"").stripSuffix("\"")
  val bytes = stripped.length + 1 
  s"""@$name = internal constant [$bytes x i8] c"$stripped\\00"\n"""
}

def fun_compile(prog: List[Decl]): String = {
    // Get all the strings and transform them to String Declaration ASTs 
  val strings = collectStrings(prog)
  val stringDecls: List[StringDecl] = strings.map { case (name, value) =>
    StringDecl(name, value)
  }

  val stringEnv = strings.map { case (name, value) => value -> name }.toMap
  
  // Generate string constants
  val stringConsts = strings.map { case (name, value) =>
    generateStringConst(name, value)
  }.mkString("\n")
  
  
  val finalAst = if (strings.length > 0) stringDecls ++ prog else prog

  // Build environments
  val retEnv = extractReturnTypes(finalAst)
  val funcEnv = extractFunctions(finalAst)
  val globalEnv = extractGlobals(finalAst)
  val argEnv = extractArgs(finalAst)

  // Generate LLVM
  prelude ++ 
  stringConsts ++  // Add string constants here
  finalAst.map(d => compile_decl(d, retEnv, funcEnv, globalEnv, argEnv, stringEnv)).mkString
}

@main
def write(fname: String) = {
    val path = os.pwd / "examples" /  fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks).head
    val code = fun_compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}


