val max : int = 10;

def sqr(x: int) : int = x * x;

def all(n: int) : void = {
  if n <= max
  then { print_int(sqr(n)) ; new_line(); all(n + 1) }
  else skip()
};

{
  print_string("squares");
  new_line();
  all(0)
} 
