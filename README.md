# Valk

Valk is a relatively simple programming language, examples can be found in the aptly named examples folder.

Valk utilizes the novel sulzmann and lu lexing algorithm, and a simple and digestible recursive descent parser. 

Valk's type system is primitive and is achieved by passing scope environments between compilation functions, no hindley milner here :(

Valk lowers to LLVM IR and can therefore be run by the LLVM interpreter lli, or clang compiler.

If you'd like to play around with Valk:

  1. Clone the repo
  2. Make sure you have sbt installed and configured
  3. Copy and paste the compiler.sc file into the repl and call the write() function with the path to the valk file.
  4. The compiler will then write the LLVM IR to a file that you can compile and run with lli and clang (these are both available on most package managers)

