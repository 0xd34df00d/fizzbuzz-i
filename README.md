# fizzbuzz

If OOP folks have [their](https://github.com/EnterpriseQualityCoding/FizzBuzzEnterpriseEdition) FizzBuzz,
why can't we have our own?

This is an implementation of the FizzBuzz game, formally verified, provably correct, Idris version.
It is built almost entirely from scratch, including our very own natural numbers with our own
(formally verified, provably correct) division procedure.

The rules of FizzBuzz are as follows. For numbers 1 through 100: 
* if the number is divisible by 3 print Fizz;
* if the number is divisible by 5 print Buzz;
* if the number is divisible by 3 and 5 (15) print FizzBuzz;
* else, print the number.

Dependent types allow ensuring that `Fizz` is printed iff the number is divisible by 3,
and `Buzz` is printed iff the number is divisible by 5.
There is no actual printing procedure because, as usual, the code is not intended to be run,
but just type-checked.

Generalizing fizzbuzz to arbitrary algebraic structures (instead of just natural numbers)
is planned for version 2.
