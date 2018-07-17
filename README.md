# VSchmidty
Verified Schmidty Interpreter.

A reinventing-the-wheel and imitative summary of multiple type systems introduced in *Software Foundations*, besides I have proved a great deal of decidability for future extraction, and I have put all the features in type system together (Sum Type, Record Type, Subtyping) thus the definition of the core language is much larger, which bring chanllenges into the readbility and maintainability of the proof script.

Since it is a total re-invention, the small-step semantic is slightly different; the definition of subtyping is different as well. It is not a deliberate action -- it is just a formalization of a type system according to my own intuition, and this definition works out.

Interestingly, primitive type is somehow represented in the same form with the extensive types, i.e., the type introduced outside.

The definition won't change from now on since the deciablity of the subtyping has already been proved. Except when I finally make up my mind to introduce stronger types -- after all, recursive type should be on the schedule. However, I don't think I will ever introduce side effect into this system. 
And keep it formally correct is very time consuming and HARD.
