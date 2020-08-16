# Formal proof for compact sequences

(Currently only for stacks.)

The file `proof/Stack.v` is a proof in [Coq][coq] of the amortized complexity of
compact stacks. The main goal is to formalize the invariant of the data
structure, and make sure all the cases to verify it have been covered.

[coq]: https://coq.inria.fr/

To fully accept the result of that proof, you must still understand the
invariant---in fact, most of the file is dedicated to defining and explaining
it---and you must trust that it implies the expected complexity guarantees.
Proving that implication formally is possible but a lot more work.

The comments in `proof/Stack.v` contain more technical details.

## Check the proof

This file has been checked with Coq from version 8.9 to 8.11;
it's expected to remain valid for the foreseeable future.

```
coqc Stack.v
```
