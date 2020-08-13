## Path to contribution

I recommend that potential contributors start by
getting to know `Data.CompactSequence.Stack.Internal`.
The basic operations there require considerably
less code than those for the other structures, so
it's easier to understand how they interact with
the debit invariant. The queues are a bit more
code with some strictness invariants not explicitly
expressed in the type itself. Deques
(still being implemented) are just like queues,
but with lots and lots more cases to deal with.

Speaking of debit invariants, it
will be very helpful for contributors to have some
intuition around Okasaki's debit analysis framework.
This is explained very accessibly in
[his thesis](http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf),
as well as
[the textbook](https://www.goodreads.com/book/show/594288.Purely_Functional_Data_Structures)
he expanded it into. There's no need to fully
understand his justification for the framework; just
get a sense of how it's applied.

Note that almost everywhere in this package,
we either *must* be lazy or *must* be strict
to maintain the desired space and time bounds.
There isn't a lot of wiggle room.
