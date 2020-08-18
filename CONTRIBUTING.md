## Path to contribution

I recommend that potential contributors start by
getting to know `Data.CompactSequence.Stack.Internal`.
The basic operations there require considerably
less code than those for the other structures, so
it's easier to understand how they interact with
the debit invariant. The other structures work
according to exactly the same principles, but with
a lot more moving parts.

Speaking of debit invariants, contributors who want to really
dig into the deep guts of these implementations should be somewhat
familiar with Okasaki's debit analysis framework.
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
There's a little wiggle room in some places, but
not terribly much.
