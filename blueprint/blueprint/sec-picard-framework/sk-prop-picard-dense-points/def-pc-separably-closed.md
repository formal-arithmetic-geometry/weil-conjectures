+++
id = "def-pc-separably-closed"
kind = "definition"
title = "Separably closed fields"
order = 747
+++
A field $k$ is *separably closed* if every nonconstant separable
polynomial $f\in k[T]$ has a root in $k$ (equivalently, $k$ has no
nontrivial finite separable field extension; the equivalence of the two
formulations is [lem-pc-sepclosed-finite-sep-trivial]).

*Implementation note.* This is the same notion as [def-kun-separably-closed],
which carries the Lean name `IsSepClosed`. Mathlib's `IsSepClosed k` is stated in
the polynomial form used here: every separable polynomial over $k$ splits. The source
attached `\lean{IsSepClosed}` to the pointer remark
[rem-ptr-pc-separably-closed-1], a fragment left over from splitting this
definition.
