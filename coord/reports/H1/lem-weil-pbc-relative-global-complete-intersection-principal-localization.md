## Worker report

The module states `Algebra.relativeGlobalCompleteIntersection_principalLocalization`.
It binds a commutative ring `R`, natural numbers `n,c`, a family of `c` polynomial
relations `f`, the hypothesis that the quotient by those relations is a relative
global complete intersection, and a polynomial `h`. The first conclusion is the
relative-global-complete-intersection predicate for the quotient of
`MvPolynomial (Option (Fin n)) R` by the `c` renamed relations together with the
new relation `rename some h * X none - 1`; this is the `n+1` variable, `c+1`
equation presentation. The second conclusion provides an `AlgEquiv` over `R` to
`Localization.Away` at the quotient image of `h`, sending each old variable to
its image under the localization algebra map and the new variable to
`IsLocalization.Away.invSelf`.

The dependency declarations used are `MvPolynomial`/`MvPolynomial.rename` and
its evaluation infrastructure from Mathlib, `Algebra.IsRelativeGlobalCompleteIntersection`
from `Sheaf.Paper.RelativeGlobalCompleteIntersection`, and
`Localization.Away`/`IsLocalization.Away.invSelf` from
`Mathlib.RingTheory.Localization.Away.Basic`. The polynomial presentation is
encoded with `MvPolynomial (Fin n) R`; adjoining one variable uses
`MvPolynomial (Option (Fin n)) R` and `Option.elim'`.

Edge cases checked include `n = 0`, `c = 0`, and `h = 0`; the statement remains
well-typed (the localization may be the zero ring) and imposes no extra
nonzeroness assumption. The search via `rg` found no existing project or source
declaration for this node. `msearch.py` searches (LeanFinder, Loogle, grep)
found only Mathlib's generic localization and standard-smooth presentation
results, with no relative-global-complete-intersection theorem. The dependency
nodes' recorded Mathlib/project declarations were inspected directly.

## Earlier second reading (a previous round; superseded)

The hypotheses and both conclusion clauses were checked against the node and
Stacks Tag 00SS(2). The `Option` presentation adds exactly one variable and one
relation `h*y - 1`; the equivalence is over `R` and specifies the images of all
old variables and the new inverse variable. No statement correction or new
nodes are needed.

## Second reading by H1

The node introduces a commutative ring `R`, natural numbers `n,c`, a family
`f : Fin c → MvPolynomial (Fin n) R`, and the hypothesis
`IsRelativeGlobalCompleteIntersection (algebraMap R (MvPolynomial (Fin n) R ⧸
Ideal.span (Set.range f)))`.  The Lean binders render these objects exactly,
with no extra finiteness, noetherian, field, characteristic, or universe hypotheses.
It then introduces `h : MvPolynomial (Fin n) R`; this is rendered by the final
binder.  The first conclusion is the relative-global-complete-intersection
predicate for the quotient of `MvPolynomial (Option (Fin n)) R` by the range of
`Option.elim'` applied to the new relation
`rename some h * X none - 1` and the old relations `rename some (f i)`.  This
adds exactly one variable and one equation and matches the node's `T'`.
The second conclusion is an existential `AlgEquiv` over `R` from that quotient
to `Localization.Away (Ideal.Quotient.mk ... h)`, followed by the two required
clauses: every old variable maps to its localization algebra-map image and the
new variable maps to `IsLocalization.Away.invSelf`.  The quantifier order and
all specified images agree with the node.

The dependency declaration `Algebra.IsRelativeGlobalCompleteIntersection` was
read in `Sheaf/Paper/RelativeGlobalCompleteIntersection.lean`; it is the same
finite-polynomial-presentation and fibre-dimension predicate used by the node.
`MvPolynomial`, `rename`, `Option.elim'`, `Localization.Away`, and
`IsLocalization.Away.invSelf` are the Mathlib notions named by the statement.
No private replacement or extra dependency module is present.

Edge cases are covered: `n = 0` and `c = 0` are allowed by `Fin` and `Set.range`,
`h = 0` is allowed (the localization may be the zero ring), and the quotient
may be zero.  The `Option` type still supplies the single new variable when
`n = 0`; no nonzeroness or characteristic assumptions are introduced.

Independent searches used `msearch.py ... leanfinder` for the theorem name and
relative-global-complete-intersection localization phrases, `rg` over
`WeilConjectures/`, Mathlib, and `lean/Sheaf`, and inspection of the recorded
dependency declaration.  Search results contained only generic localization or
standard-smooth results; no existing theorem or definition states this node.

No mismatch was found, so no source, statement, or module change was needed.
The module compiles cleanly with `scompile.py`; its only proof placeholder is
the required `sorry`.
