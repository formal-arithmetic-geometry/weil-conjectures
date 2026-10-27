## What changed

Proved `AlgebraicGeometry.ProEtale.SpPurityReduction.pullback_level_bounds` from an
explicit finite evaluation isomorphism, a proved finite-ring pullback theorem,
and the strictly smaller ordered-line tensor calculation.

Added the proved private helper `finite_constant_pullback_bounds` and its proved
private comparison helpers in the item module, by adapting the existing
`sf_pullback_torAmplitude` proof to arbitrary finite constant rings and the existing bounded-constructible
predicate. This proves preservation directly at the ell-power quotient; no
coefficient transport is needed. The proof uses the existing finite-ring derived
origin, etale constructibility comparison, canonical pullback square, comparison
Tor equivalence, and etale inverse-image flat-model argument.

Added `Sheaf.Paper.OrderedLineLevelBounds`, which states only the remaining tensor
calculation for an arbitrary finite-coefficient derived object. The item proof
first applies the proved pullback theorem, then composes inverse levelComparison,
the evaluated realization counit, tensorEvaluation, pullEvaluation and the
input levelComparison. The resulting isomorphism identifies the actual target
with the ordered-line tensor. Constructibility is transported via homology and
constant-scalar restriction; Tor amplitude is transported directly from its
quantified representative definition. All existing signatures and public imports
are preserved. Updated the item node's proof and dependency list, and added a node
for the ordered-line theorem.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.SpPurityReduction.pullback_level_bounds`
(node `lem-sp-purity-pullback-level-bounds`): a complete Lean proof combining the
finite pullback theorem, the ordered-line calculation, and the specified
realization/evaluation isomorphisms.

Additional private helper proved: `finite_constant_pullback_bounds`: zero sorry.
Its private comparison helpers are also proved. The current blueprint already
states finite-ring pullback preservation, so no duplicate public statement or
new node is introduced for this helper.

One new hole remains:
`AlgebraicGeometry.ProEtale.SpPurityReduction.ordered_line_level_bounds`
(node `lem-sp-ordered-line-level-bounds`), in its own module, with exactly
`:= by sorry`. It is the tensor/shift part of the existing plan. It has no
morphism, no strict-tower input K, no inverse realization and no pullback. Its
input is an arbitrary single finite-coefficient object, so it cannot directly
restate the original obligation. The docstring supplies the induction, base
case, rank-one trivialization, evaluation comparisons and shift computation.
The cases d=0, n=0, equal endpoints and zero input were checked mathematically.

Counts: one original hole closed, one hole added, zero holes in the item module.
This is a decomposition with the entire finite pullback and coordinate-transport
parts proved; net holes closed minus added is zero. It is not reported as a net
hole reduction. No axioms or hollow definitions are introduced.

Validation: the first remote `--all` compile succeeded for both modules.
The unused `haz` warning was repaired by supplying it explicitly as the ordered
interval component of the Tor hypothesis. Final remote compilation and delivery
preflight are recorded by the delivery tool.

## No longer needed

No existing public imports removed; the existing SmoothPurityTowerGamma import
is retained for the definitions used by the statement. No module is withdrawn.
The proof uses only definitions from the gamma module, never its tower purity
or normalization theorem.

The item no longer uses these declared proof dependencies directly:

- `lem-sf-pullback-tor-amplitude` / `Sheaf.Paper.PullbackTorAmplitude`: the proved
  arbitrary finite-ring version uses the same existing comparison and flat-model
  argument directly at R_n, avoiding uniformizer-quotient transport.
- `sk-def-sp-coefficient-towers`: the cofinality calculation is unnecessary for
  the pullback step. This remains a dependency of the unresolved Tate-line
  calculation and stays in the statement closure.
- `prop-weil-twist-preserves` / `Sheaf.Paper.TwistPreservesFiniteness`: needed by
  the smaller ordered-line node's mathematical proof, not applied directly in
  the item module.
- `def-sbc-smooth-morphisms`: smoothness is retained in the unchanged signature,
  but finite constant-ring inverse image does not need it.
- `sk-def-sp-normalized-towers`: remains a statement dependency for the bounded
  finite-level predicate, rather than a direct proof dependency of the item.

No claims are made that the above modules are globally unreachable: the line
calculation and other consumers still need some of them. No unit statement or
realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

There is no disputed statement or source error. The planned pullback proof's
uniformizer transport is unnecessary: its existing proof is valid for every
finite constant ring. This matches the newest blueprint statement of
lem-sf-pullback-tor-amplitude under sec-proetale-coefficients, read with its
complete proof. The older recorded Lean signature is still restricted to
uniformizer coefficients; the generalization is used only as a private helper.
The ordered-line tensor API is not given by the cited
finite-twist preservation theorem verbatim, because it uses the supplied
levelClosed tensor and an ordered product of evaluated shifted factors.
That remaining model comparison and induction is now stated separately.

The new ordered-line node cites definition nodes for the tower unit and Tate
data, not the theorem node det-sp-tower-gamma: using that theorem would be
circular through its unfinished purity-conjugacy proof. Only its explicit
orderedLine construction is used in Lean. The combined overlaid node graph was
checked for a path back to each changed/new node; none was found.

## New nodes

`lem-sp-ordered-line-level-bounds` attaches the remaining ordered-line tensor
calculation in `Sheaf.Paper.OrderedLineLevelBounds`. Its source is the twist part
of gamma proof (3). It is strictly the final tensor step of the original argument,
independent of the now-proved geometric pullback and realization cancellation.

For the new node, Mathlib searches ran through msearch (LeanSearch, LeanFinder,
Loogle and grep), and local searches inspected the existing pullback, twist,
chart-domain, Tor-transport and evaluation interfaces. Blueprint searches for
"Tate line Tor amplitude" and "pullback Tor amplitude" found zero exact matches.
No change record is needed: all existing declarations and definitions retain
their signatures and bodies outside the item's theorem proof and proof imports.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
