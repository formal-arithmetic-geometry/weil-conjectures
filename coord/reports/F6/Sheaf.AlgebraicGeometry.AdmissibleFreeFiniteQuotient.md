## What changed

Preserved both action-relation definitions and the complete public signature of
`AlgebraicGeometry.exists_admissible_free_finite_quotient`. Replaced its sorry by
an explicit proof from the new invariant-affine presentation lemma.

The proof constructs invariant affine neighborhoods by finite intersection of
translates in the separated scheme, descends finiteness along the quotient's own
fpqc cover, and descends separatedness along its finite surjection. Private proved
helpers establish singleton fppf sheaf descent, the presheaf-coequalizer universal
property, the base-changed relation square, and factorization of field points
through a single coproduct summand. Sheaf separatedness on the coproduct's open
cover handles invariant maps on disconnected test schemes. These yield every
remaining clause, including arbitrary base change and quasi-compactness.

Added `Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotientPresentation`: its
single theorem isolates the scheme construction from a supplied invariant affine
cover. Its conclusion asserts only an etale surjection with the specified kernel
pair. Its source and complete construction argument are in its docstring and
node. No definitions contain sorry; no existing public interface changes.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.exists_admissible_free_finite_quotient`
(node `lem-sfb-admissible-free-finite-quotient`) by a complete Lean proof from
the new presentation theorem and existing declarations. There are zero sorries
in the item module.

Added one hole:
`AlgebraicGeometry.exists_admissible_free_finite_quotient_presentation`
(node `lem-sfb-admissible-free-finite-quotient-presentation`). Its proof is exactly
`by sorry`. This is a decomposition, not a net proof: one original hole closed,
one strictly narrower construction hole added, net zero. The construction lemma
requires a supplied invariant affine cover and does not assert finiteness,
separatedness, sheaf universality, arbitrary base change, geometric orbit fibres,
or quasi-compactness; these are proved in the item rather than repackaged into
its hypothesis. All private helper theorems are proved.

## No longer needed

The general invariant-affine shrinking theorem
`lem-sfb-locally-free-groupoid-invariant-affine`
(`Sheaf.AlgebraicGeometry.LocallyFreeGroupoidInvariantAffine`) is unnecessary on
this route: finite intersections of translates suffice because M is separated.
The generic quotient descent theorem
`lem-a1-fppf-kernel-pair-quotient-descent`
(`Sheaf.AlgebraicGeometry.FppfKernelPairQuotientDescent`) is unnecessary: singleton
sheaf gluing and the coequalizer universal property are proved directly here.
Neither node is used by the new presentation construction.

Removed the following proof imports from the item:

- `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
- `Sheaf.AlgebraicGeometry.GroupoidScheme`
- `Sheaf.AlgebraicGeometry.EtaleRelationQuotient`
- `Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient`
- `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`
- `Sheaf.AlgebraicGeometry.FppfKernelPairQuotientDescent`

The construction dependencies (groupoid, affine quotient, etale relation quotient,
finding opens, and scheme representability) remain in the new node's proof plan;
these are relocated, not claimed as pruned. The source/target etaleness properties
also remain a construction dependency. FiberDegree's finite-locally-free API is
not needed by the main proof: the proved finite coproduct instance is imported
from `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite` instead.

The main node no longer needs separate finite-morphism permanence or etale-base-
change nodes for its base-change sheaf clause: the proof uses the elementary
pullback construction and the fppf-cover instances directly. No modules are
withdrawn or source-library declarations removed. No claim is made that the
above nodes are globally unreachable through other parents.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original general groupoid
shrinking step is stronger than needed for separated schemes. The quotient
kernel-pair descent declaration is stated over `Over S`, whereas the item asks
for absolute `uliftYoneda` and all larger sheaf universes. Rather than change that
shared interface, the proof establishes the needed absolute sheaf descent from
Mathlib's singleton sheaf axiom.

The new statement was checked on the empty scheme, trivial group, disconnected
tests and arbitrary finite-group universe. It uses no choice of arbitrary data
from an admitted existence theorem in a definition. The inherited unit and
chapter route stay unchanged. The latest blueprint and its direct-image proof
were read; blueprint searches for `finite flat equivalence` and `07S6` gave no
matching blueprint declaration, and the ancestor tool returned None, consistent
with the inherited null ancestor and recorded supporting-input chain.

## New nodes

`lem-sfb-admissible-free-finite-quotient-presentation`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-admissible-free-finite-quotient-presentation.json`,
states the invariant-affine construction step from Stacks 07S6 and attaches its
single new Lean module and declaration. The parent node's proof, dependencies
and origin now follow the actual Lean proof. The affine construction dependencies
are generic tools already approved for the parent's construction, not a bypass
of any unit step. No change record is needed: no existing statement, definition
or other module is changed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
