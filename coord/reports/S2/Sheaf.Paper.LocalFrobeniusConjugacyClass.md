## What changed

Added proof-local irreducibility attributes for the large local point/operator
constructions, so endpoint transport does not expand their underlying derived data.
These attributes have local scope and leave all definitions unchanged.

Replaced the hole in `WeilConjectures.localFrobeniusConjugacyClass` with a Lean reduction
along the source's Frobenius orbit. The public statement and public imports are unchanged.

The proof now constructs the compatible embeddings `gamma^i.comp iota`, checks the
semilinear point square by both fibre-product projections, obtains the endpoint exponent
from the proved source-library finite-field lemmas, composes the adjacent isomorphisms
by induction, and applies the coefficient cohomology functor to the resulting equation.
The geometric-power indexing reverses the one-step point square; this is handled
explicitly, rather than treating geometric Frobenius as a k-linear point map.

Added `Sheaf.Paper.LocalFrobeniusStepCompatibility`. Its one-step map is an explicit
composite of the existing point transport, the two specified pullback compositors, the
equality of scheme maps, and the pulled-back Weil structure. Its invertibility is proved
from `frobeniusCohomologyTransport_isIso` using the auxiliary identity model `Spec k_0`;
no separatedness hypothesis is added to the item. The one remaining local compatibility
calculation has its own theorem and DAG node with a full proof in words.

This is a decomposition, not a complete proof without new obligations. The new theorem
only compares consecutive semilinear points with specified returns. It does not quantify
over residue embeddings or cohomological degrees, prove orbit transitivity, or assert
the original existential conjugacy conclusion. The parent contains the field-theoretic,
scheme-theoretic, categorical induction and cohomology assembly in Lean.

## Proved and sorry left

Closed the original hole in `WeilConjectures.localFrobeniusConjugacyClass`
(node `lem-weil-local-frobenius-conjugacy-class`) by reduction.

Added one hole: `WeilConjectures.localFrobeniusStepCompatibility`
(node `lem-weil-local-frobenius-step-compatibility`), in its new module. This is exactly
one public theorem with `:= by sorry`; no data is chosen from this theorem.

Proved the compatibility of every geometric-power residue embedding, its one-step
semilinear scheme equation, invertibility of the explicit one-step map, the induction
composing all adjacent conjugacies, and the final cohomological equation. The item
module has zero remaining holes. Net holes closed minus holes added: 0 (decomposition).

Both delivered modules compile through the required server compiler. The step module
compiled in the sandbox import-order check; the final item version compiled with exit
code 0 in 10.4 seconds. No compiler warnings remain. The original theorem signature
was also compared textually and is unchanged; both files satisfy the 100-column limit.

## No longer needed

Removed the item's private imports:

- `Sheaf.AlgebraicGeometry.ClosedPointField`
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`
- `Sheaf.Paper.CoefficientCohomologyModules`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.IntegralPullbackComposition`
- `Sheaf.SixFunctors.FrobeniusPointTransport`
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`

The first six are available through the retained public import
`Sheaf.Paper.LocalFrobeniusTrace`. The last module is privately imported by the new
step module for its proved invertibility helper; naturality and composition coherence
remain obligations of the new node, not unused mathematics. No module is withdrawn,
and no globally pruned module is claimed.

The parent's direct proof dependencies on `lem-pod-integral-pullback-composition`,
`def-weil-derived-pullback-tensor-hom`, `def-weil-frobenius-point-transport`,
`lem-weil-frobenius-point-transport-natural`, and
`lem-weil-frobenius-cohomology-transport-iso` are replaced by the one-step node.
They remain needed underneath it or the local-operator definitions. Removed the parent's
stale `tool_uses` entries `lem-weil-frobenius-cohomology-transport-iso`,
`lem-weil-frobenius-point-transport-natural`, and `lem-pod-integral-pullback-composition`;
only its directly used closed-point-field approval remains. The new source
import `WeilConjectures.Mathlib.FieldTheory.Finite.Basic` supplies already proved
finite-embedding and geometric-power lemmas; no new finite-field hole is introduced.

## Where the brief, the DAG or earlier work was wrong

The current blueprint moved this lemma to
`sec-poincare-duality/sk-thm-frobenius` and its source text now also mentions algebraically
closed coefficients. The assigned finite-field-coefficient theorem is preserved exactly;
this delivery does not claim the additional coefficient generality. The saved DAG's
expanded argument is used to make precise the current blueprint's single sentence
asserting one-translate intertwining. The stored unit route and its realized nodes are
unchanged; this item is not a realized unit step.

The original proof dependencies do not directly state the required compatibility of
the explicitly specified return operator with one moving-point transport. The new
local theorem isolates that calculation. Its proof is sourced from the current
blueprint and expanded DAG steps 2--6, not an arbitrary isomorphism assumption.

Checked the mathematical edge cases: zero point complexes, zero cohomology, return
length one, residue degree one, identical embeddings, and a nonzero orbit exponent.
The one-step statement uses a positive return exponent `n+1`; it has no exceptional
zero-length return. Scheme-map equality proofs are irrelevant, so the return witnesses
used by the parent match those in `localClosedFrobenius`.

The transport and compositor theorems are generic tools already approved for the
original node. Their use moves to the new local node; it does not bypass a finiteness,
duality or trace-formula unit. `lem-trf-local-frobenius-conjugacy` concerns finite torsion
coefficients with a separated model and different local operators, while
`lem-trf-local-frobenius-transport-normalization` compares a rational-point operator
with scheme-Frobenius normalization. Neither states the new one-step equation for
arbitrary semilinear point maps at rational coefficients.

## New nodes

`lem-weil-local-frobenius-step-compatibility`, in
`dag/nodes/sec-poincare-duality/`, records the explicit one-step map, its invertibility,
and its equality with the equal-length return operators. It carries the source,
three kinds of logged Mathlib searches, the local cyclic-product proof and its
existing dependencies, and the attachment to
`Sheaf.Paper.LocalFrobeniusStepCompatibility`. There are no statement or definition
changes to existing declarations, no forced adaptations, and no change record is needed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
