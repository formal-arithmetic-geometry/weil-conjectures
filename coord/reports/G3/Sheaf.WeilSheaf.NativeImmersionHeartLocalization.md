## What changed

Proved the three theorems of `Sheaf.WeilSheaf.NativeImmersionHeartLocalization` without
changing their statements. The coefficient comparison is a specialization of the canonical
coefficient cocycle to the two Frobenius squares. Exactness and constructibility use existing
native instances and native constructibility theorems. The open adjunction is the concrete
`IsoAlgebra.mapOfNatIsoLeftAdjunction` construction already used privately in
`NativeBasicComparisons`; its unit and counit carriers and those of the closed adjunction are
identical to the ordinary adic maps. The localization sequence is checked on the open and
closed restrictions, then reflected using preservation of kernels, cokernels and homology
and joint detection of zero objects. The categorical argument is factored into proved private
helpers in the same module. A private Frobenius-square specialization uses the general
coefficient cocycle. Geometric-fiber, geometric-fiber-map and geometric-Frobenius definitions
are locally irreducible after the generic calculation: otherwise checking its specialization
unfolds the base-change constructions and times out. Proof-only imports expose a commutative-ring Grothendieck-abelian shortcut and alternate
ULift/algebraic-closure ring instances. Their priorities are locally lowered to match the
public imports: the mismatched instances otherwise force expensive sheaf-functor conversions.
No upstream attribute changes. Updated the existing node's proof to describe this route.

## Proved and sorry left

Closed these three original holes:
- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersion_coefficientComparisons`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersion_exact_constructible`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersionHeartLocalization`.

All three realize `lem-sf-native-weil-immersion-heart-localization`. No holes added or split
off; zero `sorry` remain in the item. Private helpers are fully proved. Existing dependencies
are used with their actual native objects; their remaining upstream holes are unchanged.

## No longer needed

Removed these proof imports:
- `WeilConjectures.WeilSheaf.Category` (already public through the required API).
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.EquivalenceAdjunctionComparison`.
- `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction` (through the left lift).
- `Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible`.
- `WeilConjectures.SixFunctors.ProEtale.Adic.Constructible` (through existing native APIs).
- `WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero` (through existing native APIs).
- `Sheaf.Paper.SfClosedPartitionModuleTest`.

The proof no longer needs these declared dependencies as separate steps:
`lem-weil-pbc-open-immersion-base-change`, `lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-qcqs-morphism-permanence`, `lem-wf-affine-noetherian-components`,
`lem-weil-proetale-isomorphism-inverse-image`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-sfb-equivalence-square-inverse-mate-coherence`,
`lem-sf-native-adic-qcqs-stratification`, and `lem-sf-closed-partition-module-test`.
The native constructions already supply the geometric base-change instances and adjunctions;
closed constructibility has a direct, proved native API. No new reindexing, coefficient-category
comparison, equivalence comparison or global stratification argument is required here.
Their old tool approvals were removed from this node where no longer used. This is local
pruning of the item's route, not a claim that no other node or upstream declaration needs them.
The native open-exact-constructible node remains in the proof route as the source of that
conclusion, but its wrapper module is unnecessary since the native declarations suffice.
The ring-sheaf open-closed sequence node remains as the mathematical localization input, used
through its proved native specializations in the source library rather than the alternate
ring-module wrapper.

## Where the brief, the DAG or earlier work was wrong

The old proof plan is mathematically usable but repeats constructions already available in the
source library. In particular the open adjunction can be lifted from the equivariant comparison
`j_! -> j_*` and its transpose formula, without identifying a new mate by sectionwise reindexing.
Closed direct-image constructibility is already proved in `Adic.ClosedLowerStar`, so it needs no
new comparison with the finite-coefficient closed-partition module test. The unit record has no
realized step on this node that is bypassed; the sheaf-heart localization route is retained.
Validation: the complete module compiled in 17 seconds, and the delivery axiom probe found
no disallowed axioms. The unused complement hypothesis is destructured in the coefficient
proof, preserving its signature while satisfying the variable linter.

No statement or definition was changed, and no new nodes or axioms were introduced.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
