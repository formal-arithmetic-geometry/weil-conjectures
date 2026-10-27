## What changed

Factored the native supported-Hom operations and their unchanged law predicates
into `Sheaf.Paper.SupportedCupFunctorialityModels`, publicly reexported by the
original module. The factoring supplies a common interface for the independent
native algebra and site-comparison results, avoiding an import cycle.

The original theorem now combines those two results with a direct Lean proof
of all four localization clauses. The proof identifies the full-support
restriction with the inverse direct-image unitor; applies exact-functor
naturality to restriction and open inclusion; constructs the isomorphism of
actual short exact coefficient sequences; and uses naturality of single-delta
and shifted composition for the boundary. No boundary sign is changed.

The supporting exact-Hom, endpoint and extension realization definitions merely
name the original composites. The selected site is formed before the sheaf
category to share the actual canonical instances.

## Proved and sorry left

Closed the body of
`WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality` by a complete
assembly proof. Its localization clauses are proved in Lean, including the
actual boundary. This is a decomposition of the original one hole, not a
sorry-free proof of all laws.

Added two strictly smaller remaining statements:

- `WeilConjectures.PurityFiniteSetting.supportedCupNativeCoherence`, node
  `lem-pur-supported-cup-native-coherence`: seven coherence/Kummer/pullback laws.
  The four bilinearity fields are proved directly in `supportedCupAlgebra`.
- `WeilConjectures.PurityFiniteSetting.supportedCupComparisonCoherence`, node
  `lem-pur-supported-cup-comparison-coherence`: six operation-comparison laws.
  The three Hom bijections and the forget-support and open-restriction equations
  are proved directly in `supportedCupComparisonBasic`; `supportedCupComparison`
  assembles these with the six remaining equations.

The original module, common models module, native algebra assembly, basic
comparison result and comparison assembly contain zero sorry bodies. The native
coherence and comparison coherence modules contain one named theorem with sorry
each. Thus one upper hole is closed and two lower holes are added. No private helper or definition
contains sorry.

Validation: the full localization proof and its axiom probes compiled in 31 seconds.
The boundary and full-support helpers use only the three permitted standard axioms.
The algebra assembly and comparison assembly also compiled. The integrated check compiled all seven packet modules and the original, unchanged
`ClosedSupportedCupVanishing`. The unchanged `PurityDivisorClass` exceeded the
60-second limit (84 seconds); its profile attributes most kernel time to
`DivisorChern`, `classes_exists`, and `divisor_chern`. No consumer is adapted in
this packet. The model also now factors mapped-kernel normalization through the
proved generic private lemma `normalizedKernelIso_of_exact`; this avoids native
rechecking of mapped short-complex projections. The delivery performs the final
packet compilation and preflight.

## No longer needed

No module or DAG dependency is claimed globally pruned. In particular, the
source-system tensor calculus, Kummer normalization and coefficient comparison
results remain needed by the two explicit remaining obligations. There are no
source-library removals.

The localization proof itself needs none of the former prospective proof-only
imports for twist-local-freeness, site cohomology comparison, K-flat telescope
closure, ringed tensor pullback, supported-Hom normalization, shifted cup
calculus or universal delta functors. Those imports are absent from the original
module. Its proof imports are now only its two assembled results, its models,
identity/direct-image coherence, constant-sheaf normalization, and exact-functor/shift calculus. The category-to-
reflexive-quiver wrapper is locally reducible to keep the same underlying Hom
instances visible to the boundary calculation. The models retain
the imports needed to construct the operations. No withdrawal is requested.
Unused new transport and boundary-composition wrappers
were removed before delivery; they are not retained as extra API.

The following original direct imports are absent from the retained packet:

- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`
- `Sheaf.Paper.SupportedCohomologyHom`
- `WeilConjectures.CategoryTheory.ExtExactFunctorCocycle`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`

These are removals of direct prospective imports, not withdrawals of modules.
The native coefficient, flat tensor and finite Tate constructions use their
already published implementations. The remaining coherence statement retains
the relevant mathematical dependencies; upstream proofs and other consumers may
still need these modules.

The old direct plan edges not used by the replacement argument are
`lem-amb-finite-root-site-comparison`, `lem-amb-finite-tate-site-descent`,
`lem-pur-supported-constant-exchange-normalization`,
`lem-pur-supported-hom-cocycle-normalization`, and
`lem-pur-supported-hom-pullback`. The finite twist/frame endpoint identification
uses the existing definitions. The source exchange is fixed by its epic
restriction, and exact inverse image is normalized directly on the Hom model;
no additional cocycle or resolution-transport interface is used here. No claim
is made that these nodes are unused by other parts of the library.

## Where the brief, the DAG or earlier work was wrong

The DAG's source-system cup calculus is expressed for ringed module sheaves,
whereas the actual operations here are native sheaves with values in ModuleCat.
Its signature therefore cannot simply be applied to close the cup fields. The
remaining native-algebra theorem records precisely that identification and its
coherence; no alternative arbitrary cup operation is substituted.

Repeated Boolean derived-category conversions also occur in the existing
interface. The definition factoring names their actual endpoints and uses the
published normalized Tate-data projections. These changes require independent
semantic review; they do not assert a new mathematical hypothesis.

## New nodes

`def-pur-supported-cup-functoriality-models` records the native common interface.
`lem-pur-supported-cup-native-algebra` assembles the directly proved bilinearity
fields with `lem-pur-supported-cup-native-coherence`, the seven remaining native
coherence/Kummer/pullback clauses of original Steps 1--5 and 8.
`lem-pur-supported-cup-comparison-calculus` combines the proved
`lem-pur-supported-cup-comparison-basic` with the six remaining clauses in
`lem-pur-supported-cup-comparison-coherence` from original Steps 6--8.
Each remaining theorem has its source,
full proof in words, and its own Lean module. The parent node now records the
actual localization proof and assembly.

Change record: `coord/changes/q8-supported-cup-native-model-interface.md`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
