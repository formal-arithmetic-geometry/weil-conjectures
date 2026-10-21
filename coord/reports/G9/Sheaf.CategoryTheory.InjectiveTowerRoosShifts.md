## What changed

Filled `CategoryTheory.injectiveTowerRoosShifts` in
`Sheaf.CategoryTheory.InjectiveTowerRoosShifts`, preserving its public signature
and the four existing public constructions. All supporting declarations are proved
private helpers in the same module. No definition chooses an arbitrary object
from an unproved existence statement.

The injective-transition, kernel and recursive-section arguments reuse the proved
private arguments of `RingedStrictTowerHomotopyLimitIndependentCoefficients`.
The product and signed-cocone shift construction reuses the generic private
shift arguments of `RoosConeCalculus`, specialized here to the actual product,
limit and Roos functors. Both source modules remain unchanged. The forward
coordinate identity determines the inverse through a biproduct isomorphism.
The boundary sign is proved on its insertion cochain before localization, then
transported through Q and the augmentation isomorphism. The final representative
isomorphism is constructed directly from the supplied unit on K-injectives and
RF(Qq).

Added proof-only imports of `ProductCommShift`, `SignedMappingCoconeShift`, and
Mathlib's evaluation adjunction. Updated the existing node's proof, proof_deps,
proof_origin and obsolete tool_uses to describe this route. No other module or
public signature or definition is changed. The added proof-only namespace,
variable and local-attribute commands are documented in
`coord/changes/G9-injective-tower-roos-shifts-proof-scope.md`.

Before the instance-scope cleanup, the complete module compiled without warnings
in 28.6 seconds. The additive-limit proof is now registered only locally in
`section LimitModel`; the final delivery recompiles this scope cleanup.
`#print axioms CategoryTheory.injectiveTowerRoosShifts` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed `CategoryTheory.injectiveTowerRoosShifts`
(node `lem-pur-injective-tower-roos-shifts`): one original hole, zero added holes,
zero split-off statements. The completed proof text has no `sorry`.
No `sorry` remains in the item, and no holes were added elsewhere.

## No longer needed

Removed proof-only imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the theorem
  starts with the chosen representative and its hypotheses; no new resolution is
  constructed.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  its generic private elementary arguments are reproduced with proofs, and the
  supplied unit η gives the required derived-limit normalization directly.
- `WeilConjectures.CategoryTheory.KInjectiveBridge`: the required naturality is
  for strict chain maps and is proved before and after localization directly.
- `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor`: no homotopy descent is needed
  for the stated strict-map naturality clause.
- `Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus`: the already
  proved signed cocone construction supplies the shifts directly.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: the final unit's
  invertibility is already an explicit hypothesis.

The proof no longer uses nodes `def-sp-kinjective-bridge`,
`lem-pe-endomorphism-fibre-coordinate-calculus`,
`lem-pur-strict-roos-homotopy-functor`,
`lem-weil-pbc-kinjective-hom-derived`, or
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` as proof dependencies.
The corresponding obsolete top-level tool_uses entries were removed, preserving
all remaining entries and their order. Existing statement dependencies are
preserved. No module is withdrawn; other consumers and source-library
public declarations are untouched.

## Where the brief, the DAG or earlier work was wrong

The generic proof-only dependencies for homotopy descent and a separate derived
limit calculation are stronger than this Lean statement needs: it asks for
naturality for strict maps, and explicitly assumes η is invertible at K-injective
representatives. The direct normalization argument retains the required equation
with q. The mathematical statement is unchanged; no disputed or weakened lemma
is used. Zero complexes, zero coefficients and all integer shifts are covered by
the generic abelian-category constructions and the coherent CommShift laws.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
