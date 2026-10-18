## What changed

Proved `AlgebraicGeometry.Scheme.adicReductionAdjunction_homEquiv_exists` in
`Sheaf.Paper.AdicCompletionReduction`. The proof uses the existing, fully proved generic
ordinary and derived adjunction helpers from
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, together with
`derivedChangeOfRingsGeneral` and `exists_isKFlatResolutionGeneral`.

The transported Hom equivalence uses the chosen K-flat realization. The proof identifies
its ordinary complex unit with `adicReductionAugmentation` by that augmentation's uniqueness
and local tensor formula, then proves the derived comparison diagram. This establishes the
specified unit formula, rather than merely an unspecified adjunction.

Added proof-only imports of the generic adjunction helpers and K-flat resolutions. Scoped
instance exclusions prevent the imported specialized coefficient-universe site-size instance
from interfering with the existing proofs. No signature, definition body, target, or
visibility changed. Updated the Hom-equivalence node and the parent node to record the Lean
proof route; the remaining restricted node still carries the Koszul calculation.

The module compiled without errors or warnings after pruning (29.1 seconds).
The scoped-command change record requested by static preflight is
`coord/changes/D4-adic-reduction-adjunction-proof-scope.md`; downstream analysis reports zero
source consumers and no adaptations are needed.

## Proved and sorry left

Closed one of the module's two holes:

- `AlgebraicGeometry.Scheme.adicReductionAdjunction_homEquiv_exists`
  (`lem-weil-pbc-adic-reduction-adjunction-hom-equiv`).

One original hole remains, unchanged:

- `AlgebraicGeometry.Scheme.adicCompletionReduction_restricted_isIso`
  (`lem-weil-pbc-adic-completion-reduction-restricted`). Its remaining work is the bounded
  perfect coefficient comparison with the product-cone model, the reduced Koszul tower's
  constant/pro-zero splitting, and identifying the resulting map with evaluation's adjoint.

Added zero holes; split off zero theorems. This is a proof of the scalar-adjunction hole from
existing declared dependencies, not a decomposition. The whole target theorem still depends
on the remaining restricted calculation and on existing dependency holes.

## No longer needed

Removed these ten direct imports:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Mathlib.Algebra.Homology.DerivedCategory.KProjective`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The ordinary pullback/pushforward adjunction and general derived-adjoint interfaces
(`lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-pc-derived-adjoint-functors`) are not used
by the new Hom-equivalence proof: their required constructions are already proved in the
generic scalar-adjunction helpers. Removed their direct proof-dependency edges from that node
and the parent, and removed the parent's obsolete
`lem-pc-derived-adjoint-functors` tool-use entry. Statement dependencies are unchanged.

The K-projective and finite-coefficient derived-tensor imports were unused. The independent
coefficient and perfect-ring imports were redundant through retained interfaces. The Sheaf
`DerivedLimitProducts` file is a retired re-export; the source-library module remains.

The Koszul, strict-perfect coefficient, exact countable-product, and strict tower-limit imports
are retained for the original remaining restricted-calculation plan. Its nodes are not claimed
pruned. No module was withdrawn and no global unreachable-module count is claimed.

## Where the brief, the DAG or earlier work was wrong

The scalar-adjunction interface was already proved generically inside another module. Its
private proof helpers handle independent site and coefficient universes and can be reused
with a proof-only `import all`; no new abstract adjunction theorem is needed.

The current attachment of `lem-pur-derived-change-of-rings` names
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, whose source file is absent from this
shared checkout. The existing `DerivedChangeOfRingsGeneral` declaration is present, compiled,
and sufficient for this proof, so no duplicate interface was introduced.

For the remaining hole, the listed strict-perfect package supplies splittings and bounded
representatives, rather than the required tensor/product-cone comparison itself. A scratch
check proved product preservation for a bounded complex of dualizable terms from its explicit
dual adjunction; it was not delivered because connecting that generic calculation to the
specified constant quotient and Koszul evaluation still requires the remaining argument.

The source-library `Complete.TensorQuotPow` and `Complete.AdicTower` results require a
principal ideal generated by a nonzerodivisor, and use ordinary module-valued sheaves.
They cannot supply the remaining general finitely generated-ideal calculation directly.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
