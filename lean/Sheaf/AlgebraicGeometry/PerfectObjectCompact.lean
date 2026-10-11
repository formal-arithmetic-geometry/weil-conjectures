import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
import Sheaf.CategoryTheory.CompactObject

/-! # Compactness of perfect complexes

Source: Stacks Project, Proposition perfect-proposition-compact-is-perfect (Tag 09M1)
(blueprint: lem-pc-perfect-object-compact).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every perfect object of the quasi-coherent derived category of a quasi-compact,
quasi-separated scheme is compact.
Source: Stacks Project, Proposition perfect-proposition-compact-is-perfect (Tag 09M1)
(blueprint: lem-pc-perfect-object-compact).
Proof: (1) use `lem-pc-perfect-tensor-hom-duality` with the perfect dual of `P` to
identify `Hom(P, M)` naturally with `Hom(𝒪_X, P⁻¹ ⊗ᴸ M)`; (2) use
`lem-pc-kflat-resolution`, `lem-pc-derived-qcoh-direct-sums`,
`lem-pc-derived-ambient-direct-sums`, and `def-pc-tensor-complex-sheaves` to show
that tensoring by this dual commutes with set-indexed direct sums; (3) apply
`lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-derived-direct-image-preserves-direct-sums`, and
`lem-pc-affine-qcoh-derived-equivalence` to the structure morphism
`X ⟶ Spec(ℤ)`, so `Hom(𝒪_X, -)` commutes with direct sums, and conclude by
naturality. The empty family is included.
-/
theorem perfectObjectCompact (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.1 → IsCompactObject P := by
  sorry

end AlgebraicGeometry
