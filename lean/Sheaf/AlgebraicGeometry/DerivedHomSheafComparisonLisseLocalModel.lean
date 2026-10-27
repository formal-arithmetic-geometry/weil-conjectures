/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison
public import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Local model comparison for bounded finite locally constant sources

Source: Stacks Project, Cohomology on Sites, Tags 08JI and 08JA.
(blueprint: lem-weil-pbc-derived-hom-sheaf-comparison-lisse-local-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Etale
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The local finite coefficient model calculation implies the canonical derived Hom
comparison. The remaining argument is the bounded-free RHom calculation on each member
of the etale cover, followed by descent of the canonical map.

Source: Stacks Project, Tags 08JI and 08JA; the finite-source local-model step of
`lem-weil-pbc-derived-hom-sheaf-comparison-lisse`.
(blueprint: lem-weil-pbc-derived-hom-sheaf-comparison-lisse-local-model)

Proof: On each cover member choose the displayed bounded complex of finite modules and
use the bounded-free RHom model. Exact inverse image preserves the finite sums, matrices,
and cohomology of that model. The derived-sections identification by a K-injective target
then identifies the local map with the canonical comparison. The local inverses agree on
pullback overlaps because both are induced by pullback of actual derived maps; descent gives
the global isomorphism.
-/
theorem derivedHomSheafComparison_isIso_of_finite_local_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hD : (DerivedCategory.TStructure.t
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).plus D)
    (hmodels : ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        (∀ n : ℤ, Finite (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj A ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))) :
    IsIso (derivedHomSheafComparison X B A D) := by
  sorry

end AlgebraicGeometry.Scheme
