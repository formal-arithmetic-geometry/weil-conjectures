/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.PoincareDuality.Biduality.Constructible
import WeilConjectures.PoincareDuality.Biduality.Reduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-! # Geometric Verdier biduality for constructible sheaves

This is the sheaf case, before the separate formal finite-truncation argument.
The target of the structure morphism is required to be isomorphic to the base point.

## Implementation details

Since `S ⟶ Spec k` is an isomorphism, it is an open immersion, so `Ra^! ℚ̄_ℓ` is the dualizing
complex `ω_X` relative to `Spec k`. The statement is then constructible Verdier biduality
`isIso_verdierBiduality` for the sheaf placed in degree `0`, read in the ambient derived
category through the inclusion of the bounded constructible complexes.

## References

* Bhatt--Scholze, Lemmas 6.7.13, 6.7.18--6.7.20 and Propositions 6.8.14, 6.8.15
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- The geometric sheaf case of Verdier biduality for condensed algebraic-closure
coefficients. The hypothesis that S maps isomorphically to Spec k excludes a singular
relative base. The sheaf need not be lisse or locally free on the whole scheme. -/
theorem isIso_biduality_constructible_sheaf [IsIso S.hom] (a : X ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hM : IsConstructibleModuleObject _ M) :
    IsIso (toIhomIhom
      ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let := boundedConstructibleBraiding (ℓ := ℓ) X
  let K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
    ⟨_, boundedConstructible_singleFunctor_zero_obj _ M hM⟩
  have : IsOpenImmersion (Over.mkIdTerminal.from S).left := by
    rw [Over.mkIdTerminal_from_left]
    infer_instance
  let e : (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _) ≅ dualizingComplex ℓ X :=
    (boundedConstructibleUpperShriek ℓ a).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ (Over.mkIdTerminal.from S)).symm ≪≫
    upperShriekDualizingComplexIso ℓ a
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have hd (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      IsIso (dualComparison ι (W := dualizingComplex ℓ X) e.inv.hom A) := by
    have : IsIso ((Functor.LaxMonoidal.ihomComparison ι A).app (dualizingComplex ℓ X)) := by
      rw [ObjectProperty.ihomComparison_ι_app]
      exact IsIso.id _
    unfold dualComparison
    infer_instance
  have := hd K
  have := hd ((ihom K).obj (dualizingComplex ℓ X))
  have : IsIso (toIhomIhom (dualizingComplex ℓ X) K) := isIso_verdierBiduality ℓ K
  exact (isIso_map_toIhomIhom_iff ι (W := dualizingComplex ℓ X) e.inv.hom K).1 inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
