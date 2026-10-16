/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Formalism

/-!
# K-injective models of the derived limit of a tower

Let `A` be a Grothendieck abelian category and `I` a K-injective complex of towers in `A`.

* `DerivedCategory.isHomotopyLimit_mapCone_limConeAsFunctor`: the termwise limit `lim I`, with
  its projections, is a derived limit of the inverse system of complexes `(Iₙ)ₙ` viewed in
  `D(A)`; in particular `Q (lim I)` represents `R lim (Q I)`.
* `DerivedCategory.isLimitFanTowerFunctor`: the termwise product `∏ₙ Iₙ` represents the
  product `∏ₙ evₙ (Q I)` in `D(A)`.
* `DerivedCategory.rlimModelIso`: for any functorial K-injective resolution `η : 𝟭 ⟶ ι` of
  complexes of towers, `K ↦ Q (lim (ι K))` is isomorphic to `K ↦ R lim (Q K)`; so any two
  functorial K-injective resolutions give isomorphic models of `R lim`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- **Blueprint `prop-weil-pbc-derived-inverse-limit-computation`**, also
**Blueprint `lem-weil-derived-limit-existence`** (assertion 3). If `I` is a K-injective complex
of towers (for instance a K-injective resolution of `M`), then the termwise limit `lim I`, with
its projections to the levels `Iₙ`, is a derived limit of the inverse system `(Iₙ)ₙ` of `D(A)`:
`Q (lim I)` represents `R lim (Q I)` (see also `DerivedCategory.rlimObjQIso`). -/
theorem isHomotopyLimit_mapCone_limConeAsFunctor (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] : IsHomotopyLimit (Q.mapCone (limConeAsFunctor I)) :=
  (isHomotopyLimit_rlimCone (Q.obj I)).of_iso (towerFunctorObjQIso I) _ (rlimObjQIso I)
    fun n ↦ by
      rw [Functor.mapCone_π_app]
      exact rlimCone_π_app_Q_obj I (op n)

/-- **Blueprint `prop-weil-pbc-derived-product-representation`**. For a K-injective complex of
towers `I`, the termwise product `∏ₙ Iₙ` of its levels represents the derived product
`R∏ₙ evₙ (Q I)`, the product in `D(A)` of the evaluations of `Q I`. -/
noncomputable def isLimitFanTowerFunctor (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    IsLimit (Fan.mk (Q.obj (∏ᶜ fun n : ℕ ↦ I.asFunctor.obj (op n))) fun n ↦
      Q.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n) ≫
        (towerFunctorObjQIso I).inv.app (op n) :
      Fan fun n : ℕ ↦ ((towerFunctor A).obj (Q.obj I)).obj (op n)) := by
  have h := isLimitFanQOfIsKInjective (productIsProduct fun n : ℕ ↦ I.asFunctor.obj (op n))
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv
    (Discrete.natIso fun n ↦ ((towerFunctorObjQIso I).app (op n.as)).symm) _).symm h)
    (Fan.ext (Iso.refl _) fun n ↦ ?_)
  simp only [Iso.refl_hom, Category.id_comp]
  rfl

section Model

variable (ι : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
  (η : 𝟭 _ ⟶ ι) [∀ K, QuasiIso (η.app K)] [∀ K, (ι.obj K).IsKInjective]

/-- The unit of `R lim` restricted along a functorial K-injective resolution `ι`. -/
noncomputable def rlimModelHom :
    ι ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex _ ⋙ Q ⟶ ι ⋙ Q ⋙ rlim A :=
  Functor.whiskerLeft (ι ⋙ HomotopyCategory.quotient _ _)
      ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnit) ≫
    Functor.whiskerLeft ι (Functor.whiskerRight (quotientCompQhIso _).hom (rlim A))

instance : IsIso (rlimModelHom ι) := by
  have (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso ((rlimModelHom ι).app K) := by
    dsimp [rlimModelHom]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **Blueprint `prop-weil-pbc-rlim-functoriality`** (independence of the model). For any
functorial K-injective resolution `η : 𝟭 ⟶ ι` of complexes of towers, the functor
`K ↦ Q (lim (ι K))` is naturally isomorphic to `K ↦ R lim (Q K)`. Hence it descends to the
triangulated functor `R lim : D(ℕᵒᵖ ⥤ A) ⥤ D(A)` (`DerivedCategory.rlim`, triangulated by
`Functor.rightDerivedFunctor`), and any two choices of functorial K-injective resolutions give
isomorphic functors. -/
noncomputable def rlimModelIso :
    ι ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex _ ⋙ Q ≅ Q ⋙ rlim A :=
  asIso (rlimModelHom ι) ≪≫
    NatIso.ofComponents (fun K ↦ ((rlim A).mapIso (asIso (Q.map (η.app K)))).symm)
      fun f ↦ by
        dsimp
        simp only [← Functor.map_comp]
        congr 1
        rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Q.map_comp, ← Q.map_comp]
        exact congr_arg Q.map (η.naturality f).symm

end Model

end DerivedCategory
