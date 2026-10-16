/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Roos
public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.NatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.Functor

/-!
# The sequential derived inverse limit

Let `A` be a Grothendieck abelian category. The category `ℕᵒᵖ ⥤ A` of *towers*
`M₀ ⟵ M₁ ⟵ M₂ ⟵ ⋯` in `A` is again Grothendieck abelian
(`CategoryTheory.Presheaf.isGrothendieckAbelian`), with kernels, cokernels and exactness computed
levelwise. This file defines

* `DerivedCategory.towerFunctor A : D(ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ D(A))`, sending an object `M` of the
  derived category of towers to the inverse system `(evₙ M)ₙ` of its evaluations in the single
  triangulated category `D(A)`, the transition maps being induced by those of the towers;
* `DerivedCategory.rlim A : D(ℕᵒᵖ ⥤ A) ⥤ D(A)`, the total right derived functor of
  `lim : (ℕᵒᵖ ⥤ A) ⥤ A`, together with the natural cone `DerivedCategory.rlimCone A M` of the
  maps `R lim M ⟶ evₙ M`.

The main result is `DerivedCategory.isHomotopyLimit_rlimCone`: `R lim M` is a derived limit
(homotopy limit, `CategoryTheory.Pretriangulated.IsHomotopyLimit`) of the inverse system
`(evₙ M)ₙ`, i.e. it is the first term of a distinguished Roos triangle
`R lim M ⟶ ∏ₙ evₙ M ──1 - s──▶ ∏ₙ evₙ M ⟶ (R lim M)[1]`. It is proved by computing on the
functorial K-injective resolution of `M`, which is K-injective with injective components: the
transition maps of an injective tower are split epimorphisms
(`CategoryTheory.isSplitEpi_map_of_injective`), so the Roos sequence of the resolution is short
exact (`DerivedCategory.isHomotopyLimit_mapCone_Q`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated

namespace CategoryTheory.Limits

variable (A : Type u) [Category.{v} A] {J : Type*} [Category J] [HasLimitsOfShape J A]

/-- The projections `lim F ⟶ F j`, as a natural transformation from `lim : (J ⥤ A) ⥤ A` to the
evaluation at `j`. -/
@[simps]
noncomputable def limπ (j : J) : (lim : (J ⥤ A) ⥤ A) ⟶ (evaluation J A).obj j where
  app F := limit.π F j

@[reassoc (attr := simp)]
lemma limπ_comp_evaluation_map {j j' : J} (f : j ⟶ j') :
    limπ A j ≫ (evaluation J A).map f = limπ A j' := by
  ext F
  simp

instance [Abelian A] : (lim : (J ⥤ A) ⥤ A).Additive := by
  have := (constLimAdj (J := J) (C := A)).rightAdjoint_preservesLimits
  have : PreservesBinaryBiproducts (lim : (J ⥤ A) ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end CategoryTheory.Limits

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- The derived evaluation functors `evₙ : D(ℕᵒᵖ ⥤ A) ⥤ D(A)`, as an inverse system of
functors: the transition maps are induced by the transition maps of the towers. -/
noncomputable def towerEval : ℕᵒᵖ ⥤ DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A where
  obj n := ((evaluation ℕᵒᵖ A).obj n).rightDerivedFunctor
  map f := Functor.rightDerivedFunctorNatTrans ((evaluation ℕᵒᵖ A).map f)
  map_id n := by
    rw [CategoryTheory.Functor.map_id]
    exact Functor.rightDerivedFunctorNatTrans_id _
  map_comp f g := by
    rw [Functor.map_comp]
    exact Functor.rightDerivedFunctorNatTrans_comp _ _

/-- An object `M` of the derived category of towers gives an inverse system `(evₙ M)ₙ` in the
derived category `D(A)`. -/
noncomputable def towerFunctor : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ ℕᵒᵖ ⥤ DerivedCategory A :=
  (towerEval A).flip

@[simp]
lemma towerFunctor_obj_obj (M : DerivedCategory (ℕᵒᵖ ⥤ A)) (n : ℕᵒᵖ) :
    ((towerFunctor A).obj M).obj n = ((towerEval A).obj n).obj M := rfl

@[simp]
lemma towerFunctor_obj_map (M : DerivedCategory (ℕᵒᵖ ⥤ A)) {n n' : ℕᵒᵖ} (f : n ⟶ n') :
    ((towerFunctor A).obj M).map f = ((towerEval A).map f).app M := rfl

@[simp]
lemma towerFunctor_map_app {M M' : DerivedCategory (ℕᵒᵖ ⥤ A)} (g : M ⟶ M') (n : ℕᵒᵖ) :
    ((towerFunctor A).map g).app n = ((towerEval A).obj n).map g := rfl

/-- **Blueprint `def-weil-pbc-derived-inverse-limit`.** The sequential derived inverse limit
`R lim : D(ℕᵒᵖ ⥤ A) ⥤ D(A)`, the total right derived functor of `lim : (ℕᵒᵖ ⥤ A) ⥤ A`. By
`DerivedCategory.isHomotopyLimit_rlimCone`, `R lim M` is a derived limit, in the sense of the
Roos triangle, of the inverse system `(evₙ M)ₙ` of `D(A)` (`DerivedCategory.towerFunctor`). -/
noncomputable def rlim : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor

/-- The natural maps `R lim M ⟶ evₙ M` induced by the projections `lim ⟶ evₙ`. -/
noncomputable def rlimπ (n : ℕᵒᵖ) : rlim A ⟶ (towerEval A).obj n :=
  Functor.rightDerivedFunctorNatTrans (limπ A n)

@[reassoc (attr := simp)]
lemma rlimπ_comp_towerEval_map {n n' : ℕᵒᵖ} (f : n ⟶ n') :
    rlimπ A n ≫ (towerEval A).map f = rlimπ A n' := by
  simp only [rlimπ, towerEval, ← Functor.rightDerivedFunctorNatTrans_comp,
    limπ_comp_evaluation_map]

/-- The cone of the maps `R lim M ⟶ evₙ M` over the inverse system `(evₙ M)ₙ`. -/
@[simps]
noncomputable def rlimCone (M : DerivedCategory (ℕᵒᵖ ⥤ A)) : Cone ((towerFunctor A).obj M) where
  pt := (rlim A).obj M
  π :=
    { app n := (rlimπ A n).app M
      naturality _ _ f := by
        simp only [Functor.const_obj_obj, towerFunctor_obj_obj, Functor.const_obj_map,
          Category.id_comp, towerFunctor_obj_map, ← NatTrans.comp_app,
          rlimπ_comp_towerEval_map] }

noncomputable instance : (rlim A).CommShift ℤ :=
  inferInstanceAs ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.CommShift ℤ)

/-- `R lim` is a triangulated functor. -/
instance : (rlim A).IsTriangulated :=
  inferInstanceAs (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.IsTriangulated

variable {A}

instance isKInjective_asFunctor_obj (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (n : ℕᵒᵖ) : CochainComplex.IsKInjective (I.asFunctor.obj n) :=
  Functor.PreservesKInjectiveComplexes.isKInjective_map (F := (evaluation ℕᵒᵖ A).obj n) I

/-- For a K-injective complex of towers `I`, the inverse system `(evₙ (Q I))ₙ` is computed by
applying `Q` to the levels of `I`. -/
noncomputable def towerFunctorObjQIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    (towerFunctor A).obj (Q.obj I) ≅ I.asFunctor ⋙ Q :=
  NatIso.ofComponents (fun n ↦ ((evaluation ℕᵒᵖ A).obj n).rightDerivedFunctorObjQIso I)
    fun {n n'} f ↦ by
      simp only [towerFunctor_obj_obj, towerFunctor_obj_map, towerEval, Functor.comp_map,
        Functor.rightDerivedFunctorNatTrans_app_Q_obj, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      rfl

/-- **Blueprint `prop-weil-pbc-derived-inverse-limit-computation`** (the representing object).
For a K-injective complex of towers `I`, `R lim (Q I)` is computed by the termwise limit:
`R lim (Q I) ≅ Q (lim I)`. -/
noncomputable def rlimObjQIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    (rlim A).obj (Q.obj I) ≅ Q.obj (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex _).obj I) :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I

/-- The termwise limit `lim I` of a complex of towers, with its projections, as a cone over the
inverse system of complexes `I.asFunctor`. -/
@[simps]
noncomputable def limConeAsFunctor (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex _).obj I
  π :=
    { app n := (NatTrans.mapHomologicalComplex (limπ A n) _).app I
      naturality _ _ f := by
        ext p
        exact (Category.id_comp _).trans (limit.w (I.X p) f).symm }

/-- The termwise limit of a complex of towers is a limit of the inverse system of complexes
`I.asFunctor`: limits of complexes are computed degreewise. -/
noncomputable def isLimitLimConeAsFunctor (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limConeAsFunctor I) :=
  HomologicalComplex.isLimitOfEval _ _ fun p ↦ limit.isLimit (I.X p)

lemma rlimCone_π_app_Q_obj (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (n : ℕᵒᵖ) :
    (rlimCone A (Q.obj I)).π.app n ≫ (towerFunctorObjQIso I).hom.app n =
      (rlimObjQIso I).hom ≫ Q.map ((limConeAsFunctor I).π.app n) := by
  simp only [rlimCone_π_app, rlimπ, towerFunctorObjQIso, NatIso.ofComponents_hom_app,
    Functor.rightDerivedFunctorNatTrans_app_Q_obj, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, rlimObjQIso, limConeAsFunctor_π_app]

/-- For a K-injective complex of towers `I` with injective components, `R lim (Q I)` is a
derived limit of the inverse system `(evₙ (Q I))ₙ`. -/
theorem isHomotopyLimit_rlimCone_Q_obj (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    [∀ p, Injective (I.X p)] : IsHomotopyLimit (rlimCone A (Q.obj I)) := by
  have h := isHomotopyLimit_mapCone_Q (G := I.asFunctor)
    (fun n p ↦ isSplitEpi_map_of_injective (I.X p) n) (isLimitLimConeAsFunctor I)
  refine h.of_iso (towerFunctorObjQIso I).symm _ (rlimObjQIso I).symm fun n ↦ ?_
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, Functor.mapCone_π_app, ← Category.assoc,
    ← rlimCone_π_app_Q_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- **Blueprint `prop-weil-pbc-roos-triangle`** (the Roos triangle). For every object `M` of the
derived category of towers, `R lim M` is a derived limit of the inverse system `(evₙ M)ₙ` of
`D(A)`: for a product `∏ₙ evₙ M` with transition endomorphism `s`, the Roos triangle
`R lim M ⟶ ∏ₙ evₙ M ──1 - s──▶ ∏ₙ evₙ M ⟶ (R lim M)[1]` is distinguished. -/
theorem isHomotopyLimit_rlimCone (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    IsHomotopyLimit (rlimCone A M) := by
  let K := Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)).obj K
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{v} _ K).2
  let e : Q.obj I ≅ M := (asIso (Q.map ((CochainComplex.toKInjectiveResolution.{v} _).app K))).symm
    ≪≫ Q.objObjPreimageIso M
  refine (isHomotopyLimit_rlimCone_Q_obj I).of_iso ((towerFunctor A).mapIso e) _
    ((rlim A).mapIso e) fun n ↦ ?_
  simp only [rlimCone_π_app, Functor.mapIso_hom, towerFunctor_map_app]
  exact ((rlimπ A (op n)).naturality e.hom).symm

end DerivedCategory
