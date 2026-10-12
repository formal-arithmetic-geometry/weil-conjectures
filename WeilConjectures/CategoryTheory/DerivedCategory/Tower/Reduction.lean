/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.TowerFunctorQ
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# The reduction tower of an object of the derived category

Let `A` be a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions, so that `D(A)` carries the derived tensor product `- ⊗ᴸ -`, and let
`P : ℕᵒᵖ ⥤ CochainComplex A ℤ` be an inverse system of complexes (a *coefficient tower*, for
instance the quotients `Pₙ = R/Iⁿ` placed in degree `0`, or the Koszul complexes
`K(R; f₁ᵐ, …, f_rᵐ)`).

For a K-flat complex `X`, the complexes `X ⊗ Pₙ` with the transition maps induced by `P` form a
complex of towers `DerivedCategory.tensorTowerFunctor P X`. Quasi-isomorphisms between K-flat
complexes are sent to quasi-isomorphisms, so this construction descends to a functor

`DerivedCategory.reductionTower P : D(A) ⥤ D(ℕᵒᵖ ⥤ A)`

(Blueprint `def-weil-pbc-adic-coefficient-datum`: the object `K_•` of the derived category of
towers attached to `K` via a functorial K-flat representative). Its underlying inverse system
in `D(A)` is the system of derived tensor products `K ⊗ᴸ Pₙ`
(`DerivedCategory.reductionTowerIso`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Opposite

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- The complex of towers `n ↦ X ⊗ Pₙ` attached to a complex `X` and a coefficient tower `P` of
complexes, the transition maps being induced by those of `P`. -/
noncomputable def tensorTowerFunctor (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  curriedTensor (CochainComplex A ℤ) ⋙ (Functor.whiskeringLeft _ _ _).obj P ⋙
    (HomologicalComplex.functorEquivalence A (ComplexShape.up ℤ) ℕᵒᵖ).inverse

/-- The tensor product with a coefficient tower sends quasi-isomorphisms between K-flat complexes
to quasi-isomorphisms of complexes of towers: quasi-isomorphisms of towers are detected
levelwise, and `f ▷ Pₙ` is a quasi-isomorphism (`MorphismProperty.whiskerRight_of_kFlat`). -/
lemma quasiIso_tensorTowerFunctor_map (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) {X Y : CochainComplex A ℤ}
    (f : X ⟶ Y) [QuasiIso f] (hX : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat X)
    (hY : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat Y) :
    QuasiIso ((tensorTowerFunctor P).map f) := by
  rw [HomologicalComplex.quasiIso_functorCategory_iff]
  intro n
  have := MorphismProperty.whiskerRight_of_kFlat _ f
    ((HomologicalComplex.mem_quasiIso_iff f).2 inferInstance) hX hY (P.obj n)
  rw [HomologicalComplex.mem_quasiIso_iff] at this
  exact this

variable (A) in
/-- The quasi-isomorphisms between K-flat complexes. -/
abbrev kFlatQuasiIso : MorphismProperty (CochainComplex.KFlat A) :=
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).WKFlat

/-- The functor `X ↦ Q (X ⊗ Pₙ)ₙ` on K-flat complexes. -/
noncomputable def tensorTowerFunctorKFlat (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex.KFlat A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A) :=
  CochainComplex.ιKFlat A ⋙ tensorTowerFunctor P ⋙ Q

lemma kFlatQuasiIso_isInvertedBy (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (kFlatQuasiIso A).IsInvertedBy (tensorTowerFunctorKFlat P) := by
  intro X Y f hf
  have : QuasiIso f.hom := (HomologicalComplex.mem_quasiIso_iff _).1 hf
  have := quasiIso_tensorTowerFunctor_map P f.hom X.2 Y.2
  dsimp [tensorTowerFunctorKFlat]
  infer_instance

/-- **Blueprint `def-weil-pbc-adic-coefficient-datum`** (the reduction tower). The functor
`D(A) ⥤ D(ℕᵒᵖ ⥤ A)` sending `K`, represented by a K-flat complex `X`, to the complex of towers
`(X ⊗ Pₙ)ₙ` with the transition maps induced by the coefficient tower `P`. Its evaluations are
the derived tensor products `K ⊗ᴸ Pₙ` (`DerivedCategory.reductionTowerIso`). -/
noncomputable def reductionTower (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A) :=
  Localization.lift (tensorTowerFunctorKFlat P) (kFlatQuasiIso_isInvertedBy P)
    (TensorCommShift₂.LKFlat A)

noncomputable instance (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    Localization.Lifting (TensorCommShift₂.LKFlat A) (kFlatQuasiIso A)
      (tensorTowerFunctorKFlat P) (reductionTower P) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ _))

/-- The inverse system `n ↦ K ⊗ᴸ Pₙ` of `D(A)`, as a functor of `K`. -/
noncomputable def reductionSystem (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    DerivedCategory A ⥤ ℕᵒᵖ ⥤ DerivedCategory A :=
  curriedTensor (DerivedCategory A) ⋙ (Functor.whiskeringLeft _ _ _).obj (P ⋙ Q)

/-- The comparison of the levels `Q (X ⊗ Pₙ)` of the reduction tower of a K-flat complex `X` with
the derived tensor products `Q X ⊗ᴸ Q Pₙ`, as an isomorphism of functors of `X`. -/
noncomputable def reductionTowerIsoAux (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    TensorCommShift₂.LKFlat A ⋙ reductionTower P ⋙ towerFunctor A ≅
      TensorCommShift₂.LKFlat A ⋙ reductionSystem P :=
  isoWhiskerRight (Localization.Lifting.iso (TensorCommShift₂.LKFlat A) (kFlatQuasiIso A)
      (tensorTowerFunctorKFlat P) (reductionTower P)) (towerFunctor A) ≪≫
    isoWhiskerLeft (CochainComplex.ιKFlat A ⋙ tensorTowerFunctor P) (towerFunctorQIso A) ≪≫
    isoWhiskerLeft (CochainComplex.ιKFlat A ⋙ curriedTensor (CochainComplex A ℤ) ⋙
        (Functor.whiskeringLeft _ _ _).obj P)
      ((Functor.whiskeringRight _ _ _).mapIso (quotientCompQhIso A).symm) ≪≫
    isoWhiskerRight (asIso (TensorCommShift₂.liftingIsoHom A)).symm
      ((Functor.whiskeringLeft _ _ _).obj P) ≪≫
    isoWhiskerLeft (TensorCommShift₂.LKFlat A ⋙ curriedTensor (DerivedCategory A))
      ((Functor.whiskeringLeft _ _ _).mapIso (isoWhiskerLeft P (quotientCompQhIso A)))

/-- The underlying inverse system `(evₙ K_•)ₙ` of the reduction tower `K_•` of `K` is the
system of derived tensor products `K ⊗ᴸ Pₙ`, naturally in `K`. -/
noncomputable def reductionTowerIso (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    reductionTower P ⋙ towerFunctor A ≅ reductionSystem P :=
  Localization.liftNatIso (TensorCommShift₂.LKFlat A) (kFlatQuasiIso A) _ _ _ _
    (reductionTowerIsoAux P)

end DerivedCategory
