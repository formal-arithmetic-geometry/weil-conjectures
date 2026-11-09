/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom

/-!
# The projection formula for extension and restriction of scalars

Let `φ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel. For
étale sheaves of modules, the restriction of scalars of `(Λ' ⊗_Λ P) ⊗ M` is `P ⊗ Res M`,
naturally in `P` and `M` (`CategoryTheory.Sheaf.extendScalarsTensorRestrictScalarsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

namespace CategoryTheory.MonoidalCategory

variable {𝒜 𝒜' : Type*} [Category* 𝒜] [Category* 𝒜'] [MonoidalCategory 𝒜]
  [MonoidalCategory 𝒜'] (E : 𝒜 ⥤ 𝒜') [E.Monoidal] (R : 𝒜' ⥤ 𝒜) (ε : R ⋙ E ≅ 𝟭 𝒜') (c : 𝒜)
  (T : E ⋙ R ≅ tensorRight c)

/-- The projection isomorphism `R(E P ⊗ M) ≅ P ⊗ R M` for a monoidal functor `E` and a functor
`R` with `E ∘ R ≅ 𝟭` and `R ∘ E ≅ - ⊗ c`, for objects `P` of `𝒜` and `M` of `𝒜'`. -/
noncomputable def projectionIsoOfCompIso (P : 𝒜) (M : 𝒜') : R.obj (E.obj P ⊗ M) ≅ P ⊗ R.obj M :=
  R.mapIso (whiskerLeftIso _ (ε.app M).symm ≪≫ Functor.Monoidal.μIso E P (R.obj M)) ≪≫
    T.app _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso P (T.app _).symm ≪≫
    whiskerLeftIso P (R.mapIso (ε.app M))

lemma projectionIsoOfCompIso_hom (P : 𝒜) (M : 𝒜') :
    (projectionIsoOfCompIso E R ε c T P M).hom =
      R.map (E.obj P ◁ ε.inv.app M) ≫ R.map (Functor.LaxMonoidal.μ E P (R.obj M)) ≫
        T.hom.app _ ≫ (α_ _ _ _).hom ≫ P ◁ T.inv.app _ ≫ P ◁ R.map (ε.hom.app M) := by
  simp [projectionIsoOfCompIso]

/-- The projection isomorphism `R(E P ⊗ M) ≅ P ⊗ R M` of
`CategoryTheory.MonoidalCategory.projectionIsoOfCompIso`, natural in `P` and `M`. -/
noncomputable def projectionNatIsoOfCompIso :
    E ⋙ curriedTensor 𝒜' ⋙ (Functor.whiskeringRight _ _ _).obj R ≅
      curriedTensor 𝒜 ⋙ (Functor.whiskeringLeft _ _ _).obj R :=
  NatIso.ofComponents
    (fun P ↦ NatIso.ofComponents (fun M ↦ projectionIsoOfCompIso E R ε c T P M)
      (fun {M M'} g ↦ by
        have h₁ := ε.inv.naturality g
        have h₂ := ε.hom.naturality g
        have h₃ := T.hom.naturality (P ◁ R.map g)
        have h₄ := T.inv.naturality (R.map g)
        dsimp at h₁ h₂ h₃ h₄ ⊢
        rw [projectionIsoOfCompIso_hom, projectionIsoOfCompIso_hom, ← R.map_comp_assoc,
          ← whiskerLeft_comp, h₁, whiskerLeft_comp, R.map_comp_assoc,
          ← R.map_comp_assoc (E.obj P ◁ E.map (R.map g)), Functor.LaxMonoidal.μ_natural_right,
          R.map_comp_assoc, reassoc_of% h₃, associator_naturality_middle_assoc,
          ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, h₄, Category.assoc, ← R.map_comp, h₂,
          R.map_comp]
        simp only [whiskerLeft_comp, Category.assoc]))
    (fun {P P'} g ↦ by
      ext M : 2
      have h₃ := T.hom.naturality (g ▷ R.obj M)
      dsimp at h₃ ⊢
      rw [projectionIsoOfCompIso_hom, projectionIsoOfCompIso_hom, ← R.map_comp_assoc,
        ← whisker_exchange, R.map_comp_assoc, ← R.map_comp_assoc (E.map g ▷ _)]
      erw [Functor.LaxMonoidal.μ_natural_left]
      rw [R.map_comp_assoc, reassoc_of% h₃,
        associator_naturality_left_assoc, ← whisker_exchange_assoc, ← whisker_exchange]
      simp)

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A A' : Type (u + 1)} [CommRing A] [CommRing A'] {f : A →+* A'}
  (hf : Function.Surjective f) {a : A} (ha : RingHom.ker f = Ideal.span {a})

/-- The isomorphism `Res((A' ⊗_A P) ⊗ M) ≅ P ⊗ Res M`, natural in the sheaf of `A`-modules `P`
and the sheaf of `A'`-modules `M`. -/
noncomputable def extendScalarsTensorRestrictScalarsIso :
    extendScalars J f ⋙ curriedTensor _ ⋙
        (Functor.whiskeringRight _ _ _).obj (restrictScalars J f) ≅
      curriedTensor _ ⋙ (Functor.whiskeringLeft _ _ _).obj (restrictScalars J f) :=
  have := isIso_extendScalarsAdjunction_counit J hf
  MonoidalCategory.projectionNatIsoOfCompIso _ _ (asIso (extendScalarsAdjunction J f).counit) _
    (extendScalarsCompRestrictScalarsQuotientIso J hf ha)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_restrictScalarsTensor
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Sheaves of modules on the small étale site have countable coproducts. Instance search times
out on this. -/
local instance instHasCountableCoproductsSheaf_restrictScalarsTensor
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

local instance instIsLeftAdjointModuleCatExtendScalars_restrictScalarsTensor
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

/-- The projection isomorphism `Res((Λ' ⊗_Λ P) ⊗ M) ≅ P ⊗ Res M` for cochain complexes `P` of
étale sheaves of `Λ`-modules and `M` of étale sheaves of `Λ'`-modules. -/
noncomputable def extendScalarsTensorRestrictScalarsComplexIso
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (M : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) :
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P ⊗
          M) ≅
      P ⊗ ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj M :=
  letI (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      ((Sheaf.extendScalars X.smallEtaleTopology φ ⋙ curriedTensor _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (Sheaf.restrictScalars X.smallEtaleTopology φ)).obj P).PreservesZeroMorphisms :=
    inferInstanceAs ((tensorLeft ((Sheaf.extendScalars X.smallEtaleTopology φ).obj P) ⋙
        Sheaf.restrictScalars X.smallEtaleTopology φ).PreservesZeroMorphisms)
  letI (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      ((curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Sheaf.restrictScalars X.smallEtaleTopology φ)).obj P).PreservesZeroMorphisms :=
    inferInstanceAs
      ((Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ tensorLeft P).PreservesZeroMorphisms)
  letI : (Sheaf.extendScalars X.smallEtaleTopology φ ⋙ curriedTensor _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (Sheaf.restrictScalars X.smallEtaleTopology φ)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  letI : (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (Sheaf.restrictScalars X.smallEtaleTopology φ)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  (HomologicalComplex₂.mapTotalIso (Sheaf.restrictScalars X.smallEtaleTopology φ)
      ((((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj
          P)).obj M) (.up ℤ)).symm ≪≫
    HomologicalComplex₂.total.mapIso
      (HomologicalComplex.mapBifunctorHomologicalComplexObjObjIso
        (Sheaf.extendScalarsTensorRestrictScalarsIso X.smallEtaleTopology hφ ha) P M) (.up ℤ)

set_option maxHeartbeats 400000 in
-- the kernel checks the chain of isomorphisms below
include hφ ha in
/-- **The projection formula for extension and restriction of scalars.** For `L ∈ D(X_ét, Λ)` and
`N ∈ D(X_ét, Λ')`, `Res((L ⊗ᴸ_Λ Λ') ⊗ᴸ N) ≅ L ⊗ᴸ Res N`: on a K-flat representative `P` of `L`
and a K-flat representative `M` of `N`, both sides are computed by the complexes
`Res((Λ' ⊗_Λ P) ⊗ M) ≅ P ⊗ Res M`
(`AlgebraicGeometry.Etale.extendScalarsTensorRestrictScalarsComplexIso`). -/
theorem nonempty_iso_derivedRestrictScalars_derivedTensor (L : 𝐃(X, Λ)) (N : 𝐃(X, Λ')) :
    Nonempty ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ') X).obj
          ((derivedExtendScalars hφ ha X).obj L)).obj N) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj N)) := by
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  let F := Sheaf.extendScalars X.smallEtaleTopology φ
  let R := Sheaf.restrictScalars X.smallEtaleTopology φ
  obtain ⟨P, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso L
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P').1 hP
  obtain ⟨Q, hQ, ⟨eN⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso N
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P' hP'
  have := _root_.DerivedCategory.isIso_tensorLeftCounit _ hP
  have := _root_.DerivedCategory.isIso_tensorRightCounit _ hQ
  let qF := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((F.mapHomologicalComplex _).obj P')
  let qM := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M
  let qRM := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((R.mapHomologicalComplex _).obj M)
  -- `L ⊗ᴸ Λ' ≅ Qh (Λ' ⊗ P)`
  let j₁ : (derivedExtendScalars hφ ha X).obj L ≅ _root_.DerivedCategory.Qh.obj qF :=
    (derivedExtendScalars hφ ha X).mapIso e.symm ≪≫
      asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P')) ≪≫
      _root_.DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors _).app P')
  -- `Res N ≅ Qh (Res M)`
  let j₂ : R.mapDerivedCategory.obj N ≅ _root_.DerivedCategory.Qh.obj qRM :=
    R.mapDerivedCategory.mapIso (eN.symm ≪≫
        (_root_.DerivedCategory.quotientCompQhIso _).app M) ≪≫
      R.mapDerivedCategoryFactors.app M ≪≫
      ((_root_.DerivedCategory.quotientCompQhIso _).app ((R.mapHomologicalComplex _).obj M)).symm
  let k₁ := R.mapDerivedCategory.mapIso (tensorIso j₁ eN.symm ≪≫
      asIso ((_root_.DerivedCategory.tensorRightCounit qM).app qF) ≪≫
      _root_.DerivedCategory.Qh.mapIso
        (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) _ M) ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).app (((F.mapHomologicalComplex _).obj P') ⊗ M))
  let k₂ := R.mapDerivedCategoryFactors.app (((F.mapHomologicalComplex _).obj P') ⊗ M)
  let k₃ := _root_.DerivedCategory.Q.mapIso
    (extendScalarsTensorRestrictScalarsComplexIso hφ ha X P' M)
  let k₄ := ((_root_.DerivedCategory.quotientCompQhIso _).app
      (P' ⊗ (R.mapHomologicalComplex _).obj M)).symm ≪≫
    _root_.DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) P' _).symm ≪≫
    (asIso ((_root_.DerivedCategory.tensorLeftCounit
      ((HomotopyCategory.quotient _ _).obj P')).app qRM)).symm ≪≫
    tensorIso e j₂.symm
  exact ⟨k₁ ≪≫ k₂ ≪≫ k₃ ≪≫ k₄⟩

end Etale

end AlgebraicGeometry
