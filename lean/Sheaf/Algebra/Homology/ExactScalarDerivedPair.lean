/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData

/-! # Assembling a normalized scalar pair for an exact extension functor

Source: Stacks 07A4, 07A6 and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

/-- Normalized ordinary and chain transposes assemble the exact scalar-derived pair.
Source: Stacks 07A4, 07A6, 0D6D (blueprint: lem-pod-exact-scalar-derived-pair).
Proof: use the exact functor's canonical derived functor and homotopy counit.
Its comparison on complexes equals the canonical cochain counit: the extra
quotient-comparison maps are identities. Exactness makes that counit invertible.
The supplied unit and transpose equations are then precisely the two normalized
adjunction fields of the scalar-derived pair. All functor data are the given data. -/
theorem exactScalarDerivedPair
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (hobj : ∀ M, E.obj M = changeOfRings a M)
    (hmap : ∀ {M N : scalarModules J R} (f : M ⟶ N),
      E.map f = eqToHom (hobj M) ≫ changeOfRingsHom a M f ≫ eqToHom (hobj N).symm)
    (adj : E ⊣ scalarRestriction a)
    (hu : ∀ (M : scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
      ((eqToHom (hobj M)).val.app V) ((adj.unit.app M).val.app V x) =
        (toSheafify J (changeOfRingsPresheaf a M).presheaf).app V
          ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
            (M.val.obj V) x))
    (δ : E.mapDerivedCategory ⊣ scalarDerivedRestriction a)
    (hn : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      ∀ (H : CochainComplex (scalarModules J S) ℤ)
        (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H),
      (δ.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
          (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
        E.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map (scalarChainTranspose a E inferInstance adj P H g)) :
    ∃ D : ScalarDerivedPair a,
      D.extension = E ∧ D.derived = E.mapDerivedCategory ∧ HEq δ D.adjunction := by
  have hε (P : CochainComplex (scalarModules J R) ℤ) :
      scalarPairComplexComparison E inferInstance E.mapDerivedCategory
        E.mapDerivedCategoryFactorsh.hom P = E.mapDerivedCategoryFactors.hom.app P := by
    dsimp only [scalarPairComplexComparison]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change E.mapDerivedCategory.map (𝟙 _) ≫
      (E.mapDerivedCategory.map (𝟙 _) ≫ E.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
    erw [E.mapDerivedCategory.map_id (DerivedCategory.Q.obj P),
      DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P))]
    have hid {X Y : DerivedCategory (scalarModules J S)} (f : X ⟶ Y) :
        𝟙 X ≫ (𝟙 X ≫ f ≫ 𝟙 Y ≫ 𝟙 Y) ≫ 𝟙 Y = f := by
      simp only [Category.id_comp, Category.comp_id]
    convert hid (E.mapDerivedCategoryFactors.hom.app P) using 1
    rfl
  exact ⟨{
    extension := E
    extension_obj := hobj
    extension_map := hmap
    extension_additive := inferInstance
    derived := E.mapDerivedCategory
    counit := E.mapDerivedCategoryFactorsh.hom
    isLeftDerived := Functor.isLeftDerivedFunctor_of_inverts _ _ E.mapDerivedCategoryFactorsh
    computes := by
      intro P _
      rw [hε]
      exact (E.mapDerivedCategoryFactors.app P).isIso_hom
    ordinaryAdjunction := adj
    ordinaryUnit := hu
    adjunction := δ
    normalization := by intro P hP hflat H f; rw [hε]; exact hn P hP hflat H f },
    rfl, rfl, HEq.rfl⟩

end SheafOfModules
