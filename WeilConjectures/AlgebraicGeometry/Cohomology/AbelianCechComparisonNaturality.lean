/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechAlphaQuasiIso
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechAlphaNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechBetaNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionCycle
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionInjective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Naturality of the augmentation quotient

Source: Stacks Project, Tag 01EQ, functoriality omitted in the proof,
and Tag 01FD, augmented comparison diagram.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Canonical comparison maps commute with coefficient morphisms.

Source: Stacks Project, Tags 01EQ and 01FD, augmentation squares. -/
theorem abelianCechComparison_naturality
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (q : ℕ)
    (c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F)
    (d : (TopCat.Sheaf.cechCohomologyFunctor U q).obj G ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj G)
    (hc : IsAbelianCechComparison U F q c) (hd : IsAbelianCechComparison U G q d) :
    (TopCat.Sheaf.cechCohomologyFunctor U q).map f ≫ d =
      c ≫ (Sheaf.functorH (Opens.grothendieckTopology X) q).map f := by
  ext x
  let I := injectiveResolution F
  let J := injectiveResolution G
  let φ : InjectiveResolution.Hom I J f :=
    ⟨InjectiveResolution.desc f J I, InjectiveResolution.desc_commutes_zero f J I⟩
  obtain ⟨a, ha, hax⟩ := I.extMk_surjective (c x) (q + 1) rfl
  obtain ⟨z, hz⟩ := abelianCech_ext_section_cycle I q a ha
  let a' := a ≫ φ.hom.f q
  have ha' : a' ≫ J.cocomplex.d q (q + 1) = 0 := by
    dsimp [a']
    simp [reassoc_of% ha]
  let S := abelianCechSectionsMap φ.hom
  let z' := HomologicalComplex.cyclesMap S q z
  have hz' : ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ a') (ULift.up 1) =
      (abelianCechSections J).iCycles q z' := by
    let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop
    have ht := ConcreteCategory.congr_hom
      (adj.homEquiv_naturality_right a (φ.hom.f q)) (ULift.up 1)
    have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i S q) z
    simp only [ConcreteCategory.comp_apply] at hi ht
    change _ = (abelianCechSections J).iCycles q
      (HomologicalComplex.cyclesMap S q z)
    rw [hi]
    change _ = (S.f q) ((abelianCechSections I).iCycles q z)
    rw [← hz]
    exact ht
  have hcx' : (Sheaf.functorH (Opens.grothendieckTopology X) q).map f (c x) =
      J.extMk a' (q + 1) rfl ha' := by
    rw [← hax]
    exact InjectiveResolution.extMk_comp_mk₀ a (q + 1) rfl ha φ
  let y := (TopCat.Sheaf.cechCohomologyFunctor U q).map f x
  obtain ⟨b, hb, hby⟩ := J.extMk_surjective (d y) (q + 1) rfl
  obtain ⟨w, hw⟩ := abelianCech_ext_section_cycle J q b hb
  have hcz := hc I x a ha z hz hax.symm
  have hdw := hd J y b hb w hw hby.symm
  have hβ := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (abelianCechBeta_square U φ)
  have hα := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (abelianCechAlpha_square U φ.hom)
  simp only [HomologicalComplex.homologyMap_comp] at hβ hα
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality S q) z
  have heq : HomologicalComplex.homologyMap (abelianCechAlpha U J) q
      ((abelianCechSections J).homologyπ q w) =
      HomologicalComplex.homologyMap (abelianCechAlpha U J) q
        ((abelianCechSections J).homologyπ q z') := by
    rw [← hdw]
    have hβx := ConcreteCategory.congr_hom hβ x
    have hαz := ConcreteCategory.congr_hom hα ((abelianCechSections I).homologyπ q z)
    simp only [ConcreteCategory.comp_apply] at hβx hαz hπ
    change HomologicalComplex.homologyMap (abelianCechTotalMap U φ.hom) q
      (HomologicalComplex.homologyMap (abelianCechBeta U I) q x) =
      HomologicalComplex.homologyMap (abelianCechBeta U J) q y at hβx
    rw [← hβx, hcz, hαz]
    exact congrArg (fun t ↦ HomologicalComplex.homologyMap (abelianCechAlpha U J) q t)
      hπ
  have : QuasiIso (abelianCechAlpha U J) := abelianCechAlpha_quasiIso U hcover J
  have heq' : (abelianCechSections J).homologyπ q w =
      (abelianCechSections J).homologyπ q z' :=
    (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (abelianCechAlpha U J) q)).injective heq
  change d y = (Sheaf.functorH (Opens.grothendieckTopology X) q).map f (c x)
  rw [hcx', ← hby]
  exact abelianCech_ext_section_injective J q b a' hb ha' w z' hw hz' heq'
end AlgebraicGeometry.Scheme.Modules
