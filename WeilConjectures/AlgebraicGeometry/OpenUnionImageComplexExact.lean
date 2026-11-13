/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenUnionModuleImagePullback
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Exactness of the concrete complex on an arbitrary open union

Source: Stacks Project, Tag 08BV, displayed sequence applied on the union.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem schemeRestrictUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) := by
  have hv : Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val := by
    apply PresheafOfModules.epi_of_surjective
    intro T
    change Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) T.unop)
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact (injective_restriction_surjective X.toRingedSpace
      (U.ι.image_preimage_le T.unop) M).1
  constructor
  intro Z g h eq
  apply SheafOfModules.hom_ext
  exact (cancel_epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val).mp
    (congrArg SheafOfModules.Hom.val eq)

private theorem schemeOpenModuleUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleAdjunction X U).unit.app M) := by
  have := schemeRestrictUnit_epi X U M
  change Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
    (Scheme.Modules.pushforward U.ι).map ((Scheme.Modules.overFunctorEquiv U).inv.app M))
  infer_instance

private theorem schemeOpenModuleImageRestriction_epi
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleImageRestriction X i).app M) := by
  have := schemeOpenModuleUnit_epi X W M
  have : Epi ((schemeOpenModuleAdjunction X U).unit.app M ≫
      (schemeOpenModuleImageRestriction X i).app M) := by
    rw [schemeOpenModuleImage_unit_restriction]
    infer_instance
  exact epi_of_epi ((schemeOpenModuleAdjunction X U).unit.app M) _

set_option maxHeartbeats 500000 in
-- The explicit biproduct comparison requires additional elaboration steps.
/-- The pair of restrictions from the union and the difference to the overlap
form a short exact sequence for a complex with injective terms.

Source: Stacks Project, Tag 08BV, lemma-exact-sequence-j-star, the displayed
sequence of complexes; Tag 01EB, lemma-mayer-vietoris, its sectionwise proof.

Proof: In degree n over a test open T, identify the four direct-image terms
with I^n(T intersection (U union V)), I^n(T intersection U),
I^n(T intersection V), and I^n(T intersection U intersection V).
The underived adjunction mate defining each arrow is ordinary restriction:
the nested-restriction comparison identifies iterated restriction, and its
counit cancels the repeated restriction to the larger open. The two iterated
restrictions to the overlap agree, so the pair followed by the difference is
zero. The opens T intersection U and T intersection V cover
T intersection (U union V). Sheaf uniqueness gives injectivity of the first
map; sheaf gluing identifies its image with the kernel of the second map.
Injectivity of I^n makes restriction from T intersection U to the overlap
surjective (injective_restriction_surjective), so pairing a lift with zero
gives surjectivity of the difference. The sectionwise kernel property is
natural in T, hence a kernel in presheaf modules and, by the fully faithful
inclusion, in sheaf modules. Sectionwise injectivity and surjectivity give
monicity and epicity. Evaluation of complexes preserves biproducts; use its
biproduct comparison and HomologicalComplex.shortExact_of_degreewise_shortExact
to conclude. No K-injectivity or derived category is used. Empty opens give
zero summands; repeated opens give the diagonal/difference split sequence. -/
theorem schemeOpenUnionImageComplex_shortExact
    (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    let f := biprod.lift
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
      (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
    let g := biprod.desc
      (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
      (-(schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I))
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  let f := biprod.lift
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_left : U ≤ U ⊔ V)) I)
    (schemeOpenModuleImageComplexRestriction X (homOfLE (le_sup_right : V ≤ U ⊔ V)) I)
  let g := biprod.desc
    (schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)) I)
    (-(schemeOpenModuleImageComplexRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)) I))
  have hz : f ≫ g = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := (schemeOpenUnionModuleImage_isPullback X U V (I.X n)).w
    change (f ≫ g).f n = 0
    dsimp only [f, g]
    rw [biprod.lift_desc]
    simp only [Preadditive.comp_neg]
    change _ + -_ = 0
    exact add_neg_eq_zero.mpr h
  refine ⟨hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact (ShortComplex.mk f g hz)
  intro n
  let h := schemeOpenUnionModuleImage_isPullback X U V (I.X n)
  have : Injective (I.X n) := hI n
  have : Epi ((schemeOpenModuleImageRestriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U))).app (I.X n)) :=
    schemeOpenModuleImageRestriction_epi X _ (I.X n)
  have : Epi h.shortComplex'.g := by
    have : Epi (biprod.inl ≫ h.shortComplex'.g) := by
      simpa only [CommSq.shortComplex'_g, biprod.inl_desc] using
        (inferInstance : Epi ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_left : U ⊓ V ≤ U))).app (I.X n)))
    exact epi_of_epi biprod.inl _
  have he : h.shortComplex'.ShortExact :=
    ShortComplex.ShortExact.mk' (IsPullback.exact_shortComplex' h)
      h.mono_shortComplex'_f inferInstance
  let S := (ShortComplex.mk f g hz).map
    (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ) n)
  -- Evaluation preserves the biproduct. Check both units and both signed restrictions.
  let e : S ≅ h.shortComplex' := ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n)
    (Iso.refl _) (by
      change biprod.lift ((schemeOpenModuleImageRestriction X (homOfLE le_sup_left)).app (I.X n))
        ((schemeOpenModuleImageRestriction X (homOfLE le_sup_right)).app (I.X n)) =
          f.f n ≫ _
      apply biprod.hom_ext
      · rw [biprod.lift_fst, Category.assoc]
        erw [HomologicalComplex.biprodXIso_hom_fst]
        exact (HomologicalComplex.biprod_lift_fst_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE le_sup_left) I)
          (schemeOpenModuleImageComplexRestriction X (homOfLE le_sup_right) I) n).symm
      · rw [biprod.lift_snd, Category.assoc]
        erw [HomologicalComplex.biprodXIso_hom_snd]
        exact (HomologicalComplex.biprod_lift_snd_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE le_sup_left) I)
          (schemeOpenModuleImageComplexRestriction X (homOfLE le_sup_right) I) n).symm)
    (by
      change _ ≫ biprod.desc
        ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U))).app
          (I.X n))
        (-((schemeOpenModuleImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))).app
          (I.X n))) = g.f n ≫ 𝟙 _
      rw [Category.comp_id]
      apply (cancel_epi (HomologicalComplex.biprodXIso
        (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n).inv).mp
      rw [Iso.inv_hom_id_assoc]
      apply biprod.hom_ext'
      · rw [biprod.inl_desc, ← Category.assoc]
        erw [HomologicalComplex.inl_biprodXIso_inv
          (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n]
        exact (HomologicalComplex.biprod_inl_desc_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I)
          (-(schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I)) n).symm
      · rw [biprod.inr_desc, ← Category.assoc]
        erw [HomologicalComplex.inr_biprodXIso_inv
          (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n]
        exact (HomologicalComplex.biprod_inr_desc_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I)
          (-(schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I)) n).symm)
  exact ShortComplex.shortExact_of_iso e.symm he

end AlgebraicGeometry
