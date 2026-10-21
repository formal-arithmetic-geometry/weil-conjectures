/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
import Sheaf.AlgebraicGeometry.LocalAcyclicityStrictFibreComparison
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Stalk cohomology of the geometric-fibre pushforward

Source: Stacks Project, Tag 0GJU, stalk calculation in lemma-beta-is-isomorphism.
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem nonempty_cohomology_iso_of_iso_over
    {X Y Z : Scheme.{u}} (e : Y ≅ Z) (mY : Y ⟶ X) (mZ : Z ⟶ X)
    (he : e.hom ≫ mZ = mY)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    Nonempty
      ((cohomology AddCommGrpCat.{u + 1} Y q).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} mY).obj G)) ≅
        (cohomology AddCommGrpCat.{u + 1} Z q).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} mZ).obj G))) := by
  let H := (upperStar AddCommGrpCat.{u + 1} mZ).obj G
  let c : (upperStar AddCommGrpCat.{u + 1} mY).obj G ≅
      (upperStar AddCommGrpCat.{u + 1} e.hom).obj H :=
    (upperStarComp AddCommGrpCat.{u + 1} e.hom mZ mY he.symm).app G
  let d := (DerivedCategory.singleFunctor _ 0).mapIso c ≪≫
    ((upperStar AddCommGrpCat.{u + 1} e.hom).mapDerivedCategorySingleFunctor 0).symm.app H
  exact ⟨(cohomology AddCommGrpCat.{u + 1} Y q).mapIso d ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((upperStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} e).app
        ((DerivedCategory.singleFunctor _ 0).obj H))⟩

/-- For an arbitrary coefficient sheaf, the nonnegative target stalks of the derived
unit on the closed fibre are the cohomology of a variety of vanishing cycles. No local
acyclicity is assumed. Source: Stacks Project, Tag 0GJU, displayed stalk calculation.
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-stalks).

Proof: the geometric-fibre projection is affine, being the base change of a morphism
between affine schemes, and hence is quasi-compact and quasi-separated. Commute homology
with exact inverse image, then use the inverse-image stalk comparison. Commute the other
inverse image with the degree-zero single functor and apply the unrestricted
strict-henselization stalk formula. The symmetry and associativity isomorphisms for
pullbacks identify its strict-local fibre with the fibre of the strict localization of
X'. Apply the strict-fibre comparison over X, and use invariance of derived global
sections under scheme isomorphisms and inverse-image composition to transport its
coefficients. This works in degree zero, in positive degrees, and for empty fibres. -/
theorem closedFibre_derivedUnit_target_stalks
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∀ q : ℕ, Nonempty
        ((Scheme.pointSmallEtale z).sheafFiber.obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj
                (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
                  (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj
                    ((upperStar AddCommGrpCat.{u + 1} p).obj G))))) ≅
          (cohomology AddCommGrpCat.{u + 1}
            (localAcyclicityFiber f x (t ≫ e.hom)) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G))) := by
  dsimp only
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
  let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
    (Scheme.strictHenselizationPointEvaluation s)))
  let h := pullback.fst f' t
  let x' := z ≫ i
  let x := x' ≫ p
  have : IsAffine (Scheme.strictHenselizationScheme s) := by
    change IsAffine (Spec (Scheme.strictHenselizationRing s))
    infer_instance
  have ht : IsAffineHom t := inferInstance
  have hh : IsAffineHom h := MorphismProperty.pullback_fst f' t ht
  have hclosed : x' ≫ f' = (z ≫ pullback.snd f'
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)))) ≫
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)) := by
    simpa only [x', i, Category.assoc] using congrArg (fun a ↦ z ≫ a)
      (pullback.condition (f := f') (g := Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationPointEvaluation s))))
  obtain ⟨_, e, E, _, hE⟩ := localAcyclicity_strict_fibre_comparison f s p f'
    (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)) x'
    (z ≫ pullback.snd f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationPointEvaluation s)))) hclosed t
  refine ⟨e, fun q ↦ ?_⟩
  let G' := (upperStar AddCommGrpCat.{u + 1} p).obj G
  let F := (upperStar AddCommGrpCat.{u + 1} h).obj G'
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G'
  let L := (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K
  let R := (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (q : ℤ)
  let Φ := (Scheme.pointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1})
  let Ψ := (Scheme.pointSmallEtale x').sheafFiber (A := AddCommGrpCat.{u + 1})
  let d : L ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
    ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0).app G'
  obtain ⟨cStalk, _⟩ := inverseImage_stalk_germ i z
  let c := Φ.mapIso
      (((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).symm.app (R.obj L)) ≪≫
    cStalk.app (H.obj (R.obj L)) ≪≫
    Ψ.mapIso (H.mapIso (R.mapIso d))
  obtain ⟨r, _, hr⟩ := unrestricted_strictHenselization_stalk h x' F q
  -- The upstream stalk formula is stated over the strict localization `strictLocalization x'`;
  -- the strict-fibre comparison over `X` uses the representative model
  -- `strictHenselizationScheme x'`. The two are identified over `X'` by the colimit comparison.
  let ρ₀ := Scheme.strictHenselizationStructuralMap x'
  let ρ := Scheme.strictLocalizationToBase x'
  let ι : Scheme.strictHenselizationScheme x' ⟶ Scheme.strictLocalization x' :=
    Spec.map (Scheme.smallStrictHenselizationColimitIso x').inv
  have hι : ι ≫ ρ = ρ₀ := Scheme.smallStrictHenselizationColimitIso_toBase x'
  let W₀ := pullback h ρ₀
  let w₀ := pullback.fst h ρ₀
  let mW₀ := (w₀ ≫ h) ≫ p
  let W := pullback h ρ
  let w := pullback.fst h ρ
  let mW := (w ≫ h) ≫ p
  let mV := pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
    Scheme.strictHenselizationStructuralMap x
  let cF : (upperStar AddCommGrpCat.{u + 1} w).obj F ≅
      (upperStar AddCommGrpCat.{u + 1} mW).obj G :=
    ((upperStarComp AddCommGrpCat.{u + 1} w h).symm.app G') ≪≫
      ((upperStarComp AddCommGrpCat.{u + 1} (w ≫ h) p).symm.app G)
  let J0 : W ≅ W₀ :=
    { hom := pullback.lift (pullback.fst h ρ) (pullback.snd h ρ ≫ inv ι) (by
        rw [Category.assoc, ← hι, IsIso.inv_hom_id_assoc, pullback.condition])
      inv := pullback.lift (pullback.fst h ρ₀) (pullback.snd h ρ₀ ≫ ι) (by
        rw [Category.assoc, hι, pullback.condition])
      hom_inv_id := by apply pullback.hom_ext <;> simp
      inv_hom_id := by apply pullback.hom_ext <;> simp }
  have hJ0 : J0.hom ≫ w₀ = w := pullback.lift_fst _ _ _
  let E0 : W₀ ≅ pullback (ρ₀ ≫ f') t :=
    pullbackSymmetry h ρ₀ ≪≫ pullbackRightPullbackFstIso f' t ρ₀
  let E' := E0 ≪≫ E
  have hE' : E'.hom ≫ mV = mW₀ := by
    simp only [E', Iso.trans_hom, mV, Category.assoc]
    rw [hE]
    change E0.hom ≫ pullback.fst (ρ₀ ≫ f') t ≫ ρ₀ ≫ p = mW₀
    simp only [E0, Iso.trans_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    change (pullbackSymmetry h ρ₀).hom ≫ pullback.fst ρ₀ h ≫ ρ₀ ≫ p = mW₀
    calc
      _ = pullback.snd h ρ₀ ≫ ρ₀ ≫ p := by
        simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ ρ₀ ≫ p)
          (pullbackSymmetry_hom_comp_fst h ρ₀)
      _ = mW₀ := by
        simpa only [mW₀, w₀, Category.assoc] using
          (congrArg (fun a ↦ a ≫ p) (pullback.condition (f := h) (g := ρ₀))).symm
  let J := J0 ≪≫ E'
  have hJ : J.hom ≫ mV = mW := by
    simp only [J, Iso.trans_hom, Category.assoc]
    rw [hE']
    change J0.hom ≫ (w₀ ≫ h) ≫ p = (w ≫ h) ≫ p
    rw [← Category.assoc, ← Category.assoc, hJ0]
  obtain ⟨cV⟩ := nonempty_cohomology_iso_of_iso_over J mW mV hJ G (q : ℤ)
  exact ⟨c ≪≫ asIso (r ≫ strictHenselizationCohomologyComparison x' h F q) ≪≫
    (cohomology AddCommGrpCat.{u + 1} W (q : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso cF) ≪≫ cV⟩

end AlgebraicGeometry.Etale
