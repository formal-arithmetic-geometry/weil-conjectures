/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeSourceIso
import WeilConjectures.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Comparison invariance under nested source-open restriction

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Computing the comparison on a smaller open after restricting to a larger open
preserves and reflects invertibility. This is a coordinate transport statement:
it has no cover, compactness, quasi-coherence or local-isomorphism hypotheses. -/
theorem singleComplexOpenComparison_nested_isIso_iff
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (W Z : X.Opens) (hZW : Z ≤ W) :
    let hW : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
        (pullback.fst g' W.ι ≫ f') ≫ g := by
      rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
    let φW : (derivedPullback (pullback.snd g' W.ι)).obj
        ((derivedPullback W.ι).obj K) ⟶
        (derivedPullback (pullback.fst g' W.ι)).obj K' :=
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' W.ι) W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' W.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' W.ι)).map φ)
    IsIso (singleComplexOpenComparison f f' g g' h K K' φ Z) ↔
      IsIso (singleComplexOpenComparison (W.ι ≫ f) (pullback.fst g' W.ι ≫ f')
        g (pullback.snd g' W.ι) hW ((derivedPullback W.ι).obj K)
        ((derivedPullback (pullback.fst g' W.ι)).obj K') φW (W.ι ⁻¹ᵁ Z)) := by
  classical
  intro hW phiW
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let A := W.ι ⁻¹ᵁ Z
  let e := Scheme.Opens.isoOfLE hZW
  let q := pullback.snd g' W.ι
  let p := pullback.fst g' W.ι
  let t := pullback.snd q A.ι
  let r := pullback.fst q A.ι
  let e' : pullback q A.ι ≅ pullback g' Z.ι :=
    pullbackLeftPullbackSndIso g' W.ι A.ι ≪≫
      asIso (pullback.map g' (A.ι ≫ W.ι) g' Z.ι (𝟙 _) e.hom (𝟙 _)
        (by simp) (by simp [e, A]))
  have hp : e'.hom ≫ pullback.fst g' Z.ι = r ≫ p := by
    simp [e', r, p, q]
  have hq : e'.hom ≫ pullback.snd g' Z.ι = t ≫ e.hom := by
    simp [e', t, q]
  let KW := (derivedPullback W.ι).obj K
  let KW' := (derivedPullback p).obj K'
  let KZ := (derivedPullback Z.ι).obj K
  let KZ' := (derivedPullback (pullback.fst g' Z.ι)).obj K'
  let phiZ := (c (pullback.snd g' Z.ι) Z.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := Z.ι)).symm) ≫
    (c (pullback.fst g' Z.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' Z.ι)).map φ
  let phiA := (c t A.ι).hom.app KW ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW)
      (pullback.condition (f := q) (g := A.ι)).symm) ≫
    (c r q).inv.app KW ≫ (derivedPullback r).map phiW
  let alpha : (derivedPullback e.hom).obj KZ ≅ (derivedPullback A.ι).obj KW :=
    (c e.hom Z.ι).app K ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Scheme.Opens.isoOfLE_hom_ι hZW)) ≪≫ (c A.ι W.ι).symm.app K
  let beta : (derivedPullback e'.hom).obj KZ' ≅ (derivedPullback r).obj KW' :=
    (c e'.hom (pullback.fst g' Z.ι)).app K' ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K') hp) ≪≫
      (c r p).symm.app K'
  have hphi : (derivedPullback t).map alpha.hom ≫ phiA =
      (c t e.hom).hom.app KZ ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KZ) hq.symm) ≫
      (c e'.hom (pullback.snd g' Z.ι)).inv.app KZ ≫
      (derivedPullback e'.hom).map phiZ ≫ beta.hom := by
    exact singleComplex_nested_coefficient_coherence g' K K' φ W Z hZW e' hp hq
  have hf : e.hom ≫ (Z.ι ≫ f) = A.ι ≫ (W.ι ≫ f) := by
    simp [e, A]
  have hf' : e'.hom ≫ (pullback.fst g' Z.ι ≫ f') = r ≫ (p ≫ f') := by
    rw [← Category.assoc, hp, Category.assoc]
  have hZ : pullback.snd g' Z.ι ≫ (Z.ι ≫ f) =
      (pullback.fst g' Z.ι ≫ f') ≫ g := by
    rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
  have h0 : t ≫ (e.hom ≫ (Z.ι ≫ f)) =
      (e'.hom ≫ (pullback.fst g' Z.ι ≫ f')) ≫ g := by
    rw [← Category.assoc, ← hq, Category.assoc, hZ, ← Category.assoc]
  have transport := exists_derivedBaseChange_source_iso
    (Z.ι ≫ f) (pullback.fst g' Z.ι ≫ f') g (pullback.snd g' Z.ι) hZ
    e e' t hq.symm h0 KZ KZ' ((derivedPullback A.ι).obj KW)
    ((derivedPullback r).obj KW') phiZ phiA alpha beta hphi
  revert transport h0
  rw [hf, hf']
  intro h0 transport
  obtain ⟨a, b, hab⟩ := transport
  change IsIso (schemeDerivedBaseChangeMap (Z.ι ≫ f)
      (pullback.fst g' Z.ι ≫ f') g (pullback.snd g' Z.ι) hZ KZ ≫
        (schemeDerivedDirectImage (pullback.fst g' Z.ι ≫ f')).map phiZ) ↔
    IsIso (schemeDerivedBaseChangeMap (A.ι ≫ (W.ι ≫ f))
      (r ≫ (p ≫ f')) g t _ ((derivedPullback A.ι).obj KW) ≫
        (schemeDerivedDirectImage (r ≫ (p ≫ f'))).map phiA)
  rw [← isIso_comp_right_iff _ b.hom, hab, isIso_comp_left_iff a.hom]

end AlgebraicGeometry
