/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarExact

/-!
# Properties of the direct image with compact support of Weil complexes

This file collects the properties of `Rf₀!` on Weil complexes used in the Deligne–Laumon
reductions.

- `Rf₀!` of a Weil sheaf has no cohomology in negative degrees
  (`AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`): it is computed
  as `Rḡ_*` of the extension by zero along a compactification, a right derived functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

section

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support of Weil complexes is the functor attached to the
chosen compactification on the derived categories of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.derivedLowerShriekCompιIso :
    WeilComplex.derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (HasCompactification.compactification f
          (hf := hasCompactification_of_over (k₀ := k₀) f)) := by
  unfold WeilComplex.derivedLowerShriek
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The higher direct images with compact support are the cohomology sheaves of `Rf₀!` of a
Weil sheaf placed in degree zero. -/
noncomputable def WeilSheaf.higherLowerShriekIso (r : ℕ) :
    WeilSheaf.higherLowerShriek k₀ l f r ≅
      WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.homologySheaf r :=
  Iso.refl _

attribute [local instance] Compactification.over in
/-- The direct image with compact support of a Weil sheaf has no cohomology in negative
degrees: `Rf₀! = Rḡ_* ∘ ī_!` for a compactification, and `ī_!` is exact while `Rḡ_*` is a right
derived functor. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (F : WeilSheaf k₀ l X) {a : ℤ}
    (ha : a < 0) :
    IsZero ((WeilComplex.homologySheaf a).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F))) := by
  let c := HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)
  let e : ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)).obj ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj F.obj)) :=
    (WeilComplex.derivedLowerShriekCompιIso f).app _ ≪≫
      (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).mapIso
        (WeilSheaf.toComplexCompιIso.app F) ≪≫
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app F.obj)
  have := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj F.obj)
  have : ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)).obj.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  exact WeilComplex.isZero_homologySheaf_obj (DerivedCategory.isZero_of_isGE _ 0 a ha)

variable {f} in
attribute [local instance] Compactification.over in
/-- **Independence of the compactification.** On Weil complexes, the direct image with compact
support `Rf₀!` is computed by any compactification `X ⟶[i] Z ⟶[g] Y` of `f`: it is isomorphic to
`Rḡ_* ∘ ī_!` for every compactification, not only for the chosen one
(blueprint: `prop-functor-package`, item 2, with the descent to `ℚ̄_ℓ`-Weil complexes of item 1).
-/
theorem WeilComplex.nonempty_derivedLowerShriekCompι_iso (c : Compactification f) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c) :=
  sorry

end

/-- **Properness law.** For a proper morphism `f`, the direct image with compact support of Weil
complexes is the derived direct image: `Rf₀! ≅ Rf₀*`
(blueprint: `prop-functor-package`, item 3). -/
theorem WeilComplex.nonempty_derivedLowerShriek_iso_derivedLowerStar (f : X ⟶ Y) [IsProper f]
    [f.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ≅ WeilComplex.derivedLowerStar (l := l) f) :=
  sorry

/-- **Composition law.** For composable morphisms `X ⟶[f] Z ⟶[g] Y` of `k₀`-schemes, the direct
images with compact support of Weil complexes compose: `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`
(blueprint: `prop-functor-package`, item 3, used as `lem-zl-shriek-composition`). -/
theorem WeilComplex.nonempty_derivedLowerShriek_comp_iso {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Z) (g : Z ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l (f ≫ g) ≅
      WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.derivedLowerShriek k₀ l g) :=
  sorry

/-- **Compact support base change.** For a pullback square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h₀^* ∘ Rf₀! ≅ Rf'₀! ∘ g₀^*` on Weil complexes
(blueprint: `prop-functor-package`, item 4). -/
theorem WeilComplex.nonempty_derivedLowerShriek_comp_upperStar_iso {X' Y' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.upperStar h ≅
      WeilComplex.upperStar g ⋙ WeilComplex.derivedLowerShriek k₀ l f') :=
  sorry

open Pretriangulated in
/-- **The open–closed triangle.** Let `j : U ⟶ X` be an open immersion whose closed complement is
`i : Z ⟶ X`. Every Weil complex `K` on `X` sits in a distinguished triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`
(blueprint: `prop-sf-open-closed-triangle-all-stages`). -/
theorem WeilComplex.exists_distTriang_openClosed {U Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {i : Z ⟶ X} [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (K : WeilComplex k₀ l X) :
    ∃ T : Triangle (WeilComplex k₀ l X), T ∈ distTriang _ ∧
      Nonempty (T.obj₁ ≅ (WeilComplex.derivedLowerShriek k₀ l j).obj
        ((WeilComplex.upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (WeilComplex.derivedLowerStar i).obj ((WeilComplex.upperStar i).obj K)) :=
  sorry

/-- **Exactness of finite direct images.** For a finite morphism `p`, the higher direct images
`Rʳp₀*` of Weil sheaves vanish for `r > 0`
(blueprint: `lemma-weil-pbc-finite-direct-image-exact`). -/
theorem WeilSheaf.isZero_higherLowerStar_of_isFinite (p : X ⟶ Y) [IsFinite p]
    [p.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) (hr : 0 < r) (G : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerStar p r).obj G) :=
  sorry

/-- The derived direct image of Weil complexes is the right derived functor of the pushforward
of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.derivedLowerStarCompιIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex.derivedLowerStar (l := l) φ ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor := by
  unfold WeilComplex.derivedLowerStar
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The higher direct images are the cohomology sheaves of the derived direct image of a Weil
sheaf placed in degree zero. -/
noncomputable def WeilSheaf.higherLowerStarIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) :
    WeilSheaf.higherLowerStar (l := l) φ r ≅
      WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerStar (k₀ := k₀) φ ⋙
        WeilComplex.homologySheaf r :=
  Iso.refl _

attribute [local instance] Compactification.over in
/-- The direct image with compact support attached to a compactification is the extension by
zero followed by the derived direct image. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ≅
      (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor :=
  Iso.refl _

/-- The extension by zero of Weil sheaves is the extension by zero of pro-étale Weil sheaves. -/
noncomputable def WeilSheaf.extensionByZeroCompιIso (j : X ⟶ Y) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf.extensionByZero (l := l) j ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.extensionByZero k₀ l j := by
  unfold WeilSheaf.extensionByZero
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

open Functor in
attribute [local instance] Compactification.over in
/-- The higher direct images with compact support of a Weil sheaf are computed by any
compactification `X ⟶[i] Z ⟶[g] Y` of `f` with `i` quasi-compact: `Rʳf₀!F ≅ Rʳg₀*(i₀!F)`. -/
theorem WeilSheaf.nonempty_higherLowerShriek_iso_higherLowerStar (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (c : Compactification f) [QuasiCompact c.i]
    (r : ℕ) (F : WeilSheaf k₀ l X) :
    Nonempty ((WeilSheaf.higherLowerShriek k₀ l f r).obj F ≅
      (WeilSheaf.higherLowerStar c.g r).obj ((WeilSheaf.extensionByZero c.i).obj F)) := by
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriekCompι_iso (k₀ := k₀) (l := l) c
  let ιS := (WeilSheaf.objectProperty k₀ l X).ι
  let single := DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0
  let extP := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  let extW := WeilSheaf.extensionByZero (k₀ := k₀) (l := l) c.i
  let Rg := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor
  let Hd := DerivedCategory.homologyFunctor (ProEtaleWeilSheaf k₀ l Y) r
  let E : WeilSheaf.higherLowerShriek k₀ l f r ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅
      (extW ⋙ WeilSheaf.higherLowerStar c.g r) ⋙ (WeilSheaf.objectProperty k₀ l Y).ι :=
    isoWhiskerRight (WeilSheaf.higherLowerShriekIso f r) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (WeilComplex.homologySheafCompιIso r) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight e Hd ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight WeilSheaf.toComplexCompιIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft ιS (isoWhiskerLeft single
      (isoWhiskerRight (ProEtaleWeilSheaf.rightDerivedLowerShriekIso (k₀ := k₀) (l := l) f c)
        Hd ≪≫ Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (extP.mapDerivedCategorySingleFunctor 0) _ ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (WeilSheaf.extensionByZeroCompιIso c.i).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft extW ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight WeilSheaf.toComplexCompιIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft WeilSheaf.toComplex ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (WeilComplex.derivedLowerStarCompιIso c.g).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (WeilComplex.homologySheafCompιIso r).symm ≪≫
        (Functor.associator _ _ _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (WeilSheaf.higherLowerStarIso c.g r).symm _) ≪≫
    (Functor.associator _ _ _).symm
  exact ⟨(((WeilSheaf.objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso E).app F⟩

end AlgebraicGeometry
