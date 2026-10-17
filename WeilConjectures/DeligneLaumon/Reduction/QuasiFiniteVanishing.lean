/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# Vanishing of direct images of Weil sheaves

The derived direct image `Rf₀*G` and the direct image with compact support `Rf₀!G` of a Weil
sheaf are concentrated in degrees `≥ 0`. For a finite morphism `p` the higher direct images
`Rʳp₀*G` vanish for `r > 0`, and so, by Zariski's main theorem, do the higher direct images with
compact support `Rʳf₀!G` along a separated quasi-finite morphism `f`. These statements do not
involve weights; they are used both by the weight reductions of
`WeilConjectures.DeligneLaumon.Reduction.FormalSteps` and by the computation of the local
Frobenius of quasi-finite direct images in
`WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg` and
  `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`: vanishing in
  negative degrees.
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`: blueprint
  `lemma-weil-pbc-finite-direct-image-exact`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`: blueprint
  `sk-l-dl-general-quasifinite`, `lem-zl-quasi-finite`, part 1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section UpperStar

variable {W X : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (h : W ⟶ X) [h.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf, placed in
degree zero. -/
noncomputable def WeilComplex.upperStarToComplexIso (G : WeilSheaf k₀ l X) :
    (WeilComplex.upperStar h).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj G) :=
  ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategorySingleFunctor 0).app G.obj)

end UpperStar

/-- The derived direct image `Rf₀*G` of a Weil sheaf is concentrated in degrees `≥ 0`: it is
computed by `f₀*` applied to an injective resolution of `G`. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {n : ℤ} (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  have : ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G)).obj.IsGE 0 :=
    (ProEtaleWeilSheaf.lowerStar k₀ l f).isGE_rightDerivedFunctor_obj_singleFunctor G.obj
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over in
/-- The direct image with compact support `Rf₀!G` of a Weil sheaf is concentrated in degrees
`≥ 0`: it is `Rḡ_*` applied to the extension by zero of `G`, a sheaf. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (G : WeilSheaf k₀ l X) {n : ℤ}
    (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have e := (Functor.mapDerivedCategorySingleFunctor
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i) 0).app G.obj
  have h := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj G.obj)
  have : _root_.DerivedCategory.TStructure.t.IsGE
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj
          G.obj)) 0 := h
  have h' := _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso e.symm) 0
  have h'' : ((WeilComplex.derivedLowerShriek k₀ l f).obj
      (WeilSheaf.toComplex.obj G)).obj.IsGE 0 := h'
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

end LowerShriek

/-- The pushforward of sheaves of modules over the constant `ℓ`-adic sheaf is exact as soon as
the pushforward of the underlying sheaves of `ℚ̄_ℓ`-modules is: the forgetful functor reflects
finite colimits and commutes with the pushforwards. -/
theorem ProEtale.preservesFiniteColimits_adicLowerStar_of_preservesFiniteColimits
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [PreservesFiniteColimits ((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))])] :
    PreservesFiniteColimits (g)_*ᵃ[l] :=
  have : PreservesFiniteColimits ((g)_*ᵃ[l] ⋙ ProEtale.AdicSheaf.forget Y) :=
    inferInstanceAs (PreservesFiniteColimits
      (ProEtale.AdicSheaf.forget X ⋙ (g)_*[WeilCoefficients.{u} l]))
  preservesFiniteColimits_of_reflects_of_preserves _ (ProEtale.AdicSheaf.forget Y)

/-- The higher direct images `Rʳp₀*G` (`r > 0`) of a Weil sheaf vanish along any morphism `p`
whose base change `p̄` to the geometric fibres has an exact pushforward of `ℓ`-adic sheaves:
then `p₀*` is exact on pro-étale Weil sheaves, so `Rp₀*` is `p₀*` applied levelwise
(`CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory`). -/
theorem WeilSheaf.isZero_higherLowerStar_of_preservesFiniteColimits {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (p : T ⟶ Y)
    [p.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFiniteType p] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [PreservesFiniteColimits
      ((Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))_*ᵃ[l])]
    (G : WeilSheaf k₀ l T) (r : ℕ) (hr : 0 < r) :
    IsZero ((WeilSheaf.higherLowerStar p r).obj G) := by
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l p) :=
    Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso _
  change IsZero ((WeilComplex.homologySheaf r).obj _)
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  let F := ProEtaleWeilSheaf.lowerStar k₀ l p
  let e := F.rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor _ 0).obj G.obj) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app G.obj
  exact (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor _ 0).obj (F.obj G.obj))
    0 r (by exact_mod_cast hr)).of_iso ((DerivedCategory.homologyFunctor _ r).mapIso e)

/-- **Finite pushforward is exact on pro-étale sheaves of `ℚ̄_ℓ`-modules**: for a finite morphism
`g : X ⟶ Y`, the direct image `g_*` of pro-étale sheaves of (discrete) `ℚ̄_ℓ`-modules preserves
finite colimits. This is the pro-étale analogue of the exactness of finite direct images for
étale sheaves (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), and the
input of the passage to `ℚ̄_ℓ`-coefficients of blueprint `def-weil-pbc-qbar-category`.

It is not yet available: unlike for closed immersions, covers of `X ×_Y V` are not refined by
base changes of covers of `V`, and a finite algebra over a w-contractible ring need not be
w-contractible (its `π₀` need not be extremally disconnected), so the closed-immersion argument
via henselian lifts does not apply directly. -/
theorem ProEtale.preservesFiniteColimits_lowerStar_padicAlgCl_of_isFinite {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsFinite g] :
    PreservesFiniteColimits ((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))]) :=
  sorry

/-- **Finite direct images are exact** for Weil sheaves (blueprint `def-weil-pbc-qbar-category`):
for a finite morphism `p : T ⟶ Y` of `k₀`-schemes, the higher direct images `Rʳp₀*G` of a Weil
sheaf vanish for `r > 0`.

This is the passage to pro-étale `ℚ̄_ℓ`-coefficients of the exactness of finite direct images
for étale sheaves, which is proved as
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedFunctor_lowerStar_of_isFinite`. By
`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_preservesFiniteColimits` it reduces to
the exactness of the pushforward of pro-étale sheaves of `ℚ̄_ℓ`-modules along the finite
morphism `p̄`, which is
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_padicAlgCl_of_isFinite`. -/
theorem WeilSheaf.isZero_higherLowerStar_of_isFinite {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (p : T ⟶ Y)
    [IsFinite p] [p.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T) (r : ℕ) (hr : 0 < r) :
    IsZero ((WeilSheaf.higherLowerStar p r).obj G) := by
  have : IsFinite (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) p _ ‹_›
  have := ProEtale.preservesFiniteColimits_lowerStar_padicAlgCl_of_isFinite (l := l)
    (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
  have := ProEtale.preservesFiniteColimits_adicLowerStar_of_preservesFiniteColimits (l := l)
    (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀))))
  exact WeilSheaf.isZero_higherLowerStar_of_preservesFiniteColimits p G r hr

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the higher direct images
with compact support `Rʳf₀!` vanish for `r > 0` (blueprint: `sk-l-dl-general-quasifinite`,
`lem-zl-quasi-finite`, part 1).

Zariski's main theorem factors `f` as a quasi-compact open immersion `j : X ⟶ T` followed by a
finite morphism `p : T ⟶ Y`, so that `Rf₀! ≅ Rp₀! ∘ Rj₀! ≅ Rp₀* ∘ j₀!`; the extension by zero
`j₀!` is exact and so is the finite direct image `p₀*`
(`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`). -/
theorem isZero_higherLowerShriek_of_quasiFinite (r : ℕ) (hr : 0 < r) (F : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let : T.Over (Spec (CommRingCat.of k₀)) := ⟨p ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change j ≫ p ≫ Y ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hjp, comp_over]⟩
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ _))
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := inferInstanceAs (QuasiCompact (p ≫ _))
  have : QuasiSeparated (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (p ≫ _))
  subst hjp
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j p
  obtain ⟨e'⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j F
  exact (WeilSheaf.isZero_higherLowerStar_of_isFinite p _ r hr).of_iso
    ((WeilComplex.homologySheaf r).mapIso (e.app (WeilSheaf.toComplex.obj F) ≪≫
      (WeilComplex.derivedLowerShriek k₀ l p).mapIso e' ≪≫
      WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar p _))

end QuasiFinite

end AlgebraicGeometry
