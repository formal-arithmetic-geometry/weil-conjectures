/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.WeilSheaf.Category
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusComparison
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

/-! # An ordinary coefficient model intertwining geometric Frobenius

Ordinary native adic sheaves admit a small sectionwise coefficient realization, together with
an internal Hom comparison, intertwining the Frobenius pullback.

## Implementation details

The model is built on the bounded pro-étale site of the geometric fibre, made small with
`AsSmall`, with inverse geometric Frobenius acting by postcomposition; the coefficient ring is
the restriction of `comparisonRing l`. Only ordinary modules occur: there are no structure maps
`θ` and no fixed-pair categories. The Hom comparison `sigmaHom` of a presentation is normalized
uniquely by evaluation (`sigmaHom_evaluation`).

## References

* Stacks Project, Tags 00YV and 03D6.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwistedActionRingedSite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Ordinary module sheaves with their Frobenius comparison, before forming any category of
fixed pairs. -/
structure NativeFrobeniusRingedModel
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] where
  /-- The small ordinary pro-etale model. -/
  C : Type (u + 1)
  /-- The category structure includes morphisms in the same universe. -/
  [category : SmallCategory C]
  /-- Pullbacks are needed for the twisted action-site construction. -/
  [pullbacks : HasPullbacks C]
  /-- The ordinary topology. -/
  J : GrothendieckTopology C
  /-- Inverse geometric Frobenius on the site. -/
  s : C ≌ C
  /-- Translation preserves sheaves. -/
  [continuous : s.functor.IsContinuous J J]
  /-- Inverse translation preserves sheaves. -/
  [inverseContinuous : s.inverse.IsContinuous J J]
  /-- The continuous, locally finite-subextension coefficient ring. -/
  R : Sheaf J CommRingCat.{u + 1}
  /-- The coefficient identification preserves values of functions. -/
  a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj R ≅ R
  /-- Ordinary sectionwise modules realize the actual native adic modules. -/
  E : Modules R ≌ ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  /-- Sums of module maps are unchanged. -/
  additive : E.functor.Additive
  /-- The ordinary realization intertwines the two actual pullbacks. -/
  comparison : E.functor ⋙ WeilSheaf.frobeniusPullback k₀ l X ≅
    sigma J s R a ⋙ E.functor

  /-- The ordinary internal Hom comparison, before imposing a Weil structure. -/
  hom (M N : Modules R) :
    E.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
      (ProEtale.AdicSheaf.ihom (E.functor.obj M)).obj (E.functor.obj N)
  /-- Ordinary local maps act by precomposition and postcomposition. -/
  hom_naturality {M M' N N' : Modules R} (f : M' ⟶ M) (g : N ⟶ N') :
    E.functor.map (SheafOfModules.homObjMap (R := R) f g) ≫ (hom M' N').hom =
      (hom M N).hom ≫ (Mod.ihomMap (E.functor.map f)).app _ ≫
        (ProEtale.AdicSheaf.ihom (E.functor.obj M')).map (E.functor.map g)
  /-- The ordinary Hom comparison commutes with translation. -/
  hom_frobenius (P : Presentation J s R a) (M N : Modules R) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (hom M N).hom ≫
        (ProEtale.adicLowerStarCompIhomIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
          (E.functor.obj M)).inv.app (E.functor.obj N) ≫
        (Mod.ihomMap (comparison.app M).inv).app _ ≫
          (ProEtale.AdicSheaf.ihom (E.functor.obj ((sigma J s R a).obj M))).map
            (comparison.app N).hom =
      comparison.hom.app (SheafOfModules.homObj (R := R) M N) ≫
        E.functor.map (P.sigmaHom M N).hom ≫ (hom _ _).hom

attribute [instance] NativeFrobeniusRingedModel.category NativeFrobeniusRingedModel.pullbacks
  NativeFrobeniusRingedModel.continuous NativeFrobeniusRingedModel.inverseContinuous

/-- Ordinary native adic sheaves have a small sectionwise coefficient realization
intertwining their Frobenius pullback. -/
theorem native_frobenius_ringed_model
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Nonempty (NativeFrobeniusRingedModel k₀ l X) := by
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).1
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).2
  obtain ⟨H⟩ := ProEtale.adicModuleHomComparisonCore l Y
  obtain ⟨c, hc⟩ := ProEtale.NativeFrobenius.nativeFrobeniusComparison Y l g H
  refine ⟨{
    C := WeilConjectures.WeilFrobeniusAction.Site Y
    category := inferInstance
    pullbacks := ?_
    J := WeilConjectures.WeilFrobeniusAction.topology Y
    s := WeilConjectures.WeilFrobeniusAction.translation g
    R := ProEtale.NativeFrobenius.ring Y l
    a := ProEtale.NativeFrobenius.ringIso Y l g
    E := ProEtale.NativeFrobenius.equivalence Y l
    additive := inferInstance
    comparison := c
    hom := ProEtale.NativeFrobenius.homComparison Y l H
    hom_naturality := ?_
    hom_frobenius := hc }⟩
  · exact Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1} :
        Y.ProEt ≌ WeilConjectures.WeilFrobeniusAction.Site Y).inverse
  · intro M M' N N' f h
    exact ProEtale.NativeFrobenius.homComparison_naturality Y l H f h

end AlgebraicGeometry.ProEtaleWeilSheaf
