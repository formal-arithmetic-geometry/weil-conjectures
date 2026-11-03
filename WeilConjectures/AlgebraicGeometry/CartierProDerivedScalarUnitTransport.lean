/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison

import WeilConjectures.AlgebraicGeometry.Cartier.CartierDerivedUnitConjugation
import WeilConjectures.AlgebraicGeometry.CartierExtSquareConjugation
import WeilConjectures.AlgebraicGeometry.Cartier.CartierSourceComparisonGenerator
import all WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateTransportedPullbackNormalization

/-! # Conjugating scalar units and Ext squares

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md`, finite coefficient extension paragraph
(blueprint: lem-amb-cartier-pro-derived-scalar-unit-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
set_option synthInstance.maxSize 2048
attribute [local instance 1100] CommRing.toRing

private theorem scalar_unit_isCartier
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj G)
    (h : ProEtale.GeoCartierScalarUnit φ T F G η) :
    IsCartierDerivedScalarUnit φ T F G η := by
  simpa only [ProEtale.GeoCartierScalarUnit, Sheaf.IsDerivedBaseChange,
    Sheaf.derivedRestrictScalars, IsCartierDerivedScalarUnit, Category.assoc] using h

section SourceGenerator

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
  {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
local notation "A" => finiteTateCoefficient l E n

set_option maxHeartbeats 800000 in
-- The support-identification types include the full fixed-scalar sheaf presentations.
private theorem normalized_source_generator
    (α : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ≅
      cartierSupported l E n i)
    (hα : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map
        (supportedConstantUnit A i) ≫ α.hom =
      cartierConstantComparison A T ≫ cartierSupportedUnit l E n i)
    (U : T.ProEtᵒᵖ) (z : A) :
    (α.inv ≫ ProEtale.geoCartierSourceComparison A i).hom.app U
        (cartierSupportedGenerator l E n i U z) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.proEtaleBaseChange i).op.obj U) z := by
  have h := (ProEtale.cartierSourceComparison_fixes_supportedGenerator
    l E n i α hα).2.2 U z
  dsimp only [cartierSupported, cartierSupportedGenerator,
    ProEtale.cartierSourceComparisonSupportIso, ProEtale.geoCartierConstant,
    id, Iso.refl_hom] at h
  delta cartierSupported ProEtale.geoCartierConstant at h ⊢
  simpa only [Category.comp_id, cartierSupportedGenerator, id] using h

end SourceGenerator

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (a b : ℕ) (hab : a ≤ b) (r : ℕ)
  (hb : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E b) = 0)
  (ha : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E a) = 0)
  {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]

local notation "B" => finiteTateCoefficient l E b
local notation "A" => finiteTateCoefficient l E a
local notation "N" => l ^ (r + 1)
local notation "φ" => cartierCoefficientReduction l E a b hab
local notation "Res" => Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
local notation "PB" => ProEtale.comparisonUpperStar (ModuleCat B) T
local notation "PA" => ProEtale.comparisonUpperStar (ModuleCat A) T


set_option maxHeartbeats 800000 in
-- The comparison types retain the original finite Tate sheaf constructions.
private theorem normalized_root_scalar_generator
    (hT : IsUnit (l : Γ(T, ⊤)))
    (qb : ProEtale.geoCartierLine B N hb T ≅ finiteTateProSheaf l E b T 1)
    (qa : ProEtale.geoCartierLine A N ha T ≅ finiteTateProSheaf l E a T 1)
    (hqb : IsFiniteTateSiteComparison l E b T r hb 1 qb)
    (hqa : IsFiniteTateSiteComparison l E a T r ha 1 qa)
    (θ₀ : ProEtale.geoCartierLine B N hb T ⟶
      (Res).obj (ProEtale.geoCartierLine A N ha T))
    (hθ₀ : ∀ (U : T.Etaleᵒᵖ) (z : B) (w : (T.rootsOfUnitySheaf N).obj.obj U),
      θ₀.hom.app ((Scheme.toProEt T).op.obj U)
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app
          (Scheme.finiteEtaleTateLine T N B hb)).hom.app U
            (finiteEtaleTateOneGenerator B N T hb U z w)) =
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        (Scheme.finiteEtaleTateLine T N A ha)).hom.app U
          (finiteEtaleTateOneGenerator A N T ha U (φ z) w)) :
    ∀ (W : T.ProEtᵒᵖ) (z : B) (x : (purTwistZlOne T l).obj.obj W),
      (qb.inv ≫ θ₀ ≫ (Res).map qa.hom).hom.app W
          (finiteTateProGenerator l E b T W z x) =
        finiteTateProGenerator l E a T W (φ z) x := by
  intro W z x
  obtain ⟨U, f, w, hw⟩ := finite_root_tuple_presentation l T hT r 1 W (fun _ ↦ x)
  have hqb' := hqb U W f z w (fun _ ↦ x) hw
  have hqa' := hqa U W f (φ z) w (fun _ ↦ x) hw
  let ηb := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app
    (Scheme.finiteEtaleTateLine T N B hb)
  let ηa := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
    (Scheme.finiteEtaleTateLine T N A ha)
  let tb := finiteEtaleTateOneGenerator B N T hb U z (w 0)
  let ta := finiteEtaleTateOneGenerator A N T ha U (φ z) (w 0)
  have hbn : qb.hom.hom.app W
      ((ProEtale.geoCartierLine B N hb T).obj.map f.op (ηb.hom.app U tb)) =
      finiteTateProGenerator l E b T W z x := by
    simpa only [finiteTateEtalePowerGenerator, finiteTateProPowerGenerator,
      finiteEtaleTateTwist, ProEtale.geoCartierLine, ηb, tb] using hqb'
  have han : qa.hom.hom.app W
      ((ProEtale.geoCartierLine A N ha T).obj.map f.op (ηa.hom.app U ta)) =
      finiteTateProGenerator l E a T W (φ z) x := by
    simpa only [finiteTateEtalePowerGenerator, finiteTateProPowerGenerator,
      finiteEtaleTateTwist, ProEtale.geoCartierLine, ηa, ta] using hqa'
  have hbinv : qb.inv.hom.app W (finiteTateProGenerator l E b T W z x) =
      (ProEtale.geoCartierLine B N hb T).obj.map f.op (ηb.hom.app U tb) := by
    rw [← hbn]
    exact ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app W) qb.hom_inv_id) _
  change qa.hom.hom.app W (θ₀.hom.app W
    (qb.inv.hom.app W (finiteTateProGenerator l E b T W z x))) = _
  rw [hbinv]
  have hn := ConcreteCategory.congr_hom (θ₀.hom.naturality f.op) (ηb.hom.app U tb)
  simp only [ModuleCat.comp_apply] at hn
  rw [hn]
  have ht : θ₀.hom.app ((Scheme.toProEt T).op.obj U) (ηb.hom.app U tb) =
      ηa.hom.app U ta := hθ₀ U z (w 0)
  exact (congrArg (fun t ↦ qa.hom.hom.app W
    ((ProEtale.geoCartierLine A N ha T).obj.map f.op t)) ht).trans han

set_option maxHeartbeats 800000 in
-- The transported Ext terms retain the full coefficient sheaf constructions.
/-- Transport the given normalized scalar maps and their Ext square to the published
finite pro-etale twists. No Kummer class or Cartier hypothesis is constructed here.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md`, finite coefficient extension paragraph
(blueprint: lem-amb-cartier-pro-derived-scalar-unit-transport).

Proof: the source-comparison generator theorem says that each beta fixes constants;
its inverse does too. For a root-limit tensor choose the universal finite-root etale
test object at the common exponent. The normalization of qb identifies its inverse
image with the restricted comparison-unit root tensor. Naturality of theta0 and its
root formula transport this to the corresponding tensor over A. The normalization of
qa gives the claimed pro-etale generator. Unfolding GeoCartierScalarUnit identifies
its Hom bijections with IsCartierDerivedScalarUnit. The two conjugation lemmas then
preserve these bijections and the Ext square. All operations are isomorphism
composition, so identity reductions, empty support, and zero coefficients are included.
-/
theorem cartierProDerivedScalarUnitTransport
    (hT : IsUnit (l : Γ(T, ⊤)))
    (αb : (PB).obj ((lowerStar (ModuleCat.{u + 1} B) i).obj
      (ordinaryFiniteConstant B D)) ≅ cartierSupported l E b i)
    (αa : (PA).obj ((lowerStar (ModuleCat.{u + 1} A) i).obj
      (ordinaryFiniteConstant A D)) ≅ cartierSupported l E a i)
    (hαb : (PB).map (supportedConstantUnit B i) ≫ αb.hom =
      cartierConstantComparison B T ≫ cartierSupportedUnit l E b i)
    (hαa : (PA).map (supportedConstantUnit A i) ≫ αa.hom =
      cartierConstantComparison A T ≫ cartierSupportedUnit l E a i)
    (qb : ProEtale.geoCartierLine B N hb T ≅ finiteTateProSheaf l E b T 1)
    (qa : ProEtale.geoCartierLine A N ha T ≅ finiteTateProSheaf l E a T 1)
    (hqb : IsFiniteTateSiteComparison l E b T r hb 1 qb)
    (hqa : IsFiniteTateSiteComparison l E a T r ha 1 qa)
    (ηD : ProEtale.geoCartierConstant B D ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj
        (ProEtale.geoCartierConstant A D))
    (θ₀ : ProEtale.geoCartierLine B N hb T ⟶
      (Res).obj (ProEtale.geoCartierLine A N ha T))
    (hηD : ∀ (W : D.ProEtᵒᵖ) (z : B),
      ηD.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of B B))).app W z) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app W (φ z))
    (hθ₀ : ∀ (U : T.Etaleᵒᵖ) (z : B) (w : (T.rootsOfUnitySheaf N).obj.obj U),
      θ₀.hom.app ((Scheme.toProEt T).op.obj U)
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app
          (Scheme.finiteEtaleTateLine T N B hb)).hom.app U
            (finiteEtaleTateOneGenerator B N T hb U z w)) =
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
        (Scheme.finiteEtaleTateLine T N A ha)).hom.app U
          (finiteEtaleTateOneGenerator A N T ha U (φ z) w))
    (hηunit : ProEtale.GeoCartierScalarUnit φ T
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).obj (ProEtale.geoCartierConstant B D))
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj (ProEtale.geoCartierConstant A D))
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).map ηD))
    (hθunit : ProEtale.GeoCartierScalarUnit φ T
      (ProEtale.geoCartierLine B N hb T) (ProEtale.geoCartierLine A N ha T) θ₀)
    (gb : ProEtale.GeoCartierClass B N hb i) (ga : ProEtale.GeoCartierClass A N ha i)
    (hsquare : (Ext.mk₀ ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).map ηD)).comp
      (ga.mapExactFunctor Res) (zero_add 2) = gb.comp (Ext.mk₀ θ₀) (add_zero 2)) :
    let βb := αb.symm ≪≫ asIso (ProEtale.geoCartierSourceComparison B i)
    let βa := αa.symm ≪≫ asIso (ProEtale.geoCartierSourceComparison A i)
    let η := βb.hom ≫ (ProEtale.lowerStar (ModuleCat.{u + 1} B) i).map ηD ≫
      (Res).map βa.inv
    let θ := qb.inv ≫ θ₀ ≫ (Res).map qa.hom
    let cb := ((Ext.mk₀ βb.hom).comp gb (zero_add 2)).comp (Ext.mk₀ qb.hom) (add_zero 2)
    let ca := ((Ext.mk₀ βa.hom).comp ga (zero_add 2)).comp (Ext.mk₀ qa.hom) (add_zero 2)
    (∀ (U : T.ProEtᵒᵖ) (z : B),
      η.hom.app U (cartierSupportedGenerator l E b i U z) =
        cartierSupportedGenerator l E a i U (φ z)) ∧
    (∀ (U : T.ProEtᵒᵖ) (z : B) (x : (purTwistZlOne T l).obj.obj U),
      θ.hom.app U (finiteTateProGenerator l E b T U z x) =
        finiteTateProGenerator l E a T U (φ z) x) ∧
    IsCartierDerivedScalarUnit φ T (cartierSupported l E b i)
      (cartierSupported l E a i) η ∧
    IsCartierDerivedScalarUnit φ T (finiteTateProSheaf l E b T 1)
      (finiteTateProSheaf l E a T 1) θ ∧
    (Ext.mk₀ η).comp (ca.mapExactFunctor Res) (zero_add 2) =
      cb.comp (Ext.mk₀ θ) (add_zero 2) := by
  dsimp only
  let βb := αb.symm ≪≫ asIso (ProEtale.geoCartierSourceComparison B i)
  let βa := αa.symm ≪≫ asIso (ProEtale.geoCartierSourceComparison A i)
  have hηunit' : IsCartierDerivedScalarUnit φ T
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).obj (ProEtale.geoCartierConstant B D))
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj (ProEtale.geoCartierConstant A D))
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).map ηD) :=
    scalar_unit_isCartier φ T _ _ _ hηunit
  have hθunit' : IsCartierDerivedScalarUnit φ T _ _ θ₀ :=
    scalar_unit_isCartier φ T _ _ _ hθunit
  refine ⟨?_, ?_,
    isCartierDerivedScalarUnit_of_iso_conj φ T _ _ _ _ _ hηunit' βb βa.symm,
    isCartierDerivedScalarUnit_of_iso_conj φ T _ _ _ _ _ hθunit' qb.symm qa,
    cartier_ext_square_conjugation φ T _ _ gb ga hsquare βb βa qb qa⟩
  · intro U z
    let zb := (toSheafify (Scheme.ProEt.topology D)
      ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of B B))).app
        ((Scheme.proEtaleBaseChange i).op.obj U) z
    let za := (toSheafify (Scheme.ProEt.topology D)
      ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
        ((Scheme.proEtaleBaseChange i).op.obj U) (φ z)
    have hbfix : βb.hom.hom.app U (cartierSupportedGenerator l E b i U z) =
        zb := normalized_source_generator l E b i αb hαb U z
    have hafix : βa.hom.hom.app U (cartierSupportedGenerator l E a i U (φ z)) =
        za := normalized_source_generator l E a i αa hαa U (φ z)
    have hainv : βa.inv.hom.app U za =
        cartierSupportedGenerator l E a i U (φ z) := by
      calc
        _ = βa.inv.hom.app U (βa.hom.hom.app U
            (cartierSupportedGenerator l E a i U (φ z))) := congrArg _ hafix.symm
        _ = _ := ConcreteCategory.congr_hom
          (congrArg (fun q ↦ q.hom.app U) βa.hom_inv_id) _
    change βa.inv.hom.app U
      (((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).map ηD).hom.app U
        (βb.hom.hom.app U (cartierSupportedGenerator l E b i U z))) = _
    rw [hbfix]
    change βa.inv.hom.app U (ηD.hom.app ((Scheme.proEtaleBaseChange i).op.obj U)
      ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of B B))).app
          ((Scheme.proEtaleBaseChange i).op.obj U) z)) = _
    exact (congrArg (fun t ↦ βa.inv.hom.app U t)
      (hηD ((Scheme.proEtaleBaseChange i).op.obj U) z)).trans hainv
  · exact normalized_root_scalar_generator l E a b hab r hb ha hT qb qa hqb hqa θ₀ hθ₀

end AlgebraicGeometry.Etale
