/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.PurityRelativeKummerMaps
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

import Sheaf.Paper.PurityRelativeLineCohomology
import Sheaf.Paper.PurityRelativePuncturedCohomology
import Sheaf.Paper.PurityRelativeKummerExchange
import Mathlib.CategoryTheory.Adjunction.Mates
/-!
# Relative affine-line acyclicity and the actual Kummer generator

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.md
(blueprint: prop-pur-gm-relative-kummer).

All objects below are actual finite-coefficient module sheaves on the small pro-etale
site. The maps are the units and canonical exchange mates of the published functors.
The generator is homology of the adjoint of the coordinate's actual Kummer boundary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] ProEtale.upperStar ProEtale.lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.derivedBaseChangeMap
  ProEtale.leftDerivedUpperStarSquareIso
  ProEtale.comparisonUpperStar Etale.upperStar
  Functor.mapDerivedCategory Functor.mapDerivedCategoryPlus
  Adjunction.derivedAdjunction Adjunction.derivedPlus

section
variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}

private theorem isIso_mate_of_units (adj : L ⊣ R) (adj' : L' ⊣ R')
    (alpha : TwoSquare G L L' H) (X : C)
    [IsIso (adj.unit.app X)] [IsIso (adj'.unit.app (G.obj X))]
    [IsIso (alpha.natTrans.app X)] :
    IsIso ((mateEquiv adj adj' alpha).natTrans.app (L.obj X)) := by
  have hu := unit_mateEquiv adj adj' alpha X
  change G.map (adj.unit.app X) ≫
      (mateEquiv adj adj' alpha).natTrans.app (L.obj X) =
    adj'.unit.app (G.obj X) ≫ R'.map (alpha.natTrans.app X) at hu
  have : IsIso (G.map (adj.unit.app X) ≫
      (mateEquiv adj adj' alpha).natTrans.app (L.obj X)) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.map (adj.unit.app X)) _
end

private theorem baseChange_at_pullback_isIso (P : PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v f' f g)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (hf : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).unit.app K))
    (hf' : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f').unit.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj K))) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq).app
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj K)) := by
  have := hf
  have := hf'
  unfold ProEtale.derivedBaseChangeMap
  exact isIso_mate_of_units
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f')
    (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient) sq).hom K

private theorem coefficient_pullback_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) (twisted : Bool) :
    IsIso (P.derivedCoefficientPullback h f twisted) := by
  have hc : IsIso (P.constantPullback f) := by
    unfold constantPullback
    infer_instance
  have ht : IsIso (P.twistPullback h f) := by
    have := P.isIso_twistEtalePullback h f hr
    unfold twistPullback
    infer_instance
  cases twisted <;>
    dsimp only [derivedCoefficientPullback, Functor.mapWithComparison] <;> infer_instance

private theorem unit_isIso_of_relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) (twisted : Bool)
    [IsIso (P.relativeUnit h f twisted)] :
    IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted)) := by
  have := coefficient_pullback_isIso P h f hr twisted
  have hi : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
          (P.derivedCoefficientPullback h f twisted)) := by
    exact ‹IsIso (P.relativeUnit h f twisted)›
  exact IsIso.of_isIso_comp_right _
    ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
      (P.derivedCoefficientPullback h f twisted))

private theorem line_exchange_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k))
    (hY : P.RelativeKummerConclusions h Y a)
    (hY' : P.RelativeKummerConclusions h Y' (g ≫ a)) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
        (P.derivedSheaf h (Line Y) true)) := by
  have hy : IsIso (P.relativeUnit h (lineProjection Y) true) := by
    exact hY.2.1
  have hy' : IsIso (P.relativeUnit h (lineProjection Y') true) := by
    exact hY'.2.1
  have hu := unit_isIso_of_relativeUnit P h (lineProjection Y) (P.exponent_isUnit Y a) true
  have hu' := unit_isIso_of_relativeUnit P h (lineProjection Y')
    (P.exponent_isUnit Y' (g ≫ a)) true
  have hco := coefficient_pullback_isIso P h g (P.exponent_isUnit Y a) true
  have hco' := coefficient_pullback_isIso P h (lineProjection Y)
    (P.exponent_isUnit Y a) true
  have hgu : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y')).unit.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj
          (P.derivedSheaf h Y true))) :=
    (NatTrans.isIso_app_iff_of_iso _ (asIso (P.derivedCoefficientPullback h g true))).2 hu'
  have hx' := baseChange_at_pullback_isIso P
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq
    (P.derivedSheaf h Y true) hu hgu
  exact (NatTrans.isIso_app_iff_of_iso _
    (asIso (P.derivedCoefficientPullback h (lineProjection Y) true))).1 hx'


attribute [local irreducible] constantPullback twistPullback derivedCoefficientPullback
  relativeUnit kummerGenerator derivedSheaf coefficientSheaf constant twist
  constantEtale twistEtale coordinateKummer

private theorem relative_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u}) (a : B ⟶ Spec (CommRingCat.of P.field.k)) :
    P.RelativeKummerConclusions h B a := by
  have line (twisted : Bool) : IsIso (P.relativeUnit h (lineProjection B) twisted) := by
    exact relative_line_cohomology P h B a twisted
  have ht := line true
  have hle : (P.derivedSheaf h B true).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (eqToIso (P.derivedSheaf_true_eq h B)).symm 0
  have hle' : ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (lineProjection B)).rightDerivedFunctor.obj (P.derivedSheaf h (Line B) true)).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (asIso (P.relativeUnit h (lineProjection B) true)) 0
  refine ⟨line false, ht, ?_, relative_punctured_cohomology P h B a⟩
  intro m hm
  exact DerivedCategory.isZero_of_isLE _ 0 _ (by exact_mod_cast hm)

private theorem relative_baseChange (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k)) :
    P.KummerBaseChangeConclusions h g a := by
  have hB := relative_conclusions P h B a
  have hB' := relative_conclusions P h B' (g ≫ a)
  have he := relative_kummer_exchange P h g a hB hB'
  refine ⟨he.1, line_exchange_isIso P h g a hB hB', ?_⟩
  exact he.2

/-- The affine line and punctured line over a separated finite-type k-scheme, with
canonical units, the actual Kummer generator, higher vanishing and both kinds of
base change, including geometric points which need not be of finite type.
Source: blueprint sk-prop-a1-kummer, prop-pur-gm-relative-kummer
(blueprint: prop-pur-gm-relative-kummer).

Proof:
1. Put r=ell^(n/e). The finite Kummer level gives rA=0 and A finite free over Z/r.
Since ell differs from p, r is invertible on k-schemes. A primitive r-th root in k
identifies the root line with constant A, compatibly with pullback.
2. Use the natural module/abelian cohomology and higher-direct-image comparisons.
Injective module sheaves are acyclic after forgetting for global sections, so these
comparisons preserve maps, not only abstract isomorphism types. Scalar forgetting
also identifies the canonical exchange and reflects isomorphisms.
3. Inverse image of the Kummer exact sequence, followed by pullback of units, is a
morphism of exact sequences. Naturality of connecting maps proves naturality of the
boundary, and coefficient extension preserves it. In particular t pulls back to t'.
4. Over the algebraically closed base field, both curves have Pic=0. The Kummer long
exact sequence computes H1 as units modulo r-th powers. Affine-line units are k-units;
punctured-line units are k-units times integral powers of t. Thus H1 is zero on the
line and Z/r generated by the actual boundary of t on the punctured line.
5. Constant sections give H0. Affine curve cohomological dimension with exponent r,
not N, kills higher cohomology. Tensor with the finite free Z/r-module A, preserving
the boundary, to obtain the asserted finite-coefficient fibre calculations.
6. For a geometric point of any base B, the strict-henselization stalk formula gives
the cohomology of the curve over Spec O_B^sh. The presheaf description of higher
direct images identifies the germ of the edge section with restriction of kappa(t).
7. Rotate the product square: apply smooth base change to the curve over k and the
affine map Spec O_B^sh to Spec k. Strictly henselian constant cohomology and the
stalk formula show that the pullback unit along the other projection is an
isomorphism. Smoothness is used on the curve over k, not on the strict local base.
8. Composition of derived direct images and its unit identifies the resulting
cohomology comparison with actual restriction from the curve over k. It preserves
constants and, by step 3, the specified coordinate Kummer generator.
9. Geometric stalk conservativity gives the relative degree-zero units, the degree-one
Kummer map, and all the stated vanishing. Cohomological detection of derived
isomorphisms gives affine-line acyclicity. The same primitive-root trivialization
handles the untwisted unit. Restriction through j preserves these constants.
10. The exchange is the canonical adjunction mate. The triangle identity shows its
composite with pullback of the unit is the unit after base change; hence it preserves
constants and is an isomorphism in degree zero.
11. On injective resolutions and their etale restrictions the higher-image exchange
sends a cocycle to its restriction. Naturality of the actual boundary shows its
degree-one map preserves kappa(t), hence is invertible.
12. Both sides have the stated vanishing in all other degrees, including negative
ones. Exact pullback and detection by cohomology prove derived exchange invertible.
The same argument applies to geometric points without a finite-type assumption.
13. Exact etale/pro-etale comparison preserves the classes, and its canonical counit
mate identifies the units and exchanges. Transport all calculations to the small
pro-etale site. Over Spec of an algebraically closed field, the constant-sheaf
comparison with modules identifies these statements with the final fibre calculations. -/
theorem relative_kummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))] :
    P.RelativeKummerConclusions h Y (Y ↘ Spec (CommRingCat.of P.field.k)) ∧
    (∀ (Y' : Scheme.{u}) [Y'.Over (Spec (CommRingCat.of P.field.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [QuasiCompact (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [IsSeparated (Y' ↘ Spec (CommRingCat.of P.field.k))]
      (g : Y' ⟶ Y) [g.IsOver (Spec (CommRingCat.of P.field.k))],
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (CommRingCat.of Ω) ⟶ Y),
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k)) ∧
      P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (g ≫ Y ↘ Spec (CommRingCat.of P.field.k)) := by
  refine ⟨relative_conclusions P h Y (Y ↘ Spec (CommRingCat.of P.field.k)), ?_, ?_⟩
  · intro Y' _ _ _ _ g _
    exact relative_baseChange P h g (Y ↘ Spec (CommRingCat.of P.field.k))
  · intro Ω _ _ g
    exact ⟨relative_baseChange P h g (Y ↘ Spec (CommRingCat.of P.field.k)),
      relative_conclusions P h (Spec (CommRingCat.of Ω)) (g ≫ Y ↘ Spec (CommRingCat.of P.field.k))⟩

end WeilConjectures.PurityFiniteSetting
