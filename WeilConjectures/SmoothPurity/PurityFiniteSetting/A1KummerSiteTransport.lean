/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.A1KummerEtaleData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.A1KummerExchange

/-! # Transport of the normalized Kummer cohomology calculation
Source: det-prop-a1-kummer.proof.md, etale/pro-etale comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The two actual direct images occurring in the proposition.
Source: det-prop-a1-kummer (a)--(c) (blueprint: new-pur-a1-kummer-site-assembly). -/
def a1KummerProImage (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) (b : Bool) :=
  if b then
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedProjection Y)).rightDerivedFunctor.obj
        (P.a1KummerComplex (Punctured Y) true)
  else
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (lineProjection Y)).rightDerivedFunctor.obj (P.a1KummerComplex (Line Y) false)

/-- The affine-line unit in degree zero, with its coefficient source identified.
Source: det-prop-a1-kummer (a) (blueprint: new-pur-a1-kummer-site-assembly). -/
def a1KummerLineZeroUnit (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
        (P.a1KummerUnit (lineProjection Y) a false)

/-- Cohomology comparisons with the actual specified maps. The line's target is untwisted;
the punctured line's target is the finite root tensor. The primitive-root isomorphism is
only used to compare their degree-zero bases.
Source: det-prop-a1-kummer.proof.md, strict-local and site comparisons
(blueprint: new-pur-a1-kummer-site-assembly). -/
def A1KummerSiteTransport (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of P.field.k)) : Prop :=
  ∃ e : ∀ (b : Bool) (n : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj (P.a1KummerEtaleImage a b)) ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) n).obj
          (P.a1KummerProImage Y b),
    ∃ j : P.constant Y ≅ P.frameTwist Y 1,
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
          (P.a1KummerEtaleZero ζ hζ a false) ≫ (e false 0).hom =
        P.a1KummerLineZeroUnit Y a) ∧
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
          (P.a1KummerEtaleZero ζ hζ a true) ≫ (e true 0).hom =
        j.hom ≫ P.a1KummerZeroUnit Y a) ∧
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
          (P.a1KummerEtaleGenerator a) ≫ (e true 1).hom =
        P.a1KummerGenerator Y a)

private theorem proImage_negative (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (b : Bool) (n : ℤ) (hn : n < 0) : IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) n).obj
        (P.a1KummerProImage Y b)) := by
  cases b
  · have : (P.a1KummerProImage Y false).IsGE 0 :=
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (lineProjection Y)).isGE_rightDerivedFunctor_obj_singleFunctor
        (P.a1KummerCoefficient (Line Y) false)
    exact (P.a1KummerProImage Y false).isZero_of_isGE 0 n hn
  · have : (P.a1KummerProImage Y true).IsGE 0 :=
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedProjection Y)).isGE_rightDerivedFunctor_obj_singleFunctor
        (P.a1KummerCoefficient (Punctured Y) true)
    exact (P.a1KummerProImage Y true).isZero_of_isGE 0 n hn

/-- Normalized comparisons transfer the etale computation to the actual pro-etale maps.
Source: det-prop-a1-kummer.proof.md, etale/pro-etale comparison
(blueprint: new-pur-a1-kummer-site-assembly).

Proof: functors preserve inverse pairs and zero objects. Use the comparison equations
to identify the degree-zero unit maps and the actual degree-one generator. The
primitive-root coefficient comparison is invertible, so it cancels in degree zero.
Higher vanishings transport through the cohomology isomorphisms. For the affine-line
unit, negative cohomology vanishes by right derivation; positive cohomology vanishes by
the transported etale calculation. The source is a single sheaf in degree zero, so the
cohomology criterion makes the full unit invertible. -/
theorem a1KummerConclusions_of_transport (P : PurityFiniteSetting.{u}) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of P.field.k))
    (hE : P.A1KummerEtaleConclusions ζ hζ a)
    (hT : P.A1KummerSiteTransport ζ hζ a) : P.A1KummerConclusions Y a := by
  obtain ⟨hzero, hgen, hvan⟩ := hE
  obtain ⟨e, j, hline, hgm, hclass⟩ := hT
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let H := fun n : ℤ => DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) n
  have hz0 (b : Bool) : IsIso (P.a1KummerEtaleZero ζ hζ a b) := hzero b
  have hline0 : IsIso (P.a1KummerLineZeroUnit Y a) := by
    rw [← hline]
    infer_instance
  have hgm0 : IsIso (P.a1KummerZeroUnit Y a) := by
    have hc : IsIso (j.hom ≫ P.a1KummerZeroUnit Y a) := by
      rw [← hgm]
      infer_instance
    exact IsIso.of_isIso_comp_left j.hom _
  have hunit0 : IsIso ((H 0).map (P.a1KummerUnit (lineProjection Y) a false)) := by
    have : IsIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app (P.constant Y) ≫
          (H 0).map (P.a1KummerUnit (lineProjection Y) a false)) := hline0
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app (P.constant Y)) _
  have hunitgm : IsIso ((H 0).map (P.a1KummerUnit (puncturedProjection Y) a true)) := by
    have : IsIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app
            (P.a1KummerCoefficient Y true) ≫
          (H 0).map (P.a1KummerUnit (puncturedProjection Y) a true)) := hgm0
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app
        (P.a1KummerCoefficient Y true)) _
  have hv (b : Bool) (q : ℕ) (hq : (if b then 1 else 0) < q) :
      IsZero ((H (q : ℤ)).obj (P.a1KummerProImage Y b)) :=
    (Functor.map_isZero C (hvan b q hq)).of_iso (e b (q : ℤ)).symm
  refine ⟨?_, hunitgm, ?_, fun q hq ↦ hv true q (by simpa using (show 1 < q by omega))⟩
  · rw [DerivedCategory.isIso_iff]
    intro n
    by_cases hn0 : n = 0
    · subst n
      exact hunit0
    · have hs : IsZero ((H n).obj (P.a1KummerComplex Y false)) := by
        by_cases hneg : n < 0
        · exact (P.a1KummerComplex Y false).isZero_of_isGE 0 n hneg
        · exact (P.a1KummerComplex Y false).isZero_of_isLE 0 n (by omega)
      have ht : IsZero ((H n).obj (P.a1KummerProImage Y false)) := by
        by_cases hneg : n < 0
        · exact proImage_negative P Y false n hneg
        · have hn : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
          exact hn ▸ hv false n.toNat (by simpa using (show 0 < n.toNat by omega))
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
  · rw [← hclass]
    have := hgen
    infer_instance

end WeilConjectures.PurityFiniteSetting
