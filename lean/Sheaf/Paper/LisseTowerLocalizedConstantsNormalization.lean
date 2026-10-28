/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar
import Mathlib.Data.ZMod.Basic

/-! # Normalized transition equation for localized constant models

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.

This is the normalized-arrow part of
`lem-weil-pbc-lisse-tower-localized-constants`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

-- An arbitrary objectwise comparison does not carry a compatibility equation.
-- Varying only its target comparison by negation forces the fixed arrow to be
-- equal to its negative. No disputed project theorem is used in either proof.
private theorem independent_model_square_forces_self_neg
    {C : Type*} [Category C] [Preadditive C] {P Q R S : C}
    (t : P ⟶ Q) (s : R ⟶ S) (e : P ≅ R) (f : Q ≅ S)
    (h : ∀ f' : Q ≅ S, t ≫ f'.hom = e.hom ≫ s) : s = -s := by
  have hneg := h (-f)
  simp only [Preadditive.neg_iso_hom, Preadditive.comp_neg, h f] at hneg
  apply (cancel_epi e.hom).1
  simpa only [Preadditive.comp_neg] using hneg.symm

private theorem independent_model_square_counterexample :
    ¬ ∀ (e₀ e₁ : ModuleCat.of (ZMod 3) (ZMod 3) ≅
        ModuleCat.of (ZMod 3) (ZMod 3)),
      𝟙 _ ≫ e₀.hom = e₁.hom ≫ 𝟙 _ := by
  intro h
  have hid := independent_model_square_forces_self_neg
    (𝟙 (ModuleCat.of (ZMod 3) (ZMod 3))) (𝟙 _) (Iso.refl _) (Iso.refl _)
    (fun f ↦ h f (Iso.refl _))
  have heval := congrArg
    (fun f : ModuleCat.of (ZMod 3) (ZMod 3) ⟶ ModuleCat.of (ZMod 3) (ZMod 3) ↦
      f (1 : ZMod 3)) hid
  have hne : (1 : ZMod 3) ≠ -1 := by decide
  exact hne heval

/- STATEMENT-DISPUTED: `model` is an arbitrary family of objectwise isomorphisms.
There is no naturality or compatibility between consecutive levels. Replacing its
level-zero components by their negatives changes only the left side of the n = 0
square. If both families satisfied the claim, the fixed algebraic transition would
be equal to its negative. On a nonempty point with zero-ideal F_3 coefficients and
a constant rank-one complex, that transition is an isomorphism and is not its
negative. The checked private lemmas above certify the categorical obstruction.
The existential parent must instead construct its model comparisons and prove their
compatibility together. Its existence statement does not justify this universal split.
-/
/-- A supplied family of constant model isomorphisms satisfies the localized
semilinear normalization square.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.  Before localization, evaluate both composites on
constant sections; both act by the supplied semilinear map.  The section-normalized
scalar comparison and the restriction compositors therefore identify the two
ordinary composites.  Exact localization transports this equality with the
specified `mapDerivedCategoryCompIso` and restriction-scalar compositors.  Finally
conjugate by `constantAdicQuotientRightIso`; its identity normalization on constant
sections gives the displayed equation.  The argument is valid for arbitrary
complexes, including zero objects and empty schemes.
(blueprint: lem-weil-pbc-lisse-tower-localized-constants-normalization). -/
theorem lisseTower_localized_constants_normalization
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (model : ∀ (n : ℕ)
      (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
      ((ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).mapDerivedCategory ⋙
          lisseTowerFixedRealization g d n).obj
        ((localProEtaleComparison a (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
        (constantAdicQuotientRealization g d n).obj E) :
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model j N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k) := by
  sorry

end AlgebraicGeometry.Scheme
