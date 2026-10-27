/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.CategoryTheory.AdjunctConjugateOpenFactor
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Sheaf.SixFunctors.SemilinearProperOpenCore
public import Sheaf.SixFunctors.SemilinearProperOpenCoherence
public import Sheaf.SixFunctors.SemilinearProperOpenScalarSupport
public import Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport

import Sheaf.SixFunctors.IntrinsicScalarAlphaCompatibility
import Sheaf.SixFunctors.IntrinsicEvaluationAlphaCompatibility

import Mathlib.Util.AliasIn
import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.CoefficientRingedSequenceSite
import all Sheaf.Paper.SemilinearSystemModels
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
import all Sheaf.SixFunctors.SemilinearProperOpenScalarSupport
import all Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport
import all Sheaf.SixFunctors.SemilinearProperOpenCore
import all Sheaf.SixFunctors.SemilinearProperOpenCoherence
import all Sheaf.SixFunctors.SemilinearProperOpenNormalization
import all Sheaf.CategoryTheory.ExactClopenNormalization

/-! # Intrinsic proper/open mates for semilinear coefficient systems

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F, open cases; blueprint
`fix-prop-coherence`, coefficient-system realization, step 2
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).

## Main definitions and statements

- `Modules`, `Derived`, `P`, `R`, `J`: the actual ordinary and derived system operations.
- `alpha`, `gamma`, `lambda`: the intrinsic clopen mate and its open restriction.
- `semilinearProperOpenMatePasting`: vertical, horizontal and base-change equations.
- `gamma_adjunct`, `gamma_identities`, `compositor_associativity`: normalization and coherence.
- `gamma_scalarRestriction`, `gamma_evaluation`, `gamma_finite`: coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

-- The original instances followed every proof import in this module. Restore that
-- registration order after moving their declarations into the data modules.
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
attribute [-instance] constantRingSheafify proEtSmall sequenceSmall derived
  siteMap_continuous push_additive push_isRightAdjoint pull_additive pull_limits
  pull_colimits systems_kInjective openPull_isRightAdjoint extension_additive
  extension_limits extension_colimits rho_additive rho_limits rho_colimits
attribute [instance] constantRingSheafify
attribute [instance] proEtSmall
attribute [instance] sequenceSmall
attribute [instance] derived
attribute [instance] siteMap_continuous
attribute [instance] push_additive
attribute [instance] push_isRightAdjoint
attribute [instance] pull_additive
attribute [instance] pull_limits
attribute [instance] pull_colimits
attribute [instance] systems_kInjective
attribute [instance] openPull_isRightAdjoint
attribute [instance] extension_additive
attribute [instance] extension_limits
attribute [instance] extension_colimits
attribute [instance] rho_additive
attribute [instance] rho_limits
attribute [instance] rho_colimits
end AlgebraicGeometry.ProEtale.SemilinearProperOpen

section ProofEnvironment

-- Compare the canonical constructions through their APIs, without unfolding their data.
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors


section CategoricalProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private alias map_iso_transport := SemilinearProperOpenCoreAliases.map_iso_transport

private alias tower_normalized_transport :=
  SemilinearProperOpenCoreAliases.tower_normalized_transport

private alias tower_iso_ext_sections := SemilinearProperOpenCoreAliases.tower_iso_ext_sections

private alias normalized_function := SemilinearProperOpenCoreAliases.normalized_function

private alias isIso_of_heq := SemilinearProperOpenCoreAliases.isIso_of_heq

private alias normalized_square := SemilinearProperOpenCoreAliases.normalized_square

private alias chosen_unit_isIso_congr := SemilinearProperOpenCoreAliases.chosen_unit_isIso_congr

private alias exact_derived_congr := SemilinearProperOpenCoreAliases.exact_derived_congr

private alias right_derived_congr := SemilinearProperOpenCoreAliases.right_derived_congr

private def constant_diagram_square
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) :
    F ⋙ (G ⋙ Functor.const ℕᵒᵖ) ≅
      (H ⋙ Functor.const ℕᵒᵖ) ⋙ (Functor.whiskeringRight ℕᵒᵖ E D).obj I := by
  exact SemilinearProperOpenCoreAliases.constant_diagram_square (A := A) (B := B) (D := D)
    (E := E) (F := F) (G := G) (H := H) (I := I) (e := e)

private alias constant_diagram_square_hom_app :=
  SemilinearProperOpenCoreAliases.constant_diagram_square_hom_app

private alias constant_diagram_square_inv_app :=
  SemilinearProperOpenCoreAliases.constant_diagram_square_inv_app

private alias mate_of_unit_normalization :=
  SemilinearProperOpenCoreAliases.mate_of_unit_normalization

private alias constant_diagram_mate := SemilinearProperOpenCoreAliases.constant_diagram_mate

private alias composite_conjugate_inv := SemilinearProperOpenCoreAliases.composite_conjugate_inv

private def adjunct_comparison
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Rr : A ⥤ D} {Lp : E ⥤ B} {Rp : B ⥤ E}
    {Ji : D ⥤ E} {Pi : E ⥤ D} {Jb : F ⥤ B} {Pb : B ⥤ F}
    {Lq : D ⥤ F} {Rq : F ⥤ D} {Rs : A ⥤ F}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (ap : Lp ⊣ Rp) (ai : Ji ⊣ Pi) (ab : Jb ⊣ Pb) (aq : Lq ⊣ Rq)
    [IsIso ab.unit] (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk)
    (t : Js ≅ Rs) (δ : Rs ⋙ Rq ≅ Rr) : (Jk ⋙ Rp) ⋙ Pi ≅ Rr := by
  exact SemilinearProperOpenCoreAliases.adjunct_comparison (A := A) (B := B) (D := D) (E := E)
    (F := F) (Rr := Rr) (Lp := Lp) (Rp := Rp) (Ji := Ji) (Pi := Pi) (Jb := Jb) (Pb := Pb)
    (Lq := Lq) (Rq := Rq) (Rs := Rs) (Js := Js) (Jk := Jk) (ap := ap) (ai := ai) (ab := ab)
    (aq := aq) (β := β) (d := d) (t := t) (δ := δ)

private alias adjunct_comparison_identity :=
  SemilinearProperOpenCoreAliases.adjunct_comparison_identity

private alias homEquiv_iso_inverse := SemilinearProperOpenCoreAliases.homEquiv_iso_inverse

private def projection_square
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Lp : E ⥤ B} {Ji : D ⥤ E}
    {Jb : F ⥤ B} {Lq : D ⥤ F} {Ls : F ⥤ A}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk) (e : Lr ≅ Lq ⋙ Ls)
    (π : 𝟭 F ⟶ Ls ⋙ Js) : Ji ⋙ Lp ⟶ Lr ⋙ Jk := by
  exact SemilinearProperOpenCoreAliases.projection_square (A := A) (B := B) (D := D) (E := E)
    (F := F) (Lr := Lr) (Lp := Lp) (Ji := Ji) (Jb := Jb) (Lq := Lq) (Ls := Ls) (Js := Js)
    (Jk := Jk) (β := β) (d := d) (e := e) (π := π)

private alias projection_square_formula := SemilinearProperOpenCoreAliases.projection_square_formula

private alias projection_square_formula_of_eq :=
  SemilinearProperOpenCoreAliases.projection_square_formula_of_eq

attribute [local implicit_reducible] SemilinearSections.ringPresheaf

private alias ordinary_restriction_existsUnique :=
  SemilinearProperOpenCoreAliases.ordinary_restriction_existsUnique

end CategoricalProof


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DerivedSquareConjugation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  {L : A ⥤ B} {l : D ⥤ E} {G G' : A ⥤ D} {H H' : B ⥤ E}
  [L.Additive] [l.Additive] [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
private alias derived_square_conjugate := SemilinearProperOpenCoreAliases.derived_square_conjugate

private alias derived_iso_symm_inv := SemilinearProperOpenCoreAliases.derived_iso_symm_inv

end DerivedSquareConjugation


section DerivedConstantSquare
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory (ℕᵒᵖ ⥤ D)] [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
  (L : A ⥤ B) (G : B ⥤ D) (F : A ⥤ E) (l : E ⥤ D)
  [L.Additive] [G.Additive] [F.Additive] [l.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]

private alias derived_constant_square_comp :=
  SemilinearProperOpenCoreAliases.derived_constant_square_comp

private alias derived_constant_square_inverse :=
  SemilinearProperOpenCoreAliases.derived_constant_square_inverse

end DerivedConstantSquare


namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] alpha gamma

set_option synthInstance.maxSize 64 in
private alias coefficientMap_forget_eq := SemilinearProperOpenCoreAliases.coefficientMap_forget_eq

attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap

private alias push_eq := SemilinearProperOpenCoreAliases.push_eq

private alias pull_eq := SemilinearProperOpenCoreAliases.pull_eq

private alias extension_eq := SemilinearProperOpenCoreAliases.extension_eq

private alias P_eq := SemilinearProperOpenCoreAliases.P_eq

private alias J_eq := SemilinearProperOpenCoreAliases.J_eq

private alias R_eq := SemilinearProperOpenCoreAliases.R_eq

private alias conjugate_transport := SemilinearProperOpenCoreAliases.conjugate_transport

private alias conjugate_transport_inverse :=
  SemilinearProperOpenCoreAliases.conjugate_transport_inverse

private alias sComp_congr := SemilinearProperOpenCoreAliases.sComp_congr

private alias alpha_eq_projection_square :=
  SemilinearProperOpenCoreAliases.alpha_eq_projection_square

-- Preserve the private helpers used by existing import-all consumers.

private alias normalized_apply := SemilinearProperOpenScalarAliases.normalized_apply

section
variable (n : ℕ)
private alias level_push_evaluation_normalized :=
  SemilinearProperOpenEvaluationAliases.level_push_evaluation_normalized

end

private alias inverse_mate_change_isIso :=
  SemilinearProperOpenEvaluationAliases.inverse_mate_change_isIso

private alias inverse_mate_pasted_isIso :=
  SemilinearProperOpenEvaluationAliases.inverse_mate_pasted_isIso

universe v h w

open SheafOfModules.OpenTensorNormalization in
private alias exact_hom_fac := SemilinearProperOpenEvaluationAliases.exact_hom_fac

open SheafOfModules.OpenTensorNormalization in
private alias exact_inverse_mate_isIso :=
  SemilinearProperOpenEvaluationAliases.exact_inverse_mate_isIso

-- Keep both proper-face pullback hypotheses of the published cube statement.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
/-- Vertical, horizontal and base-change coherence for every commutative proper/open
square, as equalities in derived semilinear-system categories, without assuming evaluation
faithful. Source: Stacks, Tags 0F7C, 0F7D and 0F7F, and blueprint, steps 5, 6, 10, 11
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: for alpha, pull the clopen decompositions to each test object. In a vertical
or horizontal pasting the selected opens are nested, so successive component
projections equal the outer component projection. Base change pulls both clopen
components and the identity/zero projector to the corresponding components. Verify
these equations on their intersections using sheaf uniqueness. Apply the exact
functors termwise to towers and complexes, then use localization uniqueness to
descend the equations. Take proper-adjunction mates with composition adjunctions.
Mate pasting gives the two composition laws; the pullback cube gives the base-change
law. Associativity of normalized compositors makes all parenthesizations agree. -/
theorem semilinearProperOpenMatePasting :
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C₀ ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived C τ A),
      (J C τ j).map ((sComp C τ r₁ r₂).hom.app M) ≫
          (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (sComp C τ p₁ p₂).inv.app ((J C τ k).obj M) =
        (gamma C τ i r₂ p₂ j h₂).app ((R C τ r₁).obj M) ≫
          (R C τ p₂).map ((gamma C τ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C₀) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived C τ A),
      (jComp C τ i j).hom.app ((R C τ r).obj M) ≫
          (gamma C τ (k ≫ l) r q (i ≫ j) h).app M ≫
          (R C τ q).map ((jComp C τ k l).inv.app M) =
        (J C τ j).map ((gamma C τ k r p i h₁).app M) ≫
          (gamma C τ l p q j h₂).app ((J C τ k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (M : Derived C τ V),
      (P C τ b).map ((gamma C τ k r p i h).app M) ≫
          (exchange C τ a p₁ p b wp).app ((J C τ k).obj M) ≫
          (R C τ p₁).map ((beta C τ d k₁ k a wk sk).hom.app M) =
        (beta C τ c i₁ i b wi si).hom.app ((R C τ r).obj M) ≫
          (J C τ i₁).map ((exchange C τ d r₁ r c wr).app M) ≫
          (gamma C τ k₁ r₁ p₁ i₁ h₁).app ((P C τ d).obj M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A C₀ E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
    exact Normalization.vertical_transfer
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ i) (VaryingRing.J C τ i)
      (J C τ j) (VaryingRing.J C τ j)
      (R C τ r₁) (VaryingRing.P C τ r₁)
      (R C τ r₂) (VaryingRing.P C τ r₂)
      (R C τ (r₁ ≫ r₂)) (VaryingRing.P C τ (r₁ ≫ r₂))
      (R C τ p₁) (VaryingRing.P C τ p₁)
      (R C τ p₂) (VaryingRing.P C τ p₂)
      (R C τ (p₁ ≫ p₂)) (VaryingRing.P C τ (p₁ ≫ p₂))
      (gamma C τ k r₁ p₁ i h₁) (VaryingRing.gamma C τ k r₁ p₁ i h₁)
      (gamma C τ i r₂ p₂ j h₂) (VaryingRing.gamma C τ i r₂ p₂ j h₂)
      (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) (VaryingRing.gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (sComp C τ r₁ r₂) (VaryingRing.pComp C τ r₁ r₂)
      (sComp C τ p₁ p₂) (VaryingRing.pComp C τ p₁ p₂)
      (J_eq C τ k)
      (J_eq C τ i)
      (J_eq C τ j)
      (R_eq C τ r₁)
      (R_eq C τ r₂)
      (R_eq C τ (r₁ ≫ r₂))
      (R_eq C τ p₁)
      (R_eq C τ p₂)
      (R_eq C τ (p₁ ≫ p₂))
      (Normalization.gamma_normalization C τ k r₁ p₁ i h₁)
      (Normalization.gamma_normalization C τ i r₂ p₂ j h₂)
      (Normalization.gamma_normalization C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (Normalization.scomp_heq C τ r₁ r₂)
      (Normalization.scomp_heq C τ p₁ p₂)
      ((VaryingRing.properOpenPasting C τ).1 k i j r₁ r₂ p₁ p₂ h₁ h₂ h)
  · intro A C₀ E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
    exact Normalization.horizontal_transfer
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ l) (VaryingRing.J C τ l)
      (J C τ i) (VaryingRing.J C τ i)
      (J C τ j) (VaryingRing.J C τ j)
      (J C τ (k ≫ l)) (VaryingRing.J C τ (k ≫ l))
      (J C τ (i ≫ j)) (VaryingRing.J C τ (i ≫ j))
      (R C τ r) (VaryingRing.P C τ r)
      (R C τ p) (VaryingRing.P C τ p)
      (R C τ q) (VaryingRing.P C τ q)
      (gamma C τ k r p i h₁) (VaryingRing.gamma C τ k r p i h₁)
      (gamma C τ l p q j h₂) (VaryingRing.gamma C τ l p q j h₂)
      (gamma C τ (k ≫ l) r q (i ≫ j) h) (VaryingRing.gamma C τ (k ≫ l) r q (i ≫ j) h)
      (jComp C τ i j) (VaryingRing.jComp C τ i j)
      (jComp C τ k l) (VaryingRing.jComp C τ k l)
      (J_eq C τ k)
      (J_eq C τ l)
      (J_eq C τ i)
      (J_eq C τ j)
      (J_eq C τ (k ≫ l))
      (J_eq C τ (i ≫ j))
      (R_eq C τ r)
      (R_eq C τ p)
      (R_eq C τ q)
      (Normalization.gamma_normalization C τ k r p i h₁)
      (Normalization.gamma_normalization C τ l p q j h₂)
      (Normalization.gamma_normalization C τ (k ≫ l) r q (i ≫ j) h)
      (Normalization.jcomp_heq C τ i j)
      (Normalization.jcomp_heq C τ k l)
      ((VaryingRing.properOpenPasting C τ).2 k l i j r p q h₁ h₂ h)
  · intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ a b c d
      _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr
    exact Normalization.cube_transfer
      (R C τ r) (VaryingRing.P C τ r)
      (R C τ p) (VaryingRing.P C τ p)
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ i) (VaryingRing.J C τ i)
      (R C τ r₁) (VaryingRing.P C τ r₁)
      (R C τ p₁) (VaryingRing.P C τ p₁)
      (J C τ k₁) (VaryingRing.J C τ k₁)
      (J C τ i₁) (VaryingRing.J C τ i₁)
      (P C τ a) (VaryingRing.G C τ a)
      (P C τ b) (VaryingRing.G C τ b)
      (P C τ c) (VaryingRing.G C τ c)
      (P C τ d) (VaryingRing.G C τ d)
      (gamma C τ k r p i h) (VaryingRing.gamma C τ k r p i h)
      (gamma C τ k₁ r₁ p₁ i₁ h₁) (VaryingRing.gamma C τ k₁ r₁ p₁ i₁ h₁)
      (exchange C τ a p₁ p b wp) (Normalization.varyingExchange C τ a p₁ p b wp)
      (exchange C τ d r₁ r c wr) (Normalization.varyingExchange C τ d r₁ r c wr)
      (beta C τ d k₁ k a wk sk) (VaryingRing.alphaPullbackBeta C τ d k₁ k a wk sk)
      (beta C τ c i₁ i b wi si) (VaryingRing.alphaPullbackBeta C τ c i₁ i b wi si)
      (R_eq C τ r)
      (R_eq C τ p)
      (J_eq C τ k)
      (J_eq C τ i)
      (R_eq C τ r₁)
      (R_eq C τ p₁)
      (J_eq C τ k₁)
      (J_eq C τ i₁)
      (P_eq C τ a)
      (P_eq C τ b)
      (P_eq C τ c)
      (P_eq C τ d)
      (Normalization.gamma_normalization C τ k r p i h)
      (Normalization.gamma_normalization C τ k₁ r₁ p₁ i₁ h₁)
      (Normalization.exchange_heq C τ a p₁ p b wp)
      (Normalization.exchange_heq C τ d r₁ r c wr)
      (Normalization.beta_heq C τ d k₁ k a wk sk)
      (Normalization.beta_heq C τ c i₁ i b wi si)
      (Normalization.varying_cube C τ k i r p k₁ i₁ r₁ p₁ a b c d
        h h₁ wk wi wp wr sk si sp sr)




section CoefficientMateAssembly
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe k₁

private def evaluationOfSpecifiedMate
    {X Y x y : Type k₁} [Category.{k₁} X] [Category.{k₁} Y]
    [Category.{k₁} x] [Category.{k₁} y]
    (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {P : Y ⥤ X} {l : x ⥤ y} {p : y ⥤ x}
    (a : L ⊣ P) (b : l ⊣ p) (e : L ⋙ F ≅ E ⋙ l)
    (v : P ⋙ E ≅ F ⋙ p)
    (hv : v.hom = (mateEquiv a b e.inv).natTrans) :
    AdjunctionEvaluation E F a b where
  left := e
  right := v
  unit A := by
    rw [hv]
    have hh := congrArg (fun z ↦ z ≫ p.map (e.hom.app A))
      (unit_mateEquiv a b e.inv A)
    simp only [Functor.id_obj, Category.assoc] at hh
    rw [← p.map_comp, Iso.inv_hom_id_app] at hh
    erw [p.map_id, Category.comp_id] at hh
    exact hh
  counit B := by
    rw [hv]
    exact mateEquiv_counit a b e.inv B

private theorem specifiedMateCompatibility
    {X Y Z W x y z w : Type k₁}
    [Category.{k₁} X] [Category.{k₁} Y] [Category.{k₁} Z] [Category.{k₁} W]
    [Category.{k₁} x] [Category.{k₁} y] [Category.{k₁} z] [Category.{k₁} w]
    {E₁ : X ⥤ x} {F₁ : Y ⥤ y} {E₂ : Z ⥤ z} {F₂ : W ⥤ w}
    {L₁ : X ⥤ Y} {R₁ : Y ⥤ X} {L₂ : Z ⥤ W} {R₂ : W ⥤ Z}
    {l₁ : x ⥤ y} {r₁ : y ⥤ x} {l₂ : z ⥤ w} {r₂ : w ⥤ z}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : l₁ ⊣ r₁) (b₂ : l₂ ⊣ r₂)
    (e₁ : L₁ ⋙ F₁ ≅ E₁ ⋙ l₁) (e₂ : L₂ ⋙ F₂ ≅ E₂ ⋙ l₂)
    (v₁ : R₁ ⋙ E₁ ⟶ F₁ ⋙ r₁) (v₂ : R₂ ⋙ E₂ ⟶ F₂ ⋙ r₂)
    (s₁ : IsIso v₁) (s₂ : IsIso v₂)
    (hv₁ : v₁ = mateEquiv a₁ b₁ e₁.inv)
    (hv₂ : v₂ = mateEquiv a₂ b₂ e₂.inv)
    {G : X ⥤ Z} {H : Y ⥤ W} {g : x ⥤ z} {h : y ⥤ w}
    (c : G ⋙ E₂ ≅ E₁ ⋙ g) (d : H ⋙ F₂ ≅ F₁ ⋙ h)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare g l₁ l₂ h)
    (γ : R₁ ⋙ G ⟶ H ⋙ R₂) (δ : r₁ ⋙ g ⟶ h ⋙ r₂)
    (hγ : γ = mateEquiv a₁ a₂ α) (hδ : δ = mateEquiv b₁ b₂ β)
    (hc : ∀ A : X,
      F₂.map (α.app A) ≫ d.hom.app (L₁.obj A) ≫ h.map (e₁.hom.app A) =
        e₂.hom.app (G.obj A) ≫ l₂.map (c.hom.app A) ≫ β.app (E₁.obj A))
    (M : Y) :
    E₂.map (γ.app M) ≫ v₂.app (H.obj M) ≫
        r₂.map (d.hom.app M) =
      c.hom.app (R₁.obj M) ≫ g.map (v₁.app M) ≫
        δ.app (F₁.obj M) := by
  subst γ δ
  exact evaluation_mate a₁ a₂ b₁ b₂
    (evaluationOfSpecifiedMate E₁ F₁ a₁ b₁ e₁ (@asIso _ _ _ _ v₁ s₁) hv₁)
    (evaluationOfSpecifiedMate E₂ F₂ a₂ b₂ e₂ (@asIso _ _ _ _ v₂ s₂) hv₂) c d α β hc M

end CoefficientMateAssembly

section ScalarRestriction
attribute [local irreducible] P R J rhoP rhoJ adj
  StrictTower.G StrictTower.R StrictTower.J StrictTower.adj StrictTower.alpha
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

/-- Scalar restriction identifies the intrinsic mate with the normalized constant-tower
mate before evaluation. Source: Stacks 0F7B and the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: scalar restriction preserves the section-normalized beta and the clopen
identity/zero projection, so it preserves alpha. Paste this equality with the
inverse-image scalar squares for p and r and take their adjunction mates. The
result is exactly the displayed equation with the canonical rhoR and rhoJ factors.
The argument is an equality of specified system maps, not detection by evaluation. -/
theorem gamma_scalarRestriction {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (rho C τ B φ hφ T).map ((gamma C τ k r p i h).app M) ≫
      (rhoR C τ B φ hφ p).app ((J C τ k).obj M) ≫
      (StrictTower.R B p).map ((rhoJ C τ B φ hφ k).hom.app M) =
    (rhoJ C τ B φ hφ i).hom.app ((R C τ r).obj M) ≫
      (StrictTower.J B i).map ((rhoR C τ B φ hφ r).app M) ≫
      (StrictTower.gamma B k r p i h).app ((rho C τ B φ hφ V).obj M) := by
  exact specifiedMateCompatibility
    (E₁ := rho C τ B φ hφ S) (F₁ := rho C τ B φ hφ V)
    (E₂ := rho C τ B φ hφ T) (F₂ := rho C τ B φ hφ W)
    (G := J C τ i) (H := J C τ k) (g := StrictTower.J B i) (h := StrictTower.J B k)
    (adj C τ r) (adj C τ p) (StrictTower.adj B r) (StrictTower.adj B p)
    (rhoP C τ B φ hφ r) (rhoP C τ B φ hφ p)
    (rhoR C τ B φ hφ r) (rhoR C τ B φ hφ p)
    (rhoR_isIso C τ B φ hφ r) (rhoR_isIso C τ B φ hφ p) rfl rfl
    (rhoJ C τ B φ hφ i) (rhoJ C τ B φ hφ k)
    (alpha C τ k r p i h) (StrictTower.alpha B k r p i h)
    (gamma C τ k r p i h) (StrictTower.gamma B k r p i h)
    (by delta gamma; rfl) (by delta StrictTower.gamma; rfl)
    (intrinsicScalarAlphaCompatibility C τ B φ hφ k r p i h) M

end ScalarRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


section Evaluation
attribute [local irreducible] J evalP evalJ adj StrictTower.J StrictTower.adj
  StrictTower.alpha
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition StrictTower.G StrictTower.R P R
variable (n : ℕ)

/-- Evaluating the intrinsic comparison gives the same normalized mate over C_n.
The constant-diagram presentation merely reuses the existing constant-ring API.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: evaluation preserves the exact section-normalized open comparison and the
clopen projection. The direct-image comparison is the mate of the evaluated
pullback comparison. Mate pasting gives the equation directly, before any use of
levelwise detection; no faithfulness of evaluation is required. -/
theorem gamma_evaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (E C τ n T).map ((gamma C τ k r p i h).app M) ≫
      (evalR C τ n p).app ((J C τ k).obj M) ≫
      (StrictTower.R (C n) p).map ((evalJ C τ n k).hom.app M) =
    (evalJ C τ n i).hom.app ((R C τ r).obj M) ≫
      (StrictTower.J (C n) i).map ((evalR C τ n r).app M) ≫
      (StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M) := by
  exact specifiedMateCompatibility
    (E₁ := E C τ n S) (F₁ := E C τ n V) (E₂ := E C τ n T) (F₂ := E C τ n W)
    (G := J C τ i) (H := J C τ k)
    (g := StrictTower.J (C n) i) (h := StrictTower.J (C n) k)
    (adj C τ r) (adj C τ p) (StrictTower.adj (C n) r) (StrictTower.adj (C n) p)
    (evalP C τ n r) (evalP C τ n p)
    (evalR C τ n r) (evalR C τ n p)
    (evalR_isIso C τ n r) (evalR_isIso C τ n p) rfl rfl
    (evalJ C τ n i) (evalJ C τ n k)
    (alpha C τ k r p i h) (StrictTower.alpha (C n) k r p i h)
    (gamma C τ k r p i h) (StrictTower.gamma (C n) k r p i h)
    (by delta gamma; rfl) (by delta StrictTower.gamma; rfl)
    (intrinsicEvaluationAlphaCompatibility C τ n k r p i h) M

end Evaluation

section FiniteEvaluation
variable (n : ℕ)

/-- The canonical source comparison, assembled from evaluation of J and its R mate.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalSource {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsOpenImmersion i] (M : Derived C τ V) :
    (E C τ n T).obj ((J C τ i).obj ((R C τ r).obj M)) ≅
      (StrictTower.J (C n) i).obj
        ((StrictTower.R (C n) r).obj ((E C τ n V).obj M)) :=
  (evalJ C τ n i).app ((R C τ r).obj M) ≪≫
    (StrictTower.J (C n) i).mapIso
      ((@asIso _ _ _ _ (evalR C τ n r) (evalR_isIso C τ n r)).app M)

/-- The canonical target comparison, assembled from the R mate and evaluation of J.
Source: Stacks 0F7B; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def evalTarget {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k] (M : Derived C τ V) :
    (E C τ n T).obj ((R C τ p).obj ((J C τ k).obj M)) ≅
      (StrictTower.R (C n) p).obj
        ((StrictTower.J (C n) k).obj ((E C τ n V).obj M)) :=
  (@asIso _ _ _ _ (evalR C τ n p) (evalR_isIso C τ n p)).app ((J C τ k).obj M) ≪≫
    (StrictTower.R (C n) p).mapIso ((evalJ C τ n k).app M)

/-- At a finite coefficient level with its specified bounded-below etale origin, the
intrinsic mate is the specified finite proper/open comparison, via canonical arrows.
The retained origin is the existing bundled witness; its coefficient carrier and
scalar map are required to be exactly C_n and its identity, respectively. Thus no
coefficient lift, extension of scalars, or extra etale-origin assumption is supplied.
The zero-th tower index evaluates a constant diagram, hence the original n-th level.
Source: Stacks 0F7B and 099R; strict-tower finite comparison
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: apply gamma_evaluation, whose source and target comparisons are evalSource
and evalTarget. Evaluate this equation at index zero of the constant diagram. Apply
the finite comparison clause of normalizedProperOpenCalculus with the supplied
origin w. The equalities hC and hscalar identify its coefficient ring and scalar
map with C_n and identity. Its finiteSource and finiteTarget give the displayed
equation, retaining w.origin and w.iso. No equality is inferred by detecting it
after evaluation. -/
theorem gamma_finite {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) [Finite (C n)] (M : Derived C τ V)
    (w : StrictTower.ScalarEtaleOrigin (C n) V
      ((StrictTower.ev (C n) V 0).obj ((E C τ n V).obj M)))
    (hC : w.Λ = (C n : Type (u + 1)))
    (hscalar : HEq w.φ (RingHom.id (C n))) :
    (StrictTower.finiteSource (C n) r i ((E C τ n V).obj M) 0 w).hom ≫
      (StrictTower.ev (C n) T 0).map ((evalSource C τ n r i M).inv) ≫
      (StrictTower.ev (C n) T 0).map ((E C τ n T).map ((gamma C τ k r p i h).app M)) ≫
      (StrictTower.ev (C n) T 0).map ((evalTarget C τ n k p M).hom) =
    (StrictTower.HD (C n) T w.Λ w.φ).map
      ((StrictTower.finiteGamma w.Λ k r p i h).hom.app w.origin.L) ≫
      (StrictTower.finiteTarget (C n) k p ((E C τ n V).obj M) 0 w).hom := by
  have _hC := hC
  have _hscalar := hscalar
  have he := gamma_evaluation C τ n k r p i h M
  have ht : (E C τ n T).map ((gamma C τ k r p i h).app M) ≫
      (evalTarget C τ n k p M).hom =
      (evalSource C τ n r i M).hom ≫
        (StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M) := by
    simpa only [evalSource, evalTarget, Iso.trans_hom, Functor.mapIso_hom,
      Functor.comp_obj,
      Iso.app_hom, asIso_hom, Category.assoc] using he
  exact (map_iso_transport (StrictTower.ev (C n) T 0)
    (evalSource C τ n r i M) (evalTarget C τ n k p M)
    ((E C τ n T).map ((gamma C τ k r p i h).app M))
    ((StrictTower.gamma (C n) k r p i h).app ((E C τ n V).obj M)) ht
    (StrictTower.finiteSource (C n) r i ((E C τ n V).obj M) 0 w).hom).trans
      (StrictTower.gamma_evaluation (C n) k r p i h ((E C τ n V).obj M) 0 w)

end FiniteEvaluation

private alias push_transport := SemilinearProperOpenCoherenceAliases.push_transport
private alias push_map_apply := SemilinearProperOpenCoherenceAliases.push_map_apply
private alias push_obj_map_apply := SemilinearProperOpenCoherenceAliases.push_obj_map_apply
private alias pushComp_apply := SemilinearProperOpenCoherenceAliases.pushComp_apply
private alias push_coherence := SemilinearProperOpenCoherenceAliases.push_coherence
private alias pull_coherence := SemilinearProperOpenCoherenceAliases.pull_coherence
private alias pull_derived_transport := SemilinearProperOpenCoherenceAliases.pull_derived_transport
private alias p_coherence := SemilinearProperOpenCoherenceAliases.p_coherence
private alias jComp_transport := SemilinearProperOpenCoherenceAliases.jComp_transport

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived C τ U),
      (gamma C τ j (𝟙 U) (𝟙 X) j h).app M ≫
          (sId C τ X).hom.app ((J C τ j).obj M) =
        (J C τ j).map ((sId C τ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived C τ U),
      (gamma C τ (𝟙 U) p p (𝟙 X) h).app M ≫
          (R C τ p).map ((jId C τ U).hom.app M) =
        (jId C τ X).hom.app ((R C τ p).obj M)) := by
  constructor
  · intro U X j _ _ h
    exact Normalization.identity_left_transfer
      (J C τ j) (VaryingRing.J C τ j)
      (R C τ (𝟙 U)) (VaryingRing.P C τ (𝟙 U))
      (R C τ (𝟙 X)) (VaryingRing.P C τ (𝟙 X))
      (gamma C τ j (𝟙 U) (𝟙 X) j h) (VaryingRing.gamma C τ j (𝟙 U) (𝟙 X) j h)
      (sId C τ U) (VaryingRing.pId C τ U) (sId C τ X) (VaryingRing.pId C τ X)
      (J_eq C τ j) (R_eq C τ (𝟙 U)) (R_eq C τ (𝟙 X))
      (Normalization.gamma_normalization C τ j (𝟙 U) (𝟙 X) j h)
      (Normalization.sid_heq C τ U) (Normalization.sid_heq C τ X)
      ((VaryingRing.gamma_identities C τ).1 j h)
  · intro U X p _ h
    exact Normalization.identity_right_transfer
      (R C τ p) (VaryingRing.P C τ p)
      (J C τ (𝟙 U)) (VaryingRing.J C τ (𝟙 U))
      (J C τ (𝟙 X)) (VaryingRing.J C τ (𝟙 X))
      (gamma C τ (𝟙 U) p p (𝟙 X) h) (VaryingRing.gamma C τ (𝟙 U) p p (𝟙 X) h)
      (jId C τ U) (VaryingRing.jId C τ U) (jId C τ X) (VaryingRing.jId C τ X)
      (R_eq C τ p) (J_eq C τ (𝟙 U)) (J_eq C τ (𝟙 X))
      (Normalization.gamma_normalization C τ (𝟙 U) p p (𝟙 X) h)
      (Normalization.jid_heq C τ U) (Normalization.jid_heq C τ X)
      ((VaryingRing.gamma_identities C τ).2 p h)


/-- The projector selects the clopen image: identity there, zero on its complement.
Source: Stacks 09AE and the proof of 0F7B
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: split each test object into its intersections with the two clopen components.
The direct-image unit keeps precisely the image factor. The inverse open-to-direct
comparison identifies it with extension by zero. Thus restriction to the image is
the open unit, and restriction to the complement is zero, also on complexes. -/
theorem pi_components {U X D : Scheme.{u}} (s : U ⟶ X) (c : D ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Derived C τ X) :
    (P C τ s).map ((pi C τ s).app M) = (jAdj C τ s).unit.app ((P C τ s).obj M) ∧
      (P C τ c).map ((pi C τ s).app M) = 0 := by
  constructor
  · have hu := jAdj_unit_isIso C τ s
    let t : Adjunction.Triple (J C τ s) (P C τ s) (R C τ s) :=
      ⟨jAdj C τ s, adj C τ s⟩
    let ff := (jAdj C τ s).fullyFaithfulLOfIsIsoUnit
    have := ff.full
    have := ff.faithful
    have he : openToS C τ s = t.leftToRight := by
      ext N
      simp [openToS, t, Adjunction.Triple.leftToRight]
    have ho := openToS_isIso C τ s
    simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
    rw [Functor.map_comp]
    apply (cancel_mono ((P C τ s).map ((openToS C τ s).app ((P C τ s).obj M)))).1
    simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      Category.comp_id]
    rw [he, t.leftToRight_app_obj, Functor.map_comp]
    change _ = (jAdj C τ s).unit.app _ ≫
      (P C τ s).map ((jAdj C τ s).counit.app M) ≫ _
    rw [← Category.assoc, (jAdj C τ s).right_triangle_components]
    exact (Category.id_comp _).symm
  · have hz (N : VaryingRing.Modules C τ U) :
        IsZero ((VaryingRing.pull C τ c).obj ((VaryingRing.extension C τ s).obj N)) := by
      obtain ⟨e⟩ := VaryingRing.ordinary_clopen_iso C τ s
      have := VaryingRing.moduleJAdj_unit_isIso C τ s
      let ff := (VaryingRing.moduleJAdj C τ s).fullyFaithfulLOfIsIsoUnit
      let fp := ff.ofIso e
      have := fp.full
      have := fp.faithful
      have := (VaryingRing.moduleAdj C τ s).isIso_unit_app_of_iso (e.app N)
      have := VaryingRing.moduleOpenToP_isIso C τ s
      have hi : IsIso ((VaryingRing.modulePi C τ s).app
          ((VaryingRing.extension C τ s).obj N)) := by
        dsimp only [VaryingRing.modulePi, NatTrans.comp_app, Functor.whiskerLeft_app]
        infer_instance
      have hii := (VaryingRing.pull C τ c).map_isIso
        ((VaryingRing.modulePi C τ s).app ((VaryingRing.extension C τ s).obj N))
      rw [(VaryingRing.modulePi_components C τ s c hc _).2] at hii
      exact ((isIsoZero_iff_source_target_isZero _ _).mp hii).1
    let F := extension C τ s ⋙ pull C τ c
    have hz' (N : Modules C τ U) : IsZero (F.obj N) := by
      change IsZero ((pull C τ c).obj ((extension C τ s).obj N))
      rw [pull_eq, extension_eq]
      exact hz N
    have hzD := F.isZero_mapDerivedCategory_obj ((P C τ s).obj M) (fun q ↦ hz' _)
    have hzT := hzD.of_iso
      ((Functor.mapDerivedCategoryCompIso (extension C τ s) (pull C τ c)).app
        ((P C τ s).obj M)).symm
    exact hzT.eq_of_tgt _ _


end AlgebraicGeometry.ProEtale.SemilinearProperOpen


end ProofEnvironment
