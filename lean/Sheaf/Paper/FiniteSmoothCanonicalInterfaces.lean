/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.PurityNormalCone
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.ReesConeNormalization
import Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence
import Sheaf.AlgebraicGeometry.ConormalConeHomExt

/-! # The normalized extended-Rees and relative-Spec cone comparison

Source: Stacks 0630, 0632; current blueprint `sk-thm-dnc`, Local construction
(blueprint: def-pur-finite-smooth-canonical-interfaces).

The comparison is fixed on homogeneous representatives. The existing section-deformation
and gamma-normalization modules retain ownership of their geometry, bundle adjoints and
etale comparison coordinates; this module introduces only the missing normalized Rees
comparison and its uniquely characterizing specification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem reesConeChart_preimage {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    ⊤ ≤ reesConeChart s U ⁻¹ᵁ
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) := by
  rw [← Scheme.Hom.comp_preimage]
  change ⊤ ≤ reesConeChart s U ⁻¹ᵁ
    ((IsClosedImmersion.lift s _ (Scheme.Hom.purityNormalCone_kernel s) ≫ s) ⁻¹ᵁ U.1)
  rw [IsClosedImmersion.lift_fac]
  exact Scheme.AffineZariskiSite.top_le_preimage_toBase
    s.ker.coequifibered_toNormalConePresheaf U

private theorem reesConeChart_app_isIso {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : V.AffineZariskiSite) :
    IsIso ((reesConeChart s U).appLE
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤
        (reesConeChart_preimage s U)) := by
  have hp : Scheme.Hom.purityNormalProjection s ≫ s =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase :=
    IsClosedImmersion.lift_fac _ _ _
  have hw : Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1) =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, hp]
  have : IsOpenImmersion (reesConeChart s U) := by
    dsimp only [reesConeChart]
    infer_instance
  have hr : (Scheme.AffineZariskiSite.relativeGluingData
      s.ker.coequifibered_toNormalConePresheaf).toBase ⁻¹ᵁ U.1 =
      (reesConeChart s U).opensRange :=
    Scheme.AffineZariskiSite.toBase_preimage s.ker.coequifibered_toNormalConePresheaf U
  rw [Scheme.Hom.appLE]
  have : IsIso ((reesConeChart s U).app
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))) :=
    Scheme.Hom.isIso_app _ _ (by rw [hw, hr])
  have : IsIso (homOfLE (reesConeChart_preimage s U)).op :=
    (eqToIso (le_antisymm le_top (reesConeChart_preimage s U)).symm).op.isIso_hom
  infer_instance

/-- Existence and uniqueness with the homogeneous representative normalization.
Source: Stacks 0630, 0632; sk-thm-dnc, Local construction
(blueprint: def-pur-finite-smooth-canonical-interfaces).
Proof: on each affine chart send a homogeneous class of a in I^n/I^(n+1) to
 a/t^n modulo t in the extended Rees algebra. Changing a by I^(n+1) multiplies
 the corresponding Rees representative by t, so this is well defined. Products
 and constants have the same formulas, and the inverse sends each Laurent term
 back to its homogeneous class. Localization commutes with these formulas;
 relative Spec therefore glues the inverse ring maps. They preserve projection
 and augmentation. The sheaf coproduct presentation and generation of I^n by
 products of n ideal sections show that the displayed degree-one identities,
 together with the structural map, determine every homogeneous class. Affine
 charts cover the cone, so they determine a unique scheme isomorphism. -/
theorem reesConeComparison_existsUnique {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] :
    ∃! q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s,
      ReesConeNormalized s q := by
  classical
  obtain ⟨q, hq⟩ := reesConeComparison_exists s
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  have : IsAffineHom (PurityNormalBundle.projection s) := (PurityNormalBundle.over s).property
  apply conormalCone_hom_ext s (PurityNormalBundle.projection s) (coneAlgebraIso s)
    (Scheme.Hom.purityNormalProjection s) q'.hom q.hom hq'.1 hq.1
  intro U b
  let U' : V.AffineZariskiSite := ⟨U.1, U.2⟩
  have hb : (ConormalGradedAlgebra.powerInclusion s 1).val.app (Opposite.op U.1) b ∈
      s.ker.siteIdeal U' := by
    obtain ⟨e, he⟩ := (ConormalGradedAlgebra.presentation s).powerIdentification 1
    have hh := congrArg (fun k ↦ k.val.app (Opposite.op U.1) b) he
    have hm := (s.ker ^ 1).range_toModulesι_app U
    have hmem : (ConormalGradedAlgebra.powerInclusion s 1).val.app
        (Opposite.op U.1) b ∈ Set.range ((s.ker ^ 1).toModulesι.app U.1) :=
      ⟨e.hom.val.app (Opposite.op U.1) b, hh⟩
    rw [hm] at hmem
    simpa [U', Scheme.IdealSheafData.siteIdeal] using hmem
  have hU' : ⊤ ≤ (reesConeChart s U' ≫ q'.hom) ⁻¹ᵁ
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, hq'.1,
      Scheme.Hom.comp_preimage]
    exact reesConeChart_preimage s U'
  have hU : ⊤ ≤ (reesConeChart s U' ≫ q.hom) ⁻¹ᵁ
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, hq.1,
      Scheme.Hom.comp_preimage]
    exact reesConeChart_preimage s U'
  have h := (hq'.2.2 U' b hb hU').trans (hq.2.2 U' b hb hU).symm
  have hc := reesConeChart_app_isIso s U'
  have hcomp (k : s.ker.normalCone ⟶ PurityNormalBundle.normalCone s)
      (hk : k ≫ PurityNormalBundle.projection s = Scheme.Hom.purityNormalProjection s) :=
    Scheme.Hom.appLE_comp_appLE (reesConeChart s U') k
      (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ U.1))
      (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ U.1)) ⊤
      (by rw [← Scheme.Hom.comp_preimage k (PurityNormalBundle.projection s), hk])
      (reesConeChart_preimage s U')
  rw [← hcomp q'.hom hq'.1, ← hcomp q.hom hq.1] at h
  exact (ConcreteCategory.bijective_of_isIso
    ((reesConeChart s U').appLE _ ⊤ (reesConeChart_preimage s U'))).1 h


/-- The uniquely specified homogeneous comparison, not a choice from bare existence.
Source: Stacks 0630, 0632; sk-thm-dnc
(blueprint: def-pur-finite-smooth-canonical-interfaces). -/
def reesConeComparison {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    s.ker.normalCone ≅ PurityNormalBundle.normalCone s :=
  (reesConeComparison_existsUnique s).exists.choose

/-- Re-export the defining normalization proof of the uniquely selected comparison.
Source: Stacks 0630, 0632; sk-thm-dnc
(blueprint: def-pur-finite-smooth-canonical-interfaces). -/
abbrev reesConeComparison_spec {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    ReesConeNormalized s (reesConeComparison s) :=
  (reesConeComparison_existsUnique s).exists.choose_spec

end AlgebraicGeometry.Etale.FiniteSmoothPurity
