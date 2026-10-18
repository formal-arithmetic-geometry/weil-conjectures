/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affineness of a geometric strict-local base
Source: Stacks Project, Tag 0EZV, corrected proof, first paragraph; Tag 04HX.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Base change of a strict henselization along a point factoring through it is affine.
Source: Stacks Project, Tags 0EZV and 04HX.
(blueprint: lem-weil-pbc-strict-local-base-affine).

Proof: the strict henselization is local and its structural map sends the closed point
above the original geometric point, by strictHenselizationResidue. Choose an affine open
chart containing that point. Its inverse image contains the closed point of the local
spectrum, hence is the whole spectrum. The structural map therefore lifts to the chart.
The given map u lifts the other leg by composition. Since the chart inclusion is mono,
the pullback over the chart is also the pullback over S. Both factors and the chart
are affine; their pullback is affine. Transport this instance along the canonical
pullback isomorphism. K may be any field; separable closedness is not needed. -/
theorem strictLocalBase_isAffine {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (K : Type u) [Field K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme s) :
    IsAffine (pullback (Scheme.strictHenselizationStructuralMap s)
      (u ≫ Scheme.strictHenselizationStructuralMap s)) := by
  classical
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, _, hclosed, _, _⟩ := strictHenselizationResidue s rfl
  let := hlocal
  obtain ⟨R, i, hi, y, hy⟩ := S.exists_Spec_apply_eq (s (IsLocalRing.closedPoint Ω))
  let := hi
  have hrange : Set.range (Scheme.strictHenselizationStructuralMap s) ⊆ Set.range i := by
    have hc : IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) ∈
        (Scheme.strictHenselizationStructuralMap s) ⁻¹ᵁ i.opensRange := by
      change Scheme.strictHenselizationStructuralMap s
        (IsLocalRing.closedPoint (Scheme.strictHenselizationRing s)) ∈ Set.range i
      rw [hclosed]
      exact ⟨y, hy⟩
    have htop := (IsLocalRing.closedPoint_mem_iff _).mp hc
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ (Scheme.strictHenselizationStructuralMap s) ⁻¹ᵁ i.opensRange :=
      htop ▸ trivial
    exact hz
  let b := IsOpenImmersion.lift i (Scheme.strictHenselizationStructuralMap s) hrange
  have hb : b ≫ i = Scheme.strictHenselizationStructuralMap s :=
    IsOpenImmersion.lift_fac _ _ _
  have hpb := IsPullback.of_isLimit (pullbackIsPullbackOfCompMono b (u ≫ b) i)
  have : IsAffine (Scheme.strictHenselizationScheme s) :=
    inferInstanceAs (IsAffine (Spec (Scheme.strictHenselizationRing s)))
  have : IsAffine hpb.cone.pt := by
    change IsAffine (pullback b (u ≫ b))
    infer_instance
  have haf := @IsAffine.of_isIso _ _ hpb.isoPullback.inv inferInstance this
  simpa only [Category.assoc, hb] using haf

end AlgebraicGeometry.Etale
