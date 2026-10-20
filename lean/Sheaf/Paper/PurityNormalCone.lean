/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PurityNormalBundle
public import Sheaf.Paper.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Sheaf.RingTheory.ReesAssociatedGradedChart
import Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence

/-! # The actual normal cone and its regular-immersion bundle description

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-normal-bundle.md;
Stacks Project, Tags 0630--0636 (blueprint: def-pur-normal-bundle).

The cone is the published quotient of the extended Rees algebra by t. This is the
associated-graded construction, not an arbitrary smooth bundle datum. Its projection
factors canonically through the closed immersion, and its augmentation is the published
normal-cone zero section. The comparison below identifies it with the recorded
relative-spectrum normal cone; the conormal and regular vector bundle are reused
from that module.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace AlgebraicGeometry.Scheme.Hom

-- Presentation interfaces for (blueprint: pur9-def-normal-cone).

/-- Affine-chart characterization of the cone as the relative spectrum of the
actual associated-graded algebra, with its structural ring map fixed.
Source: Stacks Tags 0630 and 0632; blueprint normal cone definition
(blueprint: def-pur-normal-bundle).
Proof: the published chart is Spec(R[t,J/t]/t). Send the class of a/t^n to
the degree-n class of a in J^n/J^(n+1); the reverse map sends that class back
to a/t^n modulo t. The defining relations prove the maps inverse and they
fix constants. Localization compatibility gives exactly the displayed chart
and structural-map identity, including J=0 and J=R. -/
theorem purityNormalCone_affineChart {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.affineOpens) :
    ∃ e : (((relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase)
          ⁻¹ᵁ U.1).toScheme ≅ Spec (.of (Ideal.associatedGraded (i.ker.ideal U))),
      e.hom ≫ Spec.map (CommRingCat.ofHom
          (Ideal.associatedGradedRingHom (i.ker.ideal U))) =
        ((relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase ∣_ U.1) ≫
          U.2.isoSpec.hom := by
  let H := i.ker.coequifibered_toNormalConePresheaf
  let d := relativeGluingData H
  let W : X.AffineZariskiSite := ⟨U.1, U.2⟩
  have hr : Set.range ((d.toBase ⁻¹ᵁ U.1).ι) =
      Set.range (colimit.ι d.functor W) := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact congrArg (fun V : d.glued.Opens ↦ (V : Set d.glued))
      (by simpa using d.toBase_preimage_eq_opensRange_ι W)
  let e := IsOpenImmersion.isoOfRangeEq (d.toBase ⁻¹ᵁ U.1).ι
    (colimit.ι d.functor W) hr
  obtain ⟨r, hr⟩ := Ideal.rees_associatedGraded_chart (i.ker.ideal U)
  let q : CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)) ≅
      i.ker.normalConePresheaf.obj (op W) :=
    r.toCommRingCatIso
  refine ⟨e ≪≫ Scheme.Spec.mapIso q.op, ?_⟩
  have hc : CommRingCat.ofHom (Ideal.associatedGradedRingHom (i.ker.ideal U)) ≫ q.hom =
      (i.ker.toReesPresheaf ≫ Scheme.toQuotientPresheaf
        i.ker.tIdeal i.ker.map_tIdeal).app (op W) := by
    ext a
    change r (Ideal.associatedGradedRingHom (i.ker.ideal U) a) = _
    obtain ⟨ha, hh⟩ := hr 0 ⟨a, by simp⟩
    change r (Ideal.associatedGradedRingHom (i.ker.ideal U) a) = _ at hh
    rw [hh]
    apply congrArg (Ideal.Quotient.mk _)
    apply Subtype.ext
    simp only [Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, mul_one]
    rfl
  apply (cancel_mono (U.2.isoSpec.inv ≫ U.1.ι)).1
  change (e.hom ≫ Spec.map q.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.associatedGradedRingHom (i.ker.ideal U)))) ≫
        (U.2.isoSpec.inv ≫ U.1.ι) = _
  rw [Category.assoc e.hom, ← Spec.map_comp, hc]
  have hd : Spec.map ((i.ker.toReesPresheaf ≫ Scheme.toQuotientPresheaf
      i.ker.tIdeal i.ker.map_tIdeal).app (op W)) ≫ U.2.isoSpec.inv ≫ U.1.ι =
      colimit.ι d.functor W ≫ d.toBase := (d.ι_toBase W).symm
  simp only [Category.assoc, hd, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact (morphismRestrict_ι d.toBase U.1).symm

/-- The actual extended-Rees zero fibre is the recorded relative-spectrum normal cone,
with the same projection and degree-zero augmentation. In particular its regular
vector-bundle structure is the existing `PurityNormalBundle.vectorBundle`, transported
through this comparison, rather than a second definition of that bundle.
Source: Stacks Tags 0630, 0632, 0636; blueprint def-pur-normal-bundle
(blueprint: def-pur-normal-bundle).
Proof: the affine chart above identifies the quotient R[t,J/t]/t with gr_J R,
sending a/t^n to the homogeneous class of a. The affine charts of
ConormalGradedAlgebra.presentation identify its algebra with the same graded ring,
with the same structural map and homogeneous classes. Compose these chart
identifications with relative Spec. Localization preserves the representative
formulas, so the isomorphisms agree on overlaps and glue. They fix constants,
hence commute with the projections to Z. Both augmentations kill all positive
homogeneous degrees and fix degree zero, so their zero sections also agree.
The recorded regular_spec, vectorBundle and vectorBundle_zeroSection then supply
all regular-immersion bundle assertions without another conormal construction. -/
theorem purityNormalCone_comparison {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    ∃ e : i.ker.normalCone ≅ PurityNormalBundle.normalCone i,
      e.hom ≫ PurityNormalBundle.projection i = purityNormalProjection i ∧
        i.normalConeZeroSection ≫ e.hom = PurityNormalBundle.zeroSection i := by
  obtain ⟨e, he⟩ :=
    AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_exists i
  exact ⟨e, he.1, he.2.1⟩

end AlgebraicGeometry.Scheme.Hom
