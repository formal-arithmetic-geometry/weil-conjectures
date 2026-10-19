/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PurityNormalBundle
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
import Sheaf.Paper.PurityVectorBundleZeroSection
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec

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

/-- The actual cone-to-X map factors through the closed immersion.
Source: Stacks Tags 062Z and 0630 (blueprint: def-pur-normal-bundle).
Proof: on Spec R its ring map kills J, because degree zero in gr_J R is R/J.
The affine restrictions cover X, so the kernel inclusion glues. -/
theorem purityNormalCone_kernel {Z X : Scheme.{u}} (i : Z ⟶ X) :
    i.ker ≤ (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase.ker := by
  sorry

/-- The projection of the actual normal cone to Z, using the unique closed-immersion
factorization; its source is the extended-Rees quotient by t.
Source: Stacks Tag 0630 (blueprint: def-pur-normal-bundle). -/
noncomputable def purityNormalProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : i.ker.normalCone ⟶ Z :=
  IsClosedImmersion.lift i
    (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase
    (purityNormalCone_kernel i)

/-- For a section, the canonical factorization to Z is precisely the published
normal-cone projection formed using its retraction. Thus the normal object in the
DNC statement uses this same associated-graded cone over Z.
Source: blueprint normal bundle and sk-lem-geometry (1)
(blueprint: def-pur-normal-bundle).
Proof: the normal-cone map to X factors through i. Compose this factorization
with g, and use i followed by g equals the identity. This gives the displayed
identity with the published toBase followed by g definition. -/
theorem purityNormalProjection_eq {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : X ⟶ Z) (hs : i ≫ g = 𝟙 Z) :
    purityNormalProjection i = normalConeProj g i := by
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.Scheme.Hom
