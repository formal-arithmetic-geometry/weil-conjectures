module

public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen

/-! # Special-fibre positivity of a symmetric cubical line over a trait

Source: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes,
LNM 119, XI 1.13 / 1.16, trait specialization input; compare Moret-Bailly VI 3.1
and Lan, revised thesis, Lemma 4.2.1.6.
(blueprint: lem-sfb-trait-symmetric-cubical-specialization)

This is the DAG's agent-formulated supporting lemma, including nonproper generic
fibres, rather than a verbatim transcription of those sources. The original Raynaud
and Moret-Bailly passages remain WANTED in the project's literature inventory.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A generically ample symmetric cubical rigidified line has ample special fibre.
Source: Raynaud XI 1.13 / 1.16, trait specialization input; compare Moret-Bailly VI 3.1
and Lan revised thesis Lemma 4.2.1.6; agent-formulated supporting lemma of the DAG.
(blueprint: lem-sfb-trait-symmetric-cubical-specialization)

Proof plan from the accepted DAG split:
1. A DVR is Noetherian and regular of dimension one (lem-sc-dvr-dimension-one).
   Smooth ascent of regularity (lem-weil-pbc-regular-ring-smooth-ascent) makes H
   regular. Finite presentation makes it quasi-compact, and separatedness over
   the affine trait makes it separated as a scheme.
2. At any x in H_k, lem-sfb-regular-scheme-affine-line-section-cover supplies an
   invertible A and a section t with affine nonvanishing neighbourhood H_t of x.
   Pullback and the affine fibre-product formula give an affine neighbourhood
   (H_k)_{t_k}; use lem-weil-pbc-invertible-pullback-tensor and
   lem-weil-pbc-fibre-product-affine-spectra.
3. Apply lem-weil-pbc-coherent-twist-global-generation to the finite-type dual
   A_K and the ample B_K. For some n > 0, C_K = A_K dual tensor B_K^n has a
   section nonzero at the identity. The tensor-pullback identities identify it
   with the generic restriction of C = A dual tensor B^n.
4. Semiabelian geometric fibres are connected: torus cosets are connected and
   their fppf quotient is the connected abelian variety. Hence
   lem-sfb-trait-primitive-section-specialization supplies a section of C whose
   special restriction is nonzero.
5. Smoothness, separatedness and finite presentation persist after base change.
   Apply lem-sfb-semiabelian-effective-square-generation to this special section
   to obtain global generation of C_k^2. A generating section u is nonzero at x.
6. Evaluation against duals identifies A_k^2 tensor C_k^2 with B_k^(2n).
   The section t_k^2 tensor u is nonzero at x. By
   lem-sc-tensor-section-affine-open its nonvanishing locus is the intersection
   of (H_k)_{t_k} with (H_k)_u and is affine.
7. The special fibre is quasi-compact by finite presentation. The preceding
   positive-power affine section neighbourhood at each x is precisely
   def-weil-pbc-ample-invertible-module, so B_k is ample.

The fraction field is arbitrary and the residue field is the actual quotient
R / maximalIdeal R. No completeness, henselianity, excellence, algebraic
closedness or properness hypothesis is imposed. -/
theorem trait_symmetric_cubical_specialization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Grp (Over (Spec (.of R)))) [IsCommMonObj H.X]
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (hH : HasSemiabelianGeometricFibres H) (B : CubicalRigidifiedLine H.X)
    (hample : @Scheme.Modules.IsAmple _
      (B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).line
      (B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).invertible)
    (hsymmetric : Nonempty
      ((Scheme.Modules.tensorPullback
        (GrpObj.inv (X := CubicalLine.baseChangedGroup
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) H.X)).left).obj
        (B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).line ≅
        (B.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).line)) :
    @Scheme.Modules.IsAmple _
      (B.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).line
      (B.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).invertible := by
  sorry

end AlgebraicGeometry
