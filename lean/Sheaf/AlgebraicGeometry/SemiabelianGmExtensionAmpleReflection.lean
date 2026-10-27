module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.AffineFreeSplitTorusInvariants
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover

/-! # Ampleness reflected by a semiabelian extension by the multiplicative group

Source: the agent-formulated relative group-quotient prerequisite supporting Raynaud,
Faisceaux amples, XI 1.11 (the latter supports the field abelian-quotient case only).
The accepted DAG proof supplies the relative symmetric formulation; its original
literature reference is marked WANTED.
(blueprint: lem-sfb-semiabelian-gm-extension-ample-reflection).

The rank-one relative split torus is the multiplicative group over S. Kernel and
local-surjectivity conditions express exactness as fppf sheaves, using the given
commutative group laws. Ampleness is absolute over the specified affine base.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Pullback along a semiabelian group extension by Gm reflects absolute ampleness
of an invertible module symmetric under inversion.

Source: the agent-formulated relative prerequisite supporting Raynaud, Faisceaux
amples, XI 1.11; the original source for this relative assertion is WANTED.
(blueprint: lem-sfb-semiabelian-gm-extension-ample-reflection).

Proof, following the accepted seven-step DAG argument:
1. Finite presentation gives finite type. By lem-weil-pbc-finite-type-over-noetherian,
   E and H are Noetherian. Apply lem-sfb-semiabelian-geometric-power-integrality
   with n = 1 and lem-weil-geometrically-connected-algebraic-closure to their
   geometric fibres. Smoothness, finite type and separatedness persist under
   base change by lem-pc-proper-base-change, lem-sfb-finite-type-composition-base-change
   and lem-weil-pbc-separated-base-change. Identity sections and
   lem-sbc-smooth-connected-generic-geometry give normal local domains on E and H.
   The affine base coordinate ring is Noetherian by pqf-lem-affine-open-locnoeth.
2. The kernel acts on E by translation. The equality q a = q p gives q*M its
   canonical linearization. The assumed inversion symmetry of M pulls back to
   inversion symmetry of q*M, compatible with inversion on Gm. Tensor powers and
   composite pullbacks use lem-weil-pbc-invertible-pullback-tensor.
3. At the identity over each s in S, lem-sfb-linearized-ample-eigen-affine-cover
   gives an eigensection sigma of a positive power of q*M with affine nonvanishing
   locus U. Transfer its inverse pullback through the symmetry isomorphism to tau;
   its weight is the opposite weight. Thus rho = sigma tensor tau has weight zero.
   Its nonvanishing locus W = U intersect inversion inverse U is affine by
   lem-sc-affine-cap-section-open and contains that identity point.
4. By lem-trf-fppf-covering-is-fpqc and lem-pc-fpqc-descent, the weight-zero section
   descends to a section v of M to the power 2n. Its inverse-image nonvanishing locus
   is W by lem-weil-pbc-invertible-pullback-tensor.
5. By lem-weil-pbc-noetherian-open-subscheme-noetherian and
   lem-weil-pbc-qc-open-immersion-finite-type, W is finite type over S. Apply
   lem-sfb-affine-free-split-torus-invariants to its free Gm action. Its invariant
   spectrum is also the quotient H_v, by lem-trf-fppf-covering-base-change and
   lem-galois-yoneda-fully-faithful. Hence H_v is affine and meets the fibre over s.
6. The image of H_v in S is open by lem-pc-smooth-flat and
   lem-weil-pbc-flat-lfp-open. Choose a principal affine neighbourhood D(f) of s
   inside that image. The restriction of H_v is affine and meets every fibre.
   Base-change permanence, lem-sc-affine-cap-section-open and
   lem-weil-pbc-qcqs-morphism-permanence allow
   lem-sfb-group-affine-section-ampleness to prove ampleness over D(f).
7. These principal opens cover S. Apply lem-trf-scheme-relative-ample-affine-cover
   to the quasi-compact H over the affine S, giving absolute ampleness of M.
No cubical structure, properness or norm hypothesis is used. -/
theorem semiabelian_gm_extension_ample_reflection
    {S : Scheme.{u}} [IsAffine S] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (E H : Grp (Over S)) [IsCommMonObj E.X] [IsCommMonObj H.X]
    [Smooth E.X.hom] [IsSeparated E.X.hom]
    [LocallyOfFinitePresentation E.X.hom] [QuasiCompact E.X.hom]
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (hE : HasSemiabelianGeometricFibres E)
    (hH : HasSemiabelianGeometricFibres H)
    (q : E ⟶ H) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    (j : relativeSplitTorus S 1 ⟶ E)
    (hkernel : IsPullback j.hom.hom (toUnit (relativeSplitTorus S 1).X)
      q.hom.hom η[H.X])
    (hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (yoneda.map q.hom.hom))
    (M : H.X.left.Modules) [M.IsInvertible]
    (hsymmetric : Nonempty ((Scheme.Modules.tensorPullback (ι[H.X]).left).obj M ≅ M))
    (hample : @Scheme.Modules.IsAmple E.X.left
      ((Scheme.Modules.tensorPullback q.hom.hom.left).obj M)
      (((Scheme.Modules.invertible_pullback_tensor q.hom.hom.left).1 M).2)) :
    Scheme.Modules.IsAmple H.X.left M := by
  sorry

end AlgebraicGeometry
