/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PbcCoefficientTwists

import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.Paper.PurTwistSheafLocallyFree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DualizingObjectPurity
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurityDiagonalDualizingObject
import Sheaf.Paper.VectorBundlePurity

/-! # Finite-coefficient smooth purity

Source: Weil conjectures blueprint, main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
thm-pur-finite-coefficient-smooth-purity
(blueprint: thm-pur-finite-coefficient-smooth-purity).

The assertion concerns the specified canonical smooth purity map on the original
small-pro-etale constructible finite-Tor object, at every positive coefficient level.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical finite-coefficient smooth purity map is invertible.
Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
thm-pur-finite-coefficient-smooth-purity
(blueprint: thm-pur-finite-coefficient-smooth-purity).

Proof:
1. Put M = Lf* K, U = A_X(d)[2d], and V = Rf! A_Y. The first factor rho of
   def-pur-smooth-purity-map is the canonical tensor/shift reassociation
   M(d)[2d] ≅ M tensor U, using def-coefficient-twists-detailed.
2. thm-pur-diagonal-dualizing-object gives the normalized orientation alpha : V ≅ U.
   Its hypotheses hold because X and Y are separated finite-type k-schemes and f is
   separated and of finite type, in the domain of def-weil-exceptional-inverse-image.
   Functoriality of tensor makes t = id_M tensor alpha.inv invertible, with inverse
   s = id_M tensor alpha.hom; the two inverse identities follow from those for alpha.
3. The tensor-formula clause of thm-pur-cohomological-smoothness makes the specified
   counit tensor mate beta : M tensor V → Rf! K an isomorphism for this K in Dctf.
   This is the constructible exceptional inverse image and its bounded-class
   adjunction; no unrestricted ambient pro-etale adjoint is used.
4. def-pur-smooth-purity-map defines gamma as rho followed by t followed by beta.
   The inverse is beta.inv followed by s followed by rho.inv. Associativity and the
   inverse identities show that both ordered composites are identities.
5. For the vector-bundle model mentioned in the unit proof, finite type over the
   Noetherian field makes the base Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   cor-pur-vector-bundle-purity and thm-amb-vector-bundle-purity identify the normalized
   map with the adjoint of def-amb-vector-integration. On a trivializing open this is
   lem-amb-affine-space-top-trace: the ordered composite of affine-line counits, with
   rank one normalized by projective-line trace and rank zero by the identity.
   A power of ell kills A and is invertible over k. The comparisons of
   def-pur-affine-line-purity-comparison and def-pur-affine-space-comparison have that
   same adjoint trace: the counit for F2 F1 is eps2 composed with F2(eps1).
   Injectivity of the adjunction bijection identifies these normalized maps.
6. On a finite trivializing cover, cor-pur-dualizing-object-purity and
   lem-pur-projection-purity-agreement identify the restrictions of gamma with this
   vector-bundle map. Their ratio is an endomorphism of A_E(d)[2d]. Cancel the shift;
   lem-pur-twist-sheaf-locally-free and def-coefficient-twists-detailed give a rank-one
   degree-zero sheaf, and lem-weil-pbc-derived-single-fully-faithful identifies its
   derived endomorphisms with sheaf maps. In a frame each is multiplication by a scalar;
   changing the frame by a unit leaves that scalar unchanged. The ratio is locally 1,
   so sheaf uniqueness makes it globally 1, also in rank zero.
-/
theorem isIso_smoothPurityMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    IsIso (P.smoothPurityMap f d K hK) := by
  sorry

end WeilConjectures.PurityFiniteSetting
