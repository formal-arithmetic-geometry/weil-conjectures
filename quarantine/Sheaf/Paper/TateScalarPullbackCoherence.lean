/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts

/-! # Scalar and geometric pullback of ordered finite Tate lines

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, paragraph (1), canonical Tate identifications
(blueprint: lem-sp-tate-scalar-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open Etale.FiniteSmoothPurity

/-- Normalized scalar comparison of an ordered finite Tate line commutes with
geometric pullback. This concerns the Tate lines alone, with no dualizing object,
orientation, or exceptional functor.

Source: latest blueprint, purity-bc-factors proof (1), canonical Tate identifications;
Stacks 03PK, 06YY and 0D6D
(blueprint: lem-sp-tate-scalar-pullback-coherence).

Proof:
1. The two supplied root maps at exponent N are the identity: their composites
with the kernel inclusion are the inclusion, by roots_power and N/N=1. The
normalized root pullbacks commute with these maps, since both composites with
the roots-to-units inclusion are inverse image of that same inclusion.
2. Transpose the degree-one scalar and pullback maps to ordinary sheaf maps.
On every local generator z tensor a tensor b, both routes give the pulled-back
root z' tensor phi(a)b. The generator normalizations in the two comparison
records give this equation. Tensor balancing and sheafification give equality
on the whole sheaf, without a global primitive root or flatness of phi.
3. The finite Tate sheaf is locally free, so its single complex and all its
ordered tensor powers are K-flat. Thus the specified scalar counit and exact
inverse image compute the preceding sheaf maps on these complexes. The
canonical scalar/pullback comparison is the same balancing map on them.
At degree zero both routes are the constant-unit comparison. Induct on d,
using the normalized tensor comparisons at a successor and the equation for
the first root factor. Commute the even shifts through these maps; the root
order is unchanged and there is no odd-degree interchange sign.
4. Transport this etale equality through the comparison functors. The canonical
site/scalar/pullback cube identifies the two transported routes with precisely
the displayed pro-etale composites. -/
theorem tate_scalar_pullback_coherence
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) (N : ℕ) (_hN : 0 < N) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (twR : Etale.OrdinaryFiniteTwistTransport R N hR)
    (twA : Etale.OrdinaryFiniteTwistTransport A N hA)
    {X X' : Scheme.{u}} (u' : X' ⟶ X) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ)
    (sX : CoefficientLineComparison φ N N hR hA X)
    (sX' : CoefficientLineComparison φ N N hR hA X') :
    (proPullback A u').map (proTwistMap d sX) ≫
        ((sitePullbackIso A u').app (line A N hA X d) ≪≫
          (comparison A X').mapIso
            (Etale.vectorIntegrationBaseCoefficientPullback A N hA twA u' hX d)).hom =
      (scalarPullbackProEtaleIso φ u').hom.app ((comparison R X).obj (line R N hR X d)) ≫
        (proScalar φ X').map
          ((sitePullbackIso R u').app (line R N hR X d) ≪≫
            (comparison R X').mapIso
              (Etale.vectorIntegrationBaseCoefficientPullback R N hR twR u' hX d)).hom ≫
          proTwistMap d sX' := by sorry

end AlgebraicGeometry.ProEtale
