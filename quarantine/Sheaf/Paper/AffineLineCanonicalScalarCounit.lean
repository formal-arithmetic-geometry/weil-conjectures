/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility

/-! # Scalar compatibility for one ordered affine coordinate

Source: blueprint Charts, scalar mates for the standard affine-line compactification
(blueprint: lem-sp-affine-line-canonical-scalar-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The canonical root-normalized right comparison respects the actual open/projective
composite counit.
Source: blueprint Charts, scalar mates for the standard affine-line compactification
(blueprint: lem-sp-affine-line-canonical-scalar-counit).

Proof: The standard compactification coefficient map is the proper coefficient map
followed by the open-extension coefficient isomorphism. The latter is defined by
transposing the open unit against the exact scalar/pullback comparison. The triangle
identities therefore give the open counit square, after transport from exact to derived
pullback. The projective counit square is lem-sp-p1-counit-scalar. Its same-annihilator
root map is the identity: cancel the root inclusion in roots_power, using N/N=1.
Its generator equation then identifies the sheaf adjunct with reductionEtaleTateMap
by uniqueness. The scalar-adjunction single-complex equation identifies its derived
normalization with reductionEtaleTateExtensionMap. Hence its right comparison is
reductionEtaleP1ScalarIso. Expand the composite counit. Naturality of the open counit
moves the projective right comparison through it. Apply the open counit square,
then naturality of the proper scalar map, then the projective counit square.
Functoriality gives exactly the scalar image of the A composite counit. Finite-Tor
constructibility supplies the allowed projective input; no coefficient flatness is used.
The formulas also hold for empty schemes, zero objects and zero coefficient rings. -/
theorem affineLineCanonicalScalarCounit
    (ell p n : ℕ) [Fact ell.Prime] (hp : 0 < p) (hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
    (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
    (dA : OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
    (dB : OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT)
    (K : DerivedCategoryModule A T)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A T K) :
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ
        (affineTraceLineCompactification T) ((affineTraceLineRight A (ell ^ n) hA T).obj K) ≫
      (affineTraceLineLeft B T).map
        (ProEtale.reductionEtaleLineScalarIso φ T (ell ^ n) hA hB hT K).hom ≫
      (affineTraceLineAdjunction B (ell ^ n) hB tB T hT dB).counit.app
        ((scalarExtension φ T).obj K) =
    (scalarExtension φ T).map
      ((affineTraceLineAdjunction A (ell ^ n) hA tA T hT dA).counit.app K) := by
  sorry

end AlgebraicGeometry.Etale
