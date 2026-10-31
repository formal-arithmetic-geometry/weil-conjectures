/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex

/-! # Site-perfect evaluation in the intrinsic finite closed presentation

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex.
(blueprint: lem-sf-finite-intrinsic-site-perfect-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The canonical evaluation transpose for the specified intrinsic finite tensor-Hom
structure is invertible for a site-perfect source and every derived target.
Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex; the tensor presentation
is def-weil-derived-pullback-tensor-hom.
(blueprint: lem-sf-finite-intrinsic-site-perfect-evaluation).

Proof: take a normalized ringed-site duality presentation. The theorem
lem-fix-ringed-site-perfect-duality-for-model makes its evaluation comparison an
isomorphism for the given perfect source. Compare its tensor with finiteIntrinsicClosed
using the unique isomorphism between left adjoints of the same internal Hom.
The K-flat tensor comparisons identify this isomorphism with the identity on ordinary
total tensors and identify the counits with ordinary evaluation. The coefficient
unit is identified by its tensor-unit universal property. Under these comparisons,
the intrinsic associator and right unitor carry the evaluation transpose to the
normalized perfect evaluation, up to invertible tensor and unit comparisons.
Equivalently, on a cover with a bounded finite-projective model for the source,
this is the finite-projective tensor-Hom isomorphism, extended to the bounded total
complex; its inverse respects the differential and the signed totalization.
Restriction to the cover detects quasi-isomorphisms of the cohomology sheaves, so
the displayed intrinsic comparison is invertible globally. No bound or
constructibility condition on the second input is used. -/
theorem finiteIntrinsic_sitePerfect_evaluation_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ)
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (_hK : IsFiniteCoefficientSitePerfect l E X n K) :
    IsIso ((finiteIntrinsicClosed l E X n).transpose _ K L
          (((finiteIntrinsicClosed l E X n).monoidal.associator L
              ((finiteIntrinsicDerivedInternalHom l E X n).obj
                (op K, (finiteIntrinsicClosed l E X n).monoidal.tensorUnit)) K).hom ≫
            (finiteIntrinsicClosed l E X n).tensor.map
              (Prod.mkHom (𝟙 L) ((finiteIntrinsicClosed l E X n).evaluation K
                (finiteIntrinsicClosed l E X n).monoidal.tensorUnit)) ≫
            ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor L).hom)) := by
  sorry

end WeilConjectures
