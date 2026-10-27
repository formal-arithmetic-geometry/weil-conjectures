/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Descent along a submersive Stein morphism

Source: Alper, arXiv:1005.2398v3, Proposition 7.1.1, proof, printed p.36;
Rydh, Submersions and effective descent of étale morphisms, Proposition 7.2 and
Theorem 7.4 (blueprint: lem-sfb-stein-submersive-reduced-descent).

Equality on the reduced self fibre product is expressed by its reduced-scheme tests.
Every map from a reduced scheme factors through the reduction, and reduced smooth
scheme charts cover the reduction. Thus these tests express equality on the entire
reduced substack, including its scheme structure, rather than just geometric points.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Precomposition is injective and its image consists precisely of maps agreeing on
 the reduced self fibre product. Morphisms to spaces are compared up to 2-isomorphism.
Source: Alper, arXiv:1005.2398v3, Proposition 7.1.1, exact Hom diagram in its proof,
printed p.36; Rydh, Proposition 7.2 and Theorem 7.4
(blueprint: lem-sfb-stein-submersive-reduced-descent).

Proof:
1. The equalizer of two maps V → Z is an immersion. If p factors through it,
surjectivity makes it closed with full support, and the structure-sheaf isomorphism
kills its defining ideal. Hence the equalizer is V, proving injectivity.
2. For a compatible h, form P = Z × V, P' = Z × U and t = id × p. In an open
neighbourhood of the diagonal of Z where it is closed, the graph of h is closed.
Reduced-relation compatibility makes this neighbourhood and the graph saturated:
common field extensions give points of the reduced self fibre product. Since t is
universally a quotient surjection, the saturated neighbourhood descends to an open A
and the graph descends to a closed subset of A.
3. The map (h,p) : U → A is quasi-compact. Apply
lem-sfb-stack-schematic-image-qc to obtain W closed in A, with U → W schematically
dominant and support the descended graph. The graph section U → W ×_V U is a
surjective closed immersion, hence universally a homeomorphism. Quotient descent
along p then shows that W → V is a universal homeomorphism. Its diagonal is an
immersion and surjective, hence closed; thus W → V is separated.
4. By lem-sfb-separated-space-homeomorphism-affine, W → V is affine. On an affine
étale chart of V, schematic dominance and flat base change give B₀ → B₁ → B₀,
where the second map is injective and the composite is the identity. Injectivity
makes these maps inverse. These local inverses glue, so W → V is an isomorphism.
Its inverse followed by W → Z gives the descended map.
5. Conversely a map factoring through p agrees on both projections. Testing this on
all reduced schemes is equivalent to equality on the reduction: reduced sources
factor through it and its reduced smooth charts detect equality into the sheaf Z.
No condition on geometric fibres is used. -/
theorem stein_submersive_reduced_descent (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (V : AlgebraicSpace (Spec (.of k)))
    (p : BasedFunctor F (discreteModuli V.obj.obj))
    (hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} p)
    (hqs : IsQuasiSeparatedAlgebraicModuliMap p)
    (hsub : ∀ (T : AlgebraicSpace (Spec (.of k))) (g : T ⟶ V),
      Function.Surjective (moduliPointMap (moduliTwoFiberSnd p
        (discreteModuliMap g.hom.hom))) ∧
      ∀ A : Set (ModuliPoints (discreteModuli T.obj.obj)),
        IsOpen A ↔ IsOpen
          (moduliPointMap (moduliTwoFiberSnd p (discreteModuliMap g.hom.hom)) ⁻¹' A))
    (hstein : IsIso (moduliStructureMap hF.1.1 V p))
    (Z : AlgebraicSpace (Spec (.of k)))
    (hZ : AlgebraicSpace.IsRepresentableWith (fun _ _ q ↦ IsImmersion q.left)
      (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj))) :
    (∀ a b : V.obj.obj ⟶ Z.obj.obj,
      Nonempty (ModuliTwoIso (p.comp (discreteModuliMap a))
        (p.comp (discreteModuliMap b))) → a = b) ∧
    ∀ h : BasedFunctor F (discreteModuli Z.obj.obj),
      (∃ a : V.obj.obj ⟶ Z.obj.obj,
        Nonempty (ModuliTwoIso (p.comp (discreteModuliMap a)) h)) ↔
      ∀ (T : Over (Spec (.of k))) [IsReduced T.left]
        (t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct p p)),
        Nonempty (ModuliTwoIso ((t.comp (moduliTwoFiberFst p p)).comp h)
          ((t.comp (moduliTwoFiberSnd p p)).comp h)) := by
  sorry

end CategoryTheory
