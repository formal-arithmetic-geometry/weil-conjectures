/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor-product comparison for a single affine chart

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Morphisms, Tag 01TQ.
(blueprint: lem-weil-pbc-affine-chart-tensor-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A fixed affine triple admits one finitely presented algebra map whose tensor
base changes describe the restricted chart morphism for every compatible affine base open.
There is no inverse system or limiting cone in this statement.

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Morphisms, Tag 01TQ;
Limits, Tag 07RP, affine reduction.
(blueprint: lem-weil-pbc-affine-chart-tensor-comparison).

Proof: Set B = Γ(Y₀,V) and C = Γ(X₀,U). The isomorphism e0 identifies R with
Γ(S,W). Transport the algebra structures given by Y₀.hom.appLE W V eV and
X₀.hom.appLE W U along this identification. The inclusion needed for the latter
follows from eU, eV, and f₀.left ≫ Y₀.hom = X₀.hom. The restriction
f₀.left.appLE V U eU is an R-algebra map φ by functoriality of appLE.
Its underlying ring map is finitely presented by finitePresentation_appLE hV hU eU;
this is precisely φ.FinitePresentation. For any t and compatible e, the inverse
image of V in Y_T is V ×_W W_T, and the inverse image of U in X_T is U ×_W W_T.
Indeed their structure maps factor through W_T by the two given open inclusions;
the open pullback universal property identifies these schemes and projections.
Apply hV.isoSpec, hU.isoSpec, e0 and e, then pullbackSpecIso, to identify them
with Spec(A ⊗[R] B) and Spec(A ⊗[R] C). Compatibility h ensures that these are
pullbacks over the algebraMap R A. The chart map corresponds to Spec(id ⊗ φ):
check its two projections using the identities on a ⊗ 1 and 1 ⊗ b, and use
pullback uniqueness. The restricted map factors the original source-chart map through the target
chart inclusion, giving the asserted equality. Empty charts cause no exception: the same
pullback and spectrum identities hold for zero coordinate rings. -/
theorem exists_affineChart_tensorComparison
    {S : Scheme.{u}} (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFinitePresentation f₀.left]
    (W : S.Opens) (hW : IsAffineOpen W)
    (V : Y₀.left.Opens) (hV : IsAffineOpen V) (eV : V ≤ Y₀.hom ⁻¹ᵁ W)
    (U : X₀.left.Opens) (hU : IsAffineOpen U) (eU : U ≤ f₀.left ⁻¹ᵁ V)
    (R : CommRingCat.{u}) (e0 : W.toScheme ≅ Spec R) :
    ∃ (B C : CommRingCat.{u}) (aB : Algebra R B) (aC : Algebra R C),
      letI := aB
      letI := aC
      ∃ φ : B →ₐ[R] C, φ.FinitePresentation ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ S) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ W).toScheme ≅ Spec A),
            t.resLE W _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            ∃ g : ((pullback.fst X₀.hom t) ⁻¹ᵁ U).toScheme ⟶
                ((pullback.fst Y₀.hom t) ⁻¹ᵁ V).toScheme,
              g ≫ ((pullback.fst Y₀.hom t) ⁻¹ᵁ V).ι =
                ((pullback.fst X₀.hom t) ⁻¹ᵁ U).ι ≫
                  ((Over.pullback t).map f₀).left ∧
              Nonempty (Arrow.mk g ≅ Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by sorry

end AlgebraicGeometry
