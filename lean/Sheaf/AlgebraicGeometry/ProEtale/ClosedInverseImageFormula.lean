/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.RefinementCoefficientRealization
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-!
# Closed inverse image as sheafification on the affine basis

Source: blueprint sec-smooth-purity/sk-prop-sf-open-closed-triangle,
order 1845; Stacks Project, Tag 09BL (1)
(blueprint: lem-exc-closed-inverse-image-formula).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The closed inverse image is the module sheafification of `V ↦ F(v(V))`.
The input is a module over the recorded continuous-function coefficient ring sheaf.
Both sides are expressed through its canonical fixed-scalar presentation, the inverse
of `finiteCoefficientRealization`. In this presentation inverse image is `upperStar`
with values in left `Λ`-modules, and the comparison is an isomorphism of module sheaves.
In particular, no commutativity of the finite coefficient ring is required.

Source: blueprint order 1845; Stacks Project, Tags 09BK and 09BL (1)
(blueprint: lem-exc-closed-inverse-image-formula).

Proof:
1. By lem-weil-pbc-ind-etale-basis, restriction to the affine ind-etale bases
   determines sheaves and morphisms. Direct image on these bases is precomposition
   with u = closedSiteBaseChange; v = closedSiteLift is left adjoint to u by
   lem-exc-closed-site-adjunction, with unit eta and counit epsilon.
2. Set P(V) = F(v(V)), with restrictions F(v(a)). Send beta : F → i_*G to
   alpha_V = G(eta_V) beta_v(V). Conversely send alpha : P → G to
   beta_W = alpha_u(W) F(epsilon_W). Naturality follows from the naturality of
   eta, epsilon, alpha and beta. These component maps preserve addition.
3. Naturality and the triangle identities epsilon_v(V) v(eta_V) = id and
   u(epsilon_W) eta_u(W) = id show that these constructions are inverse.
   Precomposition and postcomposition commute with them, so the bijection is natural.
4. The universal property of def-weil-pbc-sheafification now makes P-sharp left
   adjoint to direct image. The inverse-image adjunction and uniqueness of left
   adjoints (lem-weil-pbc-conjugate-iso-unit-equation) identify P-sharp with i-inverse.
5. Precomposition preserves products, and set sheafification preserves finite
   products (lem-weil-pbc-sheafification-sets-exact). Applying these functors to
   addition, negation, zero and the scalar action transports every operation and
   its defining equalities. Naturality of the comparison at projections and each
   operation makes it compatible with all module operations, including nullary ones.
6. The canonical coefficient identification of
   prop-weil-pbc-proetale-constant-ring-map identifies this module inverse image
   with i-star of def-weil-pbc-proetale-operations. For left modules the scalar
   extension isomorphism is r tensor m ↦ c-inverse(r)m, with inverse m ↦ 1 tensor m;
   balancing proves both inverse identities. Restriction along constant sections is
   precisely the inverse realization used below. Thus the formula holds for every
   input module, including noncommutative coefficients. It asserts sheafification,
   without asserting that the displayed presheaf is already a sheaf. -/
theorem closed_inverseImage_sheafification (A : Type u) [CommRing A] (I : Ideal A)
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : ProEtale.FiniteCoefficientModules (Spec (.of A)) Λ) :
    Nonempty
      (((toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
          (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I))))).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
          ((ProEtale.finiteCoefficientRealization (Spec (.of A)) Λ).asEquivalence.inverse.obj
            F)) ≅
        (presheafToSheaf (topology (Spec (.of (A ⧸ I)))) (ModuleCat.{u + 1} Λ)).obj
          ((closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙
            ((ProEtale.finiteCoefficientRealization (Spec (.of A)) Λ).asEquivalence.inverse.obj
              F).obj)) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  let D := ModuleCat.{u + 1} Λ
  have : Limits.HasLimitsOfSize.{u, u + 1} D :=
    Limits.hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} D
  obtain ⟨adj, _⟩ := exists_closedSiteAdjunction A I
  obtain ⟨_, _, _, _, hco, _, _, _⟩ := affine_closed_site_functor_properties A I
  let : v.IsCocontinuous (topology Z) (topology X) := hco
  let : r.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).IsContinuous
      (ProEt.topology X) (ProEt.topology Z) := ProEt.isContinuous_overPullback i
  let RX := (toProEt X).sheafPushforwardContinuous D (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous D (topology Z) (ProEt.topology Z)
  let : RX.IsEquivalence :=
    isEquivalence_sheafPushforwardContinuous_toProEt (S := X)
  let : RZ.IsEquivalence :=
    isEquivalence_sheafPushforwardContinuous_toProEt (S := Z)
  -- The site adjunction gives the linear Hom formulas before sheafification.
  let L := sheafToPresheaf (topology X) D ⋙
    (Functor.whiskeringLeft _ _ D).obj v.op ⋙ presheafToSheaf (topology Z) D
  let R := r.sheafPushforwardContinuous D (topology X) (topology Z)
  let a : L ⊣ R :=
    ((adj.op.whiskerLeft D).comp (sheafificationAdjunction (topology Z) D)).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf (topology X) D))
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  have t : r ⋙ toProEt Z ≅ toProEt X ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ i := Iso.refl _
  let : (toProEt X ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).IsContinuous
      (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (ProEt.topology X) (ProEt.topology Z)
  let : (r ⋙ toProEt Z).IsContinuous (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (topology Z) (ProEt.topology Z)
  -- Full-site and affine-basis direct images agree by the base-change square.
  let beta : ProEtale.lowerStar D i ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i)
      D (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm D (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp r (toProEt Z) D
      (topology X) (topology Z) (ProEt.topology Z)).symm
  -- Transport the left adjoints across the two affine-basis equivalences.
  let alpha := ((mateEquiv (ProEtale.upperStarLowerStarAdjunction D i) a).symm
    beta.hom).natTrans
  have : IsIso alpha :=
    isIso_inverseMate_of_equivalences (ProEtale.upperStarLowerStarAdjunction D i) a beta
  exact ⟨((asIso alpha).symm.app
    ((ProEtale.finiteCoefficientRealization X Λ).asEquivalence.inverse.obj F))⟩

end AlgebraicGeometry.Scheme.AffineProEt
