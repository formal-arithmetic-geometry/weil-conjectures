/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry

import WeilConjectures.AlgebraicGeometry.VectorIntegrationIdentityUnit
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSwapChartPrefix

/-! # Frame calculation for block exchange of vector integration

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-integration-swap-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private lemma cancel_action {C : Type*} [Category C] {X Y Z W U : C}
    (f : X ⟶ Y) (b : Y ⟶ Z) (a : X ⟶ W) (e : W ⟶ Z)
    (z : Z ⟶ Z) (q : Z ⟶ U) (q' : W ⟶ U)
    (hp : f ≫ b = a ≫ e ≫ z) (hz : z ≫ q = q) (he : e ≫ q = q') :
    f ≫ b ≫ q = a ≫ q' := by
  rw [← Category.assoc, hp, Category.assoc, Category.assoc, hz, he]

private lemma finish_chart {C E : Type*} [Category C] [Category E] (P : C ⥤ E)
    {X Y Z : C} {W₁ W₂ W₃ W₄ W₅ W₆ U : E}
    (x : X ⟶ Y) (y : Y ⟶ Z)
    (a : P.obj Z ⟶ W₁) (b : W₁ ⟶ W₂) (c : W₂ ⟶ W₃) (q : W₃ ⟶ U)
    (d : P.obj X ⟶ W₄) (e : W₄ ⟶ W₅) (f : W₅ ⟶ W₆) (q' : W₆ ⟶ U)
    (h : P.map (x ≫ y) ≫ (a ≫ b ≫ c) ≫ q = (d ≫ e ≫ f) ≫ q') :
    P.map x ≫ P.map y ≫ a ≫ b ≫ c ≫ q = d ≫ e ≫ f ≫ q' := by
  simpa only [Functor.map_comp, Category.assoc] using h

/-- Transport through block exchange preserves the prescribed trace on a single frame.
The input k need only have the prescribed restriction on the supplied target frame;
it need not be a globally normalized integration map.
Source: blueprint vector-bundle purity proof, paragraph 2, frame independence and
ordered affine counits; geometric-descent Step 7.
(blueprint: lem-pur-vector-integration-swap-local).

Proof: restrict the identity-base swap square to V. Its top map is the linear
isomorphism induced by biproduct braiding, by its symmetric-algebra generator formula.
In the two supplied frames, of the same rank r+s=s+r, this is an invertible linear
substitution. Paste its square with the inverse-coordinate square of the target
frame. Compact-support exchange pasting identifies this with the inverse-coordinate
square of the source frame followed by that linear substitution. The Tate coefficient
comparison is the inverse-image compositor followed by the rank equality; its
composition equations make these precisely the coefficient identifications in the
local traces. Restriction commutes with exchange, and hk replaces the restricted k
by the target affine counit. Linear trace invariance cancels the substitution. The
identity-base and constant-unit comparisons cancel by their unit equations, leaving
the source local trace. Inverse exchange gives the displayed formula. This only uses
a single open and its two frames, not global integration or gluing. Rank zero gives
the identity substitution; the empty open and zero coefficient ring are included.
-/
theorem vectorIntegration_swap_local (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.swap S r s F G)).obj
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.swap S r s F G)
        (VectorBundleZeroSection.π S (s + r) (VectorTraceGeometry.sum S G F))
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
        (by simpa only [Category.comp_id] using
          (VectorTraceGeometry.swap_isPullback S r s F G).w.symm)).symm.app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm s r))))
    (b : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.swap_isPullback S r s F G)).app
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).map c.hom)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S (r + s) (VectorTraceGeometry.sum S F G) V)
    (e' : VectorBundleZeroSection.Trivialization S (s + r) (VectorTraceGeometry.sum S G F) V)
    (k : vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F) ⟶
      ordinaryFiniteUnit A S)
    (hk : (ordinaryFinitePullback A V.ι).map k ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS (s + r)
        (VectorTraceGeometry.sum S G F) V e') :
    (ordinaryFinitePullback A V.ι).map
        (b.inv ≫ (ordinaryFinitePullback A (𝟙 S)).map k ≫
          (ordinaryFiniteUnitPullback A (𝟙 S)).hom) ≫
      (ordinaryFiniteUnitPullback A V.ι).hom =
    vectorIntegrationLocalTrace N hN A hA t D S hS (r + s)
      (VectorTraceGeometry.sum S F G) V e := by
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  have hu := vectorIntegration_identity_unit A S
  have hn := (affineLinearPullbackId A S).hom.naturality k
  simp only [Functor.id_map] at hn
  rw [hu, hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [hk]
  obtain ⟨g, sq, hp⟩ := vectorIntegration_swap_chart_prefix
    N hN A hA S hS r s F G c hc b hb t V e e'
  obtain ⟨sq', hi⟩ := affineSpaceLinearTraceInvariance N hN A hA t D V.toScheme
    (affineTracePullbackInvertible N V.ι hS) (s + r) g
  have hsq : sq' = sq := Subsingleton.elim _ _
  subst sq'
  have hi' : affineLinearTraceAction N hN A hA t V.toScheme
      (affineTracePullbackInvertible N V.ι hS) (s + r)
      (affineTraceLinearMap V.toScheme (s + r) g) sq ≫
        affineTraceCounit A N hA t D V.toScheme
          (affineTracePullbackInvertible N V.ι hS) (s + r) =
      affineTraceCounit A N hA t D V.toScheme
        (affineTracePullbackInvertible N V.ι hS) (s + r) := hi
  have ht (d d' : ℕ) (h : d = d') :
      eqToHom (congrArg (fun n ↦ (affineTraceLeft A V.toScheme n).obj
        ((affineTraceRight A N hA V.toScheme n).obj (ordinaryFiniteUnit A V.toScheme))) h) ≫
        affineTraceCounit A N hA t D V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d' =
      affineTraceCounit A N hA t D V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d := by
    subst d'
    simp only [eqToHom_refl, Category.id_comp]
  have hp' := cancel_action _ _ _ _ _ _ _ hp hi' (ht _ _ (Nat.add_comm r s))
  exact finish_chart (ordinaryFinitePullback A V.ι) _ _ _ _ _ _ _ _ _ _ hp'

end AlgebraicGeometry.Etale
