/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Left exactness of the sequence-site inverse image

Source: Stacks Project, Sites, Tags 00VC, 00VE, 00WX and 00X5; Zheng §4.1
(blueprint: lem-sp-sequence-inverse-image-left-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale

/-- The sequence-site inverse image is continuous, left adjoint to restriction,
and preserves finite limits. The Kan extension and sheafification are the
components of `spMonoidalSequenceInverseImage`.
Source: Stacks Project, Sites, Tags 00VC, 00VE, 00WX, 00X3 and 00X5;
blueprint/latest, integral direct-image proof (3)
(blueprint: lem-sp-sequence-inverse-image-left-exact).

Proof: the pro-etale base-change functor preserves the final object, fibre
products and covering families. Vertical coverings therefore remain coverings
under its product with the identity of `ℕ`, so the product functor is
continuous. The continuous-functor sheaf pullback adjunction identifies the
left adjoint with the displayed left Kan extension followed by sheafification.
For a target `(n,W)`, the ordinary comma category of pairs `(V, W ⟶ u(V))`
is cofiltered. Lift an object or common predecessor to index `n`; it then maps
to any prescribed objects at indices at least `n`. To equalize two arrows,
equalize their base arrows and use the source index; the index arrows agree
since `ℕ` is a poset. Thus the opposite comma category in the Kan formula is
nonempty and filtered, including for the empty finite limit diagram.
Filtered colimits of sets commute with finite limits, while
sheaf inclusion and sheafification preserve finite limits; hence the displayed
left adjoint preserves finite limits.
-/
theorem spMonoidalSequenceInverseImage_leftExact
    {T T' : Scheme.{u}} (g : T' ⟶ T) :
    ∃ h : ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)).IsContinuous
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (coefficientSequenceTopology (Scheme.ProEt.topology T')),
      Nonempty (spMonoidalSequenceInverseImage T g ⊣
        @Functor.sheafPushforwardContinuous _ _ _ _
          ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)) (Type (u + 1)) _
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (coefficientSequenceTopology (Scheme.ProEt.topology T')) h) ∧
      PreservesFiniteLimits (spMonoidalSequenceInverseImage T g) := by
  let F := Scheme.proEtaleBaseChange g
  let B := (𝟭 ℕ).prod F
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  have : RepresentablyFlat B := by
    constructor
    intro X
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence X.1 X.2 (𝟭 ℕ) F).symm
  have h : B.IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceTopology (Scheme.ProEt.topology T')) := by
    apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    constructor
    intro V S hS
    change (S.functorPushforward B).functorPullback
      (Prod.sectR V.1 T'.ProEt) ∈ Scheme.ProEt.topology T' (F.obj V.2)
    apply (Scheme.ProEt.topology T').superset_covering _
      ((Scheme.proEtaleBaseChangeCoverPreserving g).cover_preserve hS)
    intro W a ha
    obtain ⟨V', k, t, hk, rfl⟩ := ha
    exact ⟨(V.1, V'), Prod.mkHom (𝟙 V.1) k, Prod.mkHom (𝟙 V.1) t, hk, by
      ext <;> simp [B, F]⟩
  let := h
  refine ⟨h, ⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
    (Type (u + 1)) _ _⟩, ?_⟩
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits
      (B.op.lan : ((ℕ × T.ProEt)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (ℕ × T'.ProEt)ᵒᵖ ⥤ Type (u + 1)) :=
    preservesFiniteLimits_op_lan_of_flat B
  unfold spMonoidalSequenceInverseImage
  exact comp_preservesFiniteLimits _ _

end AlgebraicGeometry.ProEtale
