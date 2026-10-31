/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.SecSmoothPurity.OpenScalarExchange

/-!
# Extension by zero and normalized open compositors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph: compatibility of the
normalized open comparison with the source-open compositor
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).

The theorem states the ordinary and derived unit-normalized pullback comparison,
the sectionwise extension-by-zero compositor, and its compatibility with the
normalized left-adjoint presentation. The proof follows the four steps in the DAG:
ordinary unit sections determine the comparison; exact termwise descent and flat-term
K-flat resolutions identify the derived compositor; the sectionwise sheafified
extension compositor is characterized by the open-adjunction unit; and mate pasting
identifies its normalized left-adjoint presentation. Identity, empty, and zero cases
are included in the quantified data; the identity and associativity laws are stated
by the companion declarations below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The normalized open comparison preserves pullback and extension compositors.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).

Proof: Step 1 uses the sectionwise unit equation for `openSquarePullbackModel` to
identify the ordinary tensor and intrinsic pullback compositors. Step 2 descends this
equation termwise and uses a flat-term K-flat resolution to identify the descended
tensor compositor with the canonical unbounded derived one. Step 3 constructs the
sectionwise extension-by-zero compositor from the open-adjunction unit and identifies
its inverse with `sfIntrinsicDerivedOpenComp`. In Step 4, `cJ` is the
`leftAdjointUniq` comparison between the composite normalized open adjunction and the
composite open adjunction; its conjugate is the inverse of
`proEtaleConstantRingPullbackComposition`. Mate pasting with `reductionOpenModel`
gives the last equation. Naturality is built into the natural isomorphisms. Identity
opens, empty opens, and zero objects are covered by the definitions and companions.
-/
theorem proEtale_open_coefficient_r_compositor
    (A : Type u) [CommRing A] [Finite A]
    {U V Z : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    let P₁ := proEtaleConstantRingPullback A j₁
    let P₂ := proEtaleConstantRingPullback A j₂
    let P₁₂ := proEtaleConstantRingPullback A (j₁ ≫ j₂)
    let I₁ := sfIntrinsicPullback A j₁
    let I₂ := sfIntrinsicPullback A j₂
    let I₁₂ := sfIntrinsicPullback A (j₁ ≫ j₂)
    let e₁ := openSquarePullbackModel A j₁
    let e₂ := openSquarePullbackModel A j₂
    let e₁₂ := openSquarePullbackModel A (j₁ ≫ j₂)
    let dtenO := (Classical.choose
      (proEtaleConstantRingPullbackComposition_ordinary j₁ j₂ A)).symm
    let dten := proEtaleConstantRingPullbackComposition j₁ j₂ A
    let dint := (sfIntrinsicPullbackComp A j₁ j₂).symm
    let dintD := (sfIntrinsicDerivedPullbackComp A j₁ j₂).inv
    let cA := (sfIntrinsicDerivedOpenComp A j₁ j₂).symm
    let r₁ := reductionOpenModel A j₁
    let r₂ := reductionOpenModel A j₂
    let r₁₂ := reductionOpenModel A (j₁ ≫ j₂)
    let a₁ := Scheme.proEtaleRingDerivedOpenAdjunction j₁
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing U A)
      (Scheme.proEtaleConstantRingComparison j₁ A)
    let a₂ := Scheme.proEtaleRingDerivedOpenAdjunction j₂
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing V A)
      (Scheme.proEtaleConstantRingComparison j₂ A)
    let a₁₂ := Scheme.proEtaleRingDerivedOpenAdjunction (j₁ ≫ j₂)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing U A)
      (Scheme.proEtaleConstantRingComparison (j₁ ≫ j₂) A)
    let cJ : openExtension (A := A) j₁ ⋙ openExtension (A := A) j₂ ≅
        openExtension (A := A) (j₁ ≫ j₂) :=
      ((a₁.comp a₂).ofNatIsoRight (by
        simpa only [proEtaleConstantRingDerivedPullback] using dten)).leftAdjointUniq a₁₂
    (dtenO.hom ≫ e₁₂.hom =
        (Functor.isoWhiskerRight e₂ P₁).hom ≫
          (Functor.isoWhiskerLeft I₂ e₁).hom ≫ dint.hom) ∧
      (dten.hom ≫ (Functor.mapDerivedCategoryNatIso e₁₂).hom =
        (Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e₂)
            (proEtaleConstantRingDerivedPullback A j₁)).hom ≫
          (Functor.isoWhiskerLeft (sfIntrinsicDerivedPullback A j₂)
            (Functor.mapDerivedCategoryNatIso e₁)).hom ≫ dintD) ∧
      (cA.hom ≫ r₁₂.hom =
        (Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen A j₁) r₂).hom ≫
          (Functor.isoWhiskerRight r₁ (openExtension (A := A) j₂)).hom ≫
          cJ.hom) := by
  sorry

/-- Identity-open normalization for the normalized extension compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).

The identity comparison `ιJ` is the left-adjoint uniqueness comparison against
`Adjunction.id`, using the canonical tensor-pullback identity `pid`.

Proof (node Steps 3-4, identity clause): for `j = 𝟙`, the extension-by-zero presheaf
`P_M = M` is already a sheaf, so the 03DI unit of `j_! ⊣ j⁻¹` is the identity; this is
the identification `sfIntrinsicDerivedOpenId`. The normalized adjunction `J_id ⊣ id_A^*`
has invertible unit, because `pid` identifies `id_A^*` with the identity through the unit
section `m ↦ m ⊗ 1`; `ιJ` is the inverse of that unit. `r_id` satisfies the unit equation
of lem-weil-pbc-conjugate-iso-unit-equation with `δ = e_id`, and `e_id` followed by the
intrinsic identity is the same unit-section identification as `pid`. Hence `r_id`
composed with `ιJ` is the unit identification of `j_!`, which is the displayed equation.
-/
theorem proEtale_open_coefficient_r_compositor_identity
    (A : Type u) [CommRing A] [Finite A] (Z : Scheme.{u}) :
    let pid := proEtaleGlobalEvaluationPullbackId A Z
    let a := Scheme.proEtaleRingDerivedOpenAdjunction (𝟙 Z)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z A)
      (Scheme.proEtaleConstantRingComparison (𝟙 Z) A)
    let ιJ := (a.ofNatIsoRight pid).leftAdjointUniq Adjunction.id
    (reductionOpenModel A (𝟙 Z)).hom ≫ ιJ.hom =
      (sfIntrinsicDerivedOpenId A Z).hom := by
  sorry

/-- The normalized compositor used by the identity and associativity companions: the
`leftAdjointUniq` comparison whose conjugate is the inverse derived pullback compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).
-/
noncomputable def normalizedOpenCompositor
    (A : Type u) [CommRing A] [Finite A]
    {U V Z : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    openExtension (A := A) j₁ ⋙ openExtension (A := A) j₂ ≅
      openExtension (A := A) (j₁ ≫ j₂) :=
  let a₁ := Scheme.proEtaleRingDerivedOpenAdjunction j₁
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j₁ A)
  let a₂ := Scheme.proEtaleRingDerivedOpenAdjunction j₂
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing V A)
    (Scheme.proEtaleConstantRingComparison j₂ A)
  let a₁₂ := Scheme.proEtaleRingDerivedOpenAdjunction (j₁ ≫ j₂)
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison (j₁ ≫ j₂) A)
  ((a₁.comp a₂).ofNatIsoRight (by
    simpa only [proEtaleConstantRingDerivedPullback] using
      proEtaleConstantRingPullbackComposition j₁ j₂ A)).leftAdjointUniq a₁₂

/-- The intrinsic and normalized open compositors satisfy both unitor laws.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).

The first two equations use `sfIntrinsicDerivedOpenId`; the last two use the
left-adjoint identity comparison `ιJ`, and all composite maps are transported
along the displayed `id_comp` or `comp_id` equality.

Proof (node Steps 3-4): the `c^!` unitors hold because both sides send a section `s`
to its 03DI unit image `[s]`, and a map out of `j_!` is fixed by that unit equation
(lem-weil-pbc-conjugate-iso-unit-equation). The `c^J` unitors are the conjugates, under
def-weil-pbc-composite-adjunction and def-weil-pbc-adjunction-conjugate, of the unitors of
the derived pullback compositor of lem-weil-pbc-proetale-derived-pullback-composition
with the unit-section identity `proEtaleGlobalEvaluationPullbackId`; equivalently they
follow from the `c^!` unitors, the identity companion and the r-equation.
-/
theorem proEtale_open_coefficient_r_compositor_unitors
    (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    let cA₁ := (sfIntrinsicDerivedOpenComp A (𝟙 U) j).symm
    let cA₂ := (sfIntrinsicDerivedOpenComp A j (𝟙 V)).symm
    let aIdU := Scheme.proEtaleRingDerivedOpenAdjunction (𝟙 U)
      (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U A)
      (Scheme.proEtaleConstantRingComparison (𝟙 U) A)
    let aIdV := Scheme.proEtaleRingDerivedOpenAdjunction (𝟙 V)
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V A)
      (Scheme.proEtaleConstantRingComparison (𝟙 V) A)
    let aJ := Scheme.proEtaleRingDerivedOpenAdjunction j
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing U A)
      (Scheme.proEtaleConstantRingComparison j A)
    let cJ₁ := normalizedOpenCompositor A (𝟙 U) j
    let cJ₂ := normalizedOpenCompositor A j (𝟙 V)
    let ιU := (aIdU.ofNatIsoRight (proEtaleGlobalEvaluationPullbackId A U)).leftAdjointUniq
      Adjunction.id
    let ιV := (aIdV.ofNatIsoRight (proEtaleGlobalEvaluationPullbackId A V)).leftAdjointUniq
      Adjunction.id
    (cA₁.hom ≫ (eqToIso (by
        cases Category.id_comp j
        rfl)).hom =
        (Functor.isoWhiskerRight (sfIntrinsicDerivedOpenId A U)
          (sfIntrinsicDerivedOpen A j)).hom ≫
          (Functor.leftUnitor (sfIntrinsicDerivedOpen A j)).hom) ∧
      (cA₂.hom ≫ (eqToIso (by
        cases Category.comp_id j
        rfl)).hom =
        (Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen A j)
          (sfIntrinsicDerivedOpenId A V)).hom ≫
          (Functor.rightUnitor (sfIntrinsicDerivedOpen A j)).hom) ∧
      (cJ₁.hom ≫
          (eqToIso (by
            cases Category.id_comp j
            rfl)).hom =
        (Functor.isoWhiskerRight ιU (openExtension (A := A) j)).hom ≫
          (Functor.leftUnitor (openExtension (A := A) j)).hom) ∧
      (cJ₂.hom ≫
          (eqToIso (by
            cases Category.comp_id j
            rfl)).hom =
        (Functor.isoWhiskerLeft (openExtension (A := A) j) ιV).hom ≫
        (Functor.rightUnitor (openExtension (A := A) j)).hom) := by
  sorry

/-- Associativity of the intrinsic and normalized open compositors.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-proetale-open-coefficient-r-compositor).

The two bracketings are compared by the functor associator and by the explicit
`eqToIso` induced by `Category.assoc`; the normalized maps are the
`leftAdjointUniq` comparisons of the corresponding composite adjunctions.

Proof (node Steps 3-4): for three opens both bracketings of `c^!` are the unique maps
`j_{3!}j_{2!}j_{1!} → (j_3j_2j_1)_!` with the unit equation `[[[s]]] ↦ [s]`, hence equal
(Step 3). The r-equation of `proEtale_open_coefficient_r_compositor` gives
`c^J = r_{j_2j_1} c^! (r_{j_2} j_{1!})⁻¹ (J_{j_2} r_{j_1})⁻¹`; substituting this in both
bracketings and moving the invertible `r` by naturality and the interchange law reduces
associativity of `c^J` to that of `c^!` (Step 4).
-/
theorem proEtale_open_coefficient_r_compositor_associativity
    (A : Type u) [CommRing A] [Finite A]
    {W U V Z : Scheme.{u}} (j₁ : W ⟶ U) (j₂ : U ⟶ V) (j₃ : V ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃] :
    let F₁ := sfIntrinsicDerivedOpen A j₁
    let F₂ := sfIntrinsicDerivedOpen A j₂
    let F₃ := sfIntrinsicDerivedOpen A j₃
    let cA₁₂ := (sfIntrinsicDerivedOpenComp A j₁ j₂).symm
    let cA₂₃ := (sfIntrinsicDerivedOpenComp A j₂ j₃).symm
    let cA₁₂₃ := (sfIntrinsicDerivedOpenComp A (j₁ ≫ j₂) j₃).symm
    let cA₁₂₃' := (sfIntrinsicDerivedOpenComp A j₁ (j₂ ≫ j₃)).symm
    let cJ₁₂ := normalizedOpenCompositor A j₁ j₂
    let cJ₂₃ := normalizedOpenCompositor A j₂ j₃
    let cJ₁₂₃ := normalizedOpenCompositor A (j₁ ≫ j₂) j₃
    let cJ₁₂₃' := normalizedOpenCompositor A j₁ (j₂ ≫ j₃)
    ((Functor.isoWhiskerRight cA₁₂ F₃).hom ≫ cA₁₂₃.hom =
        (Functor.associator F₁ F₂ F₃).hom ≫
          (Functor.isoWhiskerLeft F₁ cA₂₃).hom ≫ cA₁₂₃'.hom ≫
          (eqToIso (by
            cases Category.assoc j₁ j₂ j₃
            rfl)).inv) ∧
      ((Functor.isoWhiskerRight cJ₁₂ (openExtension (A := A) j₃)).hom ≫
          cJ₁₂₃.hom =
        (Functor.associator (openExtension (A := A) j₁)
          (openExtension (A := A) j₂) (openExtension (A := A) j₃)).hom ≫
          (Functor.isoWhiskerLeft (openExtension (A := A) j₁) cJ₂₃).hom ≫
          cJ₁₂₃'.hom ≫
          (eqToIso (by
            cases Category.assoc j₁ j₂ j₃
            rfl)).inv) := by
  sorry

end AlgebraicGeometry.ProEtale
