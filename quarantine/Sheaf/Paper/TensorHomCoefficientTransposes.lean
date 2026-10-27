/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.CoefficientGammaRepresentatives
public import Sheaf.Paper.PodHomChainCounitFormula
public import Sheaf.Paper.PodCtfPairingMaps
public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Coefficient transposes and field descent of the five-arrow Hom chain

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, coefficient-comparison and field-stage paragraphs
(blueprint: lem-sf-tensor-hom-coefficient-transposes).

The chain is the published `PodHomChain.homEquiv`. Its fourth arrow is
precomposition with the forward, compactification-normalized projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v a b
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite TensorProduct
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures.TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
  [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}

section Comparison
variable (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  (S' : SixFunctorOperationDatum D C E' n' hn') (t : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : Domain S s f c) (R' : Domain S' t f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

variable {S s S' t f c R R'}
  {TX : (PodCoefficientStage.domain S s X).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t X).FullSubcategory}
  {TY : (PodCoefficientStage.domain S s Y).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t Y).FullSubcategory}

/-- Coefficient transposition for the five-arrow chain on its full stated domains.
Source: current blueprint fix-lem-tensor-adjunction.proof.md, coefficient paragraph
(blueprint: lem-sf-tensor-hom-coefficient-transposes).

Proof, steps 1--5 of the node: (1) the specified comparisons preserve evaluations,
units and counits by lem-fix-operation-reduction. At finite quotients use
lem-coef-evaluation-transpose-coherence, without assuming its Hom comparison invertible
outside the stipulated domains; integral reduction uses lem-coef-integral-hom-reduction.
(2) For the first arrow, expand the inverse ordinary transpose as pull(z);epsilon.
Counit compatibility and naturality of the pull comparison give its square; this is
lem-amb-mate-unit-counit. (3) Uncurry the second arrow. The evaluation-transpose identity
gives the same image of evaluation after the tensor comparison. Completed tensor is
used at the integral stage. (4) Expand the inverse exceptional transpose as
support(v);mu. The exceptional counit equation and naturality give its square, again
by lem-amb-mate-unit-counit. (5) The retained projection equation is exactly the fourth
square, with precomposition by forward PF. Uncurry the two fifth-arrow expressions;
the target evaluation equation identifies them, and injectivity of curry gives their
equality. Paste these five squares to obtain precisely alpha_A and alpha_B above. -/
theorem coefficient_square (d : Comparison S s S' t f c R R' TX TY) :
    Square d := by
  sorry
/-- Pasting any subsequent coefficient change gives the two-step square with the
literal composite endpoint comparisons. Thus a direct change with the specified
endpoint cocycle gives the same square. This includes identity changes and quotient
reductions following integral reduction.
Source: successive-change clause (blueprint: lem-sf-tensor-hom-coefficient-transposes).

Proof, node step 6: apply coefficient_square twice and functoriality to its first
equality, then substitute the second. The endpoint composites are the specified
cocycles: tensor reassociation multiplies coefficients associatively;
lem-fix-scalar-completion-associator and lem-pur-integral-operations-scalar-extension
supply completed associators; lem-fix-compact-support-coefficient-change supplies
quotient compatibility; lem-weil-pbc-mate-pasting supplies right-adjoint cocycles.
Evaluation transposes satisfy the composite and identity laws of
lem-coef-evaluation-transpose-coherence. Hence these composite coordinates are the
direct-change coordinates, with no assertion that reduction detects arbitrary maps. -/
theorem successive_square
    {E'' : Type u} [Field E''] [Algebra (Padic C.l) E'']
    [FiniteDimensional (Padic C.l) E''] {n'' : ℕ} {hn'' : 1 ≤ n''}
    (S'' : SixFunctorOperationDatum D C E'' n'' hn'') (r : PodCoefficientStage)
    (R'' : Domain S'' r f c)
    (UX : (PodCoefficientStage.domain S' t X).FullSubcategory ⥤
      (PodCoefficientStage.domain S'' r X).FullSubcategory)
    (UY : (PodCoefficientStage.domain S' t Y).FullSubcategory ⥤
      (PodCoefficientStage.domain S'' r Y).FullSubcategory)
    (d : Comparison S s S' t f c R R' TX TY)
    (e : Comparison S' t S'' r f c R' R'' UX UY)
    (direct : Comparison S s S'' r f c R R'' (TX ⋙ UX) (TY ⋙ UY))
    (_ordinary : ∀ Q, direct.ordinary.right.hom.app Q =
      UY.map (d.ordinary.right.hom.app Q) ≫ e.ordinary.right.hom.app (TX.obj Q))
    (_exceptional : ∀ Q, direct.exceptional.right.hom.app Q =
      UX.map (d.exceptional.right.hom.app Q) ≫ e.exceptional.right.hom.app (TY.obj Q))
    (_homX : ∀ M Q, (direct.tensorX M).right.app Q =
      UX.map ((d.tensorX M).right.app Q) ≫
        (e.tensorX (TX.obj M)).right.app (TX.obj Q))
    (_homY : ∀ M Q, (direct.tensorY M).right.app Q =
      UY.map ((d.tensorY M).right.app Q) ≫
        (e.tensorY (TX.obj M)).right.app (TY.obj Q)) :
    (∀ M N, direct.source M N =
      UY.map (d.source M N) ≫ e.source (TX.obj M) (TY.obj N)) ∧
    (∀ M N, direct.target M N =
      UY.map (d.target M N) ≫ e.target (TX.obj M) (TY.obj N)) ∧
    Square direct := by
  sorry
end Comparison

/-- The coefficient square specialized to precisely the finite quotient, integral
reduction and completed integral scalar extensions of the node. Realizations pin TX
and TY to actual derived extension along a; these are not unconstrained functors.
Source: displayed coefficient square
(blueprint: lem-sf-tensor-hom-coefficient-transposes).

Proof: the permitted map is one of the three specified coefficient constructions.
The two realization isomorphisms identify its restriction with the actual derived
coefficient functor. The recorded operation comparisons preserve their units,
counits and canonical evaluations. Apply the five-square calculation in
coefficient_square to those comparisons. Finite Tor and the supplied full domains
are the only restrictions on the inputs; no site-perfectness hypothesis is used.
The extra admissibility is precisely the node's optional ambient hypothesis. -/
theorem tensorHomCoefficientTransposes
    (S : SixFunctorOperationDatum D C E n hn) (i : Bool)
    (S' : SixFunctorOperationDatum D C E' n' hn') (j : Bool)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (_hadm : Admissible S (ringStage i) f c)
    (R : Domain S (ringStage i) f c) (R' : Domain S' (ringStage j) f c)
    (a : PurCompactSupport.Change (coefficients S i) (coefficients S' j))
    (_ha : Permitted S i S' j a)
    (TX : (PodCoefficientStage.domain S (ringStage i) X).FullSubcategory ⥤
      (PodCoefficientStage.domain S' (ringStage j) X).FullSubcategory)
    (TY : (PodCoefficientStage.domain S (ringStage i) Y).FullSubcategory ⥤
      (PodCoefficientStage.domain S' (ringStage j) Y).FullSubcategory)
    (_hX : TX ⋙ inclusion S' j X ≅ inclusion S i X ⋙ pbcDerivedExtend (a.map X.obj.left))
    (_hY : TY ⋙ inclusion S' j Y ≅ inclusion S i Y ⋙ pbcDerivedExtend (a.map Y.obj.left))
    (d : Comparison S (ringStage i) S' (ringStage j) f c R R' TX TY)
    (_hA : ∀ M N, IsIso (d.source M N)) (_hB : ∀ M N, IsIso (d.target M N)) :
    Square d := by
  exact coefficient_square d

private theorem baseChange_postcompose
    {A : Type*} [Category* A] [Preadditive A]
    {K : Type*} [CommRing K] [Linear K A] (p : K)
    {L U V : A} (g : (L ⟶ U) ≃ₗ[K] (L ⟶ V)) (b : U ⟶ V)
    (hg : ∀ z, g z = z ≫ b) (z : Localization.Away p ⊗[K] (L ⟶ U)) :
    (g.baseChange K (Localization.Away p) _ _) z =
      ScalarLocalization.composition K A p L U V (1 ⊗ₜ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c z =>
    rw [LinearEquiv.baseChange_tmul, hg, ScalarLocalization.composition_tmul, one_mul]
  | add z w hz hw => simp only [map_add, hz, hw]

section Localization
variable (S : SixFunctorOperationDatum D C E n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : Domain S .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

private theorem integralHomEquiv_postcompose
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N L : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (z : L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) :
    integralHomEquiv S f c R M N L z = z ≫ (integralGammaIso S f c R M N).hom.hom := by
  let q : L ⟶ (PodHomChain.sourceFunctor S .integral f c R M).obj N := ⟨z⟩
  have h := (PodHomChain.counit_formula S .integral f c R M).2.1 N _ L q (𝟙 _)
  change (PodHomChain.homEquiv S .integral f c R M N L
    (((PodCoefficientStage.domain S .integral Y).fullyFaithfulι.homEquiv
      (X := L) (Y := (PodHomChain.sourceFunctor S .integral f c R M).obj N)).symm z)).hom = _
  have hq : ((PodCoefficientStage.domain S .integral Y).fullyFaithfulι.homEquiv
      (X := L) (Y := (PodHomChain.sourceFunctor S .integral f c R M).obj N)).symm z =
      q := rfl
  rw [hq]
  simpa only [Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
    integralGammaIso] using congrArg (fun a => a.hom) h

/-- Integral linearity, including additivity, and the E-linear localized bijection
with its prescribed pure-tensor formula. The tensor order is scalar first, as in the
recorded raw localization; its Hom-first coordinates are sfRationalHomCoordinates.
Source: localization paragraph (blueprint: lem-sf-tensor-hom-coefficient-transposes).

Proof, node step 7: test-object naturality identifies the chain with postcomposition
by integralGammaIso.hom. Linear.homCongr for this isomorphism is the required integral
linear equivalence. Base change gives the localized and E-linear equivalences; its
defining pure-tensor formula gives both asserted formulas. No Karoubi completion is
taken. -/
theorem localized_bijection
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N L : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    ∃ g : (L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) ≃ₗ[
        Padic.coefficientExtensionIntegers C.l E]
      (L.obj ⟶ ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj),
      (∀ z, g z = integralHomEquiv S f c R M N L z) ∧
      ∃ q : ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L.obj ⟶
          (sfRationalConstructibleLocalization C.l E Y.obj.left).obj
            ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) ≃ₗ[
          Localization.Away (Padic.coefficientExtensionUniformizer C.l E)]
        ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj L.obj ⟶
          (sfRationalConstructibleLocalization C.l E Y.obj.left).obj
            ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj),
        (∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer C.l E))
          (z : L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj),
          q (a ⊗ₜ z) = a ⊗ₜ g z) ∧
        ∃ qE : (E ⊗[Padic.coefficientExtensionIntegers C.l E]
            (L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj)) ≃ₗ[E]
          (E ⊗[Padic.coefficientExtensionIntegers C.l E]
            (L.obj ⟶ ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj)),
          ∀ z e, qE (e ⊗ₜ z) = e ⊗ₜ g z := by
  let g := Linear.homCongr (Padic.coefficientExtensionIntegers C.l E) (Iso.refl L.obj)
    ((PodCoefficientStage.domain S .integral Y).ι.mapIso (integralGammaIso S f c R M N))
  refine ⟨g, ?_, g.baseChange _ _ _ _, ?_, g.baseChange _ E _ _, ?_⟩
  · intro z
    simpa [g, Linear.homCongr_apply] using
      (integralHomEquiv_postcompose S f c R M N L z).symm
  · intro a z
    rfl
  · intro z e
    rfl
/-- A representing inverse pair survives raw localization and represents the localized
chain on every fractional arrow, including its inverse.
Source: inverse-pair clause (blueprint: lem-sf-tensor-hom-coefficient-transposes).

Proof, node step 7: functoriality carries both inverse equations to the rational
category. The postcomposition formulas hold on a tensor with one by the integral
representing property. Bilinearity extends them to arbitrary scalar multiples and
sums of pure tensors. Apply the same argument to the inverse chain. -/
theorem localized_representatives
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (a : (PodHomChain.targetFunctor S .integral f c R M).obj N ⟶
      (PodHomChain.sourceFunctor S .integral f c R M).obj N)
    (b : (PodHomChain.sourceFunctor S .integral f c R M).obj N ⟶
      (PodHomChain.targetFunctor S .integral f c R M).obj N)
    (hab : a ≫ b = 𝟙 _) (hba : b ≫ a = 𝟙 _)
    (hb : ∀ (L : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
      (z : L ⟶ (PodHomChain.sourceFunctor S .integral f c R M).obj N),
      PodHomChain.homEquiv S .integral f c R M N L z = z ≫ b) :
    (sfRationalConstructibleLocalization C.l E Y.obj.left).map a.hom ≫
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map b.hom = 𝟙 _ ∧
    (sfRationalConstructibleLocalization C.l E Y.obj.left).map b.hom ≫
        (sfRationalConstructibleLocalization C.l E Y.obj.left).map a.hom = 𝟙 _ ∧
    ∀ (L : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
      (g : (L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) ≃ₗ[
        Padic.coefficientExtensionIntegers C.l E]
        (L.obj ⟶ ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj)),
      (∀ z, g z = integralHomEquiv S f c R M N L z) →
      (∀ z : (sfRationalConstructibleLocalization C.l E Y.obj.left).obj L.obj ⟶
          (sfRationalConstructibleLocalization C.l E Y.obj.left).obj
            ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj,
        HEq (g.baseChange _ (Localization.Away
          (Padic.coefficientExtensionUniformizer C.l E)) _ _ z)
          (z ≫ (sfRationalConstructibleLocalization C.l E Y.obj.left).map b.hom)) ∧
      (∀ z : (sfRationalConstructibleLocalization C.l E Y.obj.left).obj L.obj ⟶
          (sfRationalConstructibleLocalization C.l E Y.obj.left).obj
            ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj,
        HEq ((g.baseChange _ (Localization.Away
          (Padic.coefficientExtensionUniformizer C.l E)) _ _).symm z)
          (z ≫ (sfRationalConstructibleLocalization C.l E Y.obj.left).map a.hom)) := by
  let Q := sfRationalConstructibleLocalization C.l E Y.obj.left
  have hab' : a.hom ≫ b.hom = 𝟙 _ := congrArg (fun z => z.hom) hab
  have hba' : b.hom ≫ a.hom = 𝟙 _ := congrArg (fun z => z.hom) hba
  refine ⟨?_, ?_, ?_⟩
  · rw [← Q.map_comp, hab', Q.map_id]
  · rw [← Q.map_comp, hba', Q.map_id]
  · intro L g hg
    have hb' (z : L.obj ⟶
        ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) :
        g z = z ≫ b.hom := by
      rw [hg]
      exact congrArg (fun z => z.hom) (hb L ⟨z⟩)
    have ha' (z : L.obj ⟶
        ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj) :
        g.symm z = z ≫ a.hom := by
      apply g.injective
      rw [g.apply_symm_apply, hb', Category.assoc, hab', Category.comp_id]
    constructor
    · intro z
      exact heq_of_eq (baseChange_postcompose _ g b.hom hb' z)
    · intro z
      have h := baseChange_postcompose (Padic.coefficientExtensionUniformizer C.l E)
        g.symm a.hom ha' z
      rw [LinearEquiv.baseChange_symm] at h
      exact heq_of_eq h
/-- The explicit rational map agrees with the linear localization of the five-arrow
chain on every pure tensor, hence on all arrows; it retains the inverse formula.
Source: node step 7 (blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: naturality of the chain in the test object gives postcomposition by Gamma(1_A).
Raw localization sends this representative to rationalGammaIso.hom. Bilinearity
therefore gives the displayed formula. Pure tensors generate the localized Hom and
both maps are linear, so this identifies the whole localized bijection. -/
theorem rationalGamma_formula
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N L : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer C.l E))
    (z : L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) :
    rationalGamma S f c R M N ((rationalization S Y).obj L) (a ⊗ₜ z) =
      a ⊗ₜ integralHomEquiv S f c R M N L z := by
  rw [integralHomEquiv_postcompose S f c R M N L z]
  unfold rationalGamma
  erw [Iso.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp]
  change ScalarLocalization.composition _ _ _ _ _ _
    (1 ⊗ₜ (integralGammaIso S f c R M N).hom.hom) (a ⊗ₜ z) = _
  rw [ScalarLocalization.composition_tmul, one_mul]
  rfl

end Localization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonGamma commonGammaIso stageGamma

section CommonChain
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (F : Index C.l C.Qbar)
  (SF : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar F) n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (RF : Domain SF .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
  (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory)

/-- The localized Gamma family commutes with enlargement and descends uniquely.
Source: common-stage clause, step 8
(blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: rationalGamma_formula identifies the family with localized integral Gamma.
Expand transport and use naturality of the scalar associator and its cocycle to
obtain compatibility. The representative criterion gives field/representative
independence. The inverse family gives an inverse, and the formula on every
representative gives uniqueness. Addition is checked at the common field. -/
theorem common_stage_bijection (L : Pair C.l C.Qbar Y.obj.left) :
    (∀ (G H : CommonTriple C.l C.Qbar Y.obj.left L
        (commonSource F SF f c RF M N) (commonTarget F SF f c RF M N))
      (hGH : G ≤ H) (z : SourceHom C.l C.Qbar Y.obj.left G),
      stageGamma F SF f c RF M N L H
        (transport L (commonSource F SF f c RF M N)
          ⟨G.val, G.property.1, G.property.2.1⟩
          ⟨H.val, H.property.1, H.property.2.1⟩ hGH z) =
      transport L (commonTarget F SF f c RF M N)
        ⟨G.val, G.property.1, G.property.2.2⟩
        ⟨H.val, H.property.1, H.property.2.2⟩ hGH
          (stageGamma F SF f c RF M N L G z)) ∧
    ∃! e : (L ⟶ commonSource F SF f c RF M N) ≃+
        (L ⟶ commonTarget F SF f c RF M N),
      (∀ z, e z = commonGamma F SF f c RF M N L z) ∧
      ∀ (G : CommonTriple C.l C.Qbar Y.obj.left L
        (commonSource F SF f c RF M N) (commonTarget F SF f c RF M N))
        (z : SourceHom C.l C.Qbar Y.obj.left G),
        e (ofHom L (commonSource F SF f c RF M N)
          G.val G.property.1 G.property.2.1 z) =
        ofHom L (commonTarget F SF f c RF M N) G.val G.property.1 G.property.2.2
          (stageGamma F SF f c RF M N L G z) := by
  sorry

/-- A supplied integral inverse pair representing Gamma represents this SAME common
Gamma, and its images remain inverse. Source: inverse-pair clause, steps 7--8
(blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: evaluate the representing equation at identity to identify b with Gamma(1_A).
The inverse equations fix a as its inverse. Localize and include both identities.
The definition of commonGamma then gives both postcomposition formulas. -/
theorem common_stage_representatives
    (a : (PodHomChain.targetFunctor SF .integral f c RF M).obj N ⟶
      (PodHomChain.sourceFunctor SF .integral f c RF M).obj N)
    (b : (PodHomChain.sourceFunctor SF .integral f c RF M).obj N ⟶
      (PodHomChain.targetFunctor SF .integral f c RF M).obj N)
    (hab : a ≫ b = 𝟙 _) (hba : b ≫ a = 𝟙 _)
    (hb : ∀ (L : (PodCoefficientStage.domain SF .integral Y).FullSubcategory)
      (z : L ⟶ (PodHomChain.sourceFunctor SF .integral f c RF M).obj N),
      PodHomChain.homEquiv SF .integral f c RF M N L z = z ≫ b) :
    ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map a ≫
        ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map b =
      𝟙 _ ∧
    ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map b ≫
        ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map a =
      𝟙 _ ∧
    ∀ L : Pair C.l C.Qbar Y.obj.left,
      (∀ z : L ⟶ commonSource F SF f c RF M N,
        commonGamma F SF f c RF M N L z = z ≫
          ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map b) ∧
      (∀ z : L ⟶ commonTarget F SF f c RF M N,
        (commonGamma F SF f c RF M N L).symm z = z ≫
          ((rationalization SF Y) ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F).map a) := by
  sorry

/-- The common-stage Gamma and its inverse are postcomposition with the fixed
localized representatives, and agree with the fieldwise family on every representative.
Source: step 8 (blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: apply the definition of commonGamma and its inverse. Include a finite-stage
representative and use the scalar associator to obtain the final formula. The
common-stage equality criterion makes this independent of field enlargement. -/
theorem common_stage_postcomposition (L : Pair C.l C.Qbar Y.obj.left) :
    (∀ z : L ⟶ commonSource F SF f c RF M N,
      commonGamma F SF f c RF M N L z = z ≫ (commonGammaIso F SF f c RF M N).hom) ∧
    (∀ z : L ⟶ commonTarget F SF f c RF M N,
      (commonGamma F SF f c RF M N L).symm z = z ≫
        (commonGammaIso F SF f c RF M N).inv) ∧
    ∀ (G : CommonTriple C.l C.Qbar Y.obj.left L
      (commonSource F SF f c RF M N) (commonTarget F SF f c RF M N))
      (z : SourceHom C.l C.Qbar Y.obj.left G),
      commonGamma F SF f c RF M N L
        (ofHom L (commonSource F SF f c RF M N) G.val G.property.1 G.property.2.1 z) =
      ofHom L (commonTarget F SF f c RF M N) G.val G.property.1 G.property.2.2
        (stageGamma F SF f c RF M N L G z) := by
  sorry

/-- Actual rational and common Gamma satisfy naturality in N and composition with
all test arrows, including fractional arrows and arbitrary common-stage objects.
Source: final sentence, steps 7--8
(blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: naturality of the five specified arrows proves the integral equation.
Use rationalGamma_formula and bilinearity to extend it to fractions. Represent the
finitely many common arrows at one field and apply the rational equation there;
common_stage_bijection and the equality criterion give the common equation. -/
theorem equations_pass_to_fields
    (N' : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) (r : N ⟶ N') :
    (∀ (L K : sfRationalConstructibleCategory C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left) (t : K ⟶ L)
      (z : L ⟶ (rationalization SF Y).obj
        ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N)),
      rationalGamma SF f c RF M N' K
        (t ≫ z ≫ (rationalization SF Y).map
          ((PodHomChain.sourceFunctor SF .integral f c RF M).map r)) =
      t ≫ rationalGamma SF f c RF M N L z ≫ (rationalization SF Y).map
        ((PodHomChain.targetFunctor SF .integral f c RF M).map r)) ∧
    ∀ (L K : Pair C.l C.Qbar Y.obj.left) (t : K ⟶ L)
      (z : L ⟶ commonSource F SF f c RF M N),
      commonGamma F SF f c RF M N' K
        (t ≫ z ≫ ((rationalization SF Y) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion F).map
            ((PodHomChain.sourceFunctor SF .integral f c RF M).map r)) =
      t ≫ commonGamma F SF f c RF M N L z ≫ ((rationalization SF Y) ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion F).map
          ((PodHomChain.targetFunctor SF .integral f c RF M).map r) := by
  sorry
/-- An integral signed-shift equation for the actual Gamma representatives remains
that equation for rational and common Gamma, with the same sign and structural maps.
Source: final sentence, steps 7--8
(blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: the rational and common representatives are the images of integralGammaIso.
Apply the two additive localization/inclusion functors to the integral equation;
functoriality gives the displayed composites. Their normalized shift comparisons
identify the image of shiftedIntegralGamma with the shifted rational/common map.
Every equation involves finitely many arrows, so common-stage independence follows
from the representative criterion. No reduction-faithfulness is asserted. -/
theorem shift_equations_pass_to_fields
    (M' : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N' : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) (r k : ℤ)
    (a : ((PodHomChain.sourceFunctor SF .integral f c RF M').obj N').obj ⟶
      (shiftFunctor (sfIntegralConstructibleCategory C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
          ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N).obj)
    (b : ((PodHomChain.targetFunctor SF .integral f c RF M').obj N').obj ⟶
      (shiftFunctor (sfIntegralConstructibleCategory C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
          ((PodHomChain.targetFunctor SF .integral f c RF M).obj N).obj)
    (h : (integralGammaIso SF f c RF M' N').hom.hom ≫ b =
      a ≫ (k • shiftedIntegralGamma F SF f c RF M N r)) :
    ShiftEquationsPassToFields F SF f c RF M N M' N' r k a b h := by
  sorry

end CommonChain

section FieldCoefficientSquare
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (F G : Index C.l C.Qbar) (hFG : F ≤ G)
  (SF : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar F) n hn)
  (SG : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar G) n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (RF : Domain SF .integral f c) (RG : Domain SG .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (TX : (PodCoefficientStage.domain SF .integral X).FullSubcategory ⥤
    (PodCoefficientStage.domain SG .integral X).FullSubcategory)
  (TY : (PodCoefficientStage.domain SF .integral Y).FullSubcategory ⥤
    (PodCoefficientStage.domain SG .integral Y).FullSubcategory)
  (d : Comparison SF .integral SG .integral f c RF RG TX TY)
  (rY : TY ⋙ rationalization SG Y ≅ rationalization SF Y ⋙
    stageTransition C.l C.Qbar Y.obj.left F G hFG)

/-- The actual rational Gamma coefficient square holds for every fractional arrow;
the actual common Gamma coefficient square holds for every common-stage arrow.
The common endpoint identifications are the normalized transIso for F≤G.
Source: final coefficient/field clauses, steps 7--8
(blueprint: lem-sf-tensor-hom-coefficient-transposes).
Proof: localize coefficient_square on integral representatives. The normalization rY
identifies both endpoint maps with the displayed rational comparisons. The pure-tensor
formula rationalGamma_formula and semilinearity extend the equality to all fractional
arrows. Include at G and use naturality of transIso. Represent any common arrow over
a larger common field; the same rational equation there and the representative
criterion prove the second square. This proves compatibility with recalculating the
actual changed chain at G, not merely with transporting a fixed representative. -/
theorem field_coefficient_square
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :
    FieldCoefficientSquare F G hFG SF SG f c RF RG TX TY d rY M N := by
  sorry
end FieldCoefficientSquare

end WeilConjectures.TensorHomCoefficientTransposes
