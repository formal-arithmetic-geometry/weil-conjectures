/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.RingTheory.PolynomialPresentationArbitraryTarget
public import Sheaf.RingTheory.CotangentLowerShriekPolynomialTop
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Polynomial base-change comma equivalence and its evaluation augmentation

Source: Stacks Project, Cotangent Complex, Tag 08QW, case i = 3, and Tag 08QV
(blueprint: lem-trf-polynomial-basechange-comma-evaluation).

The polynomial target H is written B[E] in the common bounded coordinates. C is arbitrary.
The auxiliary record expands the asserted equivalence, its coefficient identification,
its canonical derived bar comparison, and the equality of the specified augmentations.
No equivalence or augmentation is chosen from the postponed existence statement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Algebra.PolynomialPresentation

variable (I A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] (E : Set I) (δ : MvPolynomial E B →ₐ[B] C)

/-- Composition of augmentation with δ, before taking opposites. Source: Stacks 08QW,
case i = 3 (blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
def postcomposeTarget : Target I B E ⥤ ArbitraryTarget.Target I B C where
  obj T := ⟨T.vars, fun i ↦ δ (T.values i)⟩
  map {T U} f := ⟨f.val, by
    change (MvPolynomial.aeval (fun i ↦ δ (U.values i))).comp f.val =
      MvPolynomial.aeval (fun i ↦ δ (T.values i))
    rw [← MvPolynomial.comp_aeval, ← MvPolynomial.comp_aeval]
    change (δ.comp U.augmentation).comp f.val = δ.comp T.augmentation
    rw [AlgHom.comp_assoc, f.property]⟩
  map_id T := rfl
  map_comp f g := rfl

/-- V = (H → C), with H = B[E]. Source: Stacks 08QW, case i = 3
(blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
def commaTarget : ArbitraryTarget.Target I B C :=
  (postcomposeTarget I B C E δ).obj (topTarget I B E)

/-- The comma site (V ↓ u); all sites carry the identity-cover topology. Source:
Stacks 08QW, case i = 3 (blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
abbrev PolynomialComma := StructuredArrow (op (commaTarget I B C E δ))
  (ArbitraryTarget.baseChange I A B C).op

/-- F_V = p_V⁻¹u⁻¹K, functorially in K. Source: Stacks 08QW, case i = 3
(blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
def commaRestriction (R : Type u) [CommRing R] :
    ((ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      ((PolynomialComma I A B C E δ)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft _ _ _).obj
    ((StructuredArrow.proj (op (commaTarget I B C E δ))
      (ArbitraryTarget.baseChange I A B C).op ⋙
        (ArbitraryTarget.baseChange I A B C).op).op)

/-- v⁻¹G with G = j⁻¹K, retaining the original polynomial-target categories. Source:
Stacks 08QW, case i = 3 (blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
def polynomialRestriction (R : Type u) [CommRing R] :
    ((ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      ((Pair I A B E)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft _ _ _).obj
    ((baseChange I A B E).op.op ⋙ (postcomposeTarget I B C E δ).op.op)

/-- Evaluation at V, as a complex in degree zero. This is also G(H → H)[0]. Source:
Stacks 08QV and 08QW (blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
def commaEvaluation (R : Type u) [CommRing R] :
    ((ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      CochainComplex (ModuleCat.{u} R) ℤ :=
  (CategoryTheory.evaluation _ _).obj (op (op (commaTarget I B C E δ))) ⋙
    CochainComplex.singleFunctor _ 0

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All data and laws of the comma equivalence with its canonical evaluation map.
The heterogeneous equalities compare identical algebra maps in the changing coordinate
fibres; they do not replace algebra-map compatibility by arbitrary coefficient choices.
Source: Stacks 08QW, case i = 3, with 08QV and the bar model of 08PG/08PH
(blueprint: lem-trf-polynomial-basechange-comma-evaluation). -/
structure PolynomialCommaEvaluation (system : CategoryColimitBarSystem.{u}) where
  equivalence : PolynomialComma I A B C E δ ≌ (Pair I A B E)ᵒᵖ
  forwardObject : ∀ Z : PolynomialComma I A B C E δ,
    equivalence.functor.obj Z = op
      { lowerVars := Z.right.unop.lowerVars
        upperVars := Z.right.unop.upperVars
        lower := Z.right.unop.lower
        upperValues := fun i ↦ Z.hom.unop.val (MvPolynomial.X i) }
  forwardAugmentation : ∀ Z : PolynomialComma I A B C E δ,
    HEq (equivalence.functor.obj Z).unop.augmentation
      (Z.hom.unop.val.toRingHom.comp Z.right.unop.specialize)
  inverseObject : ∀ W : Pair I A B E,
    (equivalence.inverse.obj (op W)).right = op
      { lowerVars := W.lowerVars
        upperVars := W.upperVars
        lower := W.lower
        upperValues := fun i ↦ δ (W.upperValues i) }
  inverseArrow : ∀ W : Pair I A B E,
    HEq (equivalence.inverse.obj (op W)).hom.unop.val W.target.augmentation
  forwardLower : ∀ {Z Z' : PolynomialComma I A B C E δ} (f : Z ⟶ Z'),
    HEq (equivalence.functor.map f).unop.lower f.right.unop.lower
  forwardUpper : ∀ {Z Z' : PolynomialComma I A B C E δ} (f : Z ⟶ Z'),
    HEq (equivalence.functor.map f).unop.upper f.right.unop.upper
  inverseLower : ∀ {W W' : (Pair I A B E)ᵒᵖ} (f : W ⟶ W'),
    HEq (equivalence.inverse.map f).right.unop.lower f.unop.lower
  inverseUpper : ∀ {W W' : (Pair I A B E)ᵒᵖ} (f : W ⟶ W'),
    HEq (equivalence.inverse.map f).right.unop.upper f.unop.upper
  coefficient : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    (commaRestriction I A B C E δ R).obj K ≅
      equivalence.functor.op ⋙ (polynomialRestriction I A B C E δ R).obj K
  coefficientIdentity : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R)
    (Z : (PolynomialComma I A B C E δ)ᵒᵖ)
    (x : ((commaRestriction I A B C E δ R).obj K).obj Z),
    HEq ((coefficient R K).hom.app Z x) x
  comparison : ∀ (R : Type u) [CommRing R],
    commaRestriction I A B C E δ R ⋙
        (system.models (PolynomialComma I A B C E δ) R).bar ⋙ DerivedCategory.Q ≅
      polynomialRestriction I A B C E δ R ⋙
        (system.models (Pair I A B E)ᵒᵖ R).bar ⋙ DerivedCategory.Q
  represented : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    (comparison R).hom.app K = DerivedCategory.Q.map
      (system.map equivalence.functor (RingHom.id R) (coefficient R K).hom)
  commaAugmentation : ∀ (R : Type u) [CommRing R],
    commaRestriction I A B C E δ R ⋙
      (system.models (PolynomialComma I A B C E δ) R).bar ⟶ commaEvaluation I B C E δ R
  polynomialAugmentation : ∀ (R : Type u) [CommRing R],
    polynomialRestriction I A B C E δ R ⋙
      (system.models (Pair I A B E)ᵒᵖ R).bar ⟶ commaEvaluation I B C E δ R
  commaFormula : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    IsEvaluationAugmentation (system.models (PolynomialComma I A B C E δ) R)
      ((commaRestriction I A B C E δ R).obj K)
      (K.obj (op (op (commaTarget I B C E δ))))
      (fun Z ↦ K.map Z.hom.op) ((commaAugmentation R).app K)
  polynomialFormula : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    IsEvaluationAugmentation (system.models (Pair I A B E)ᵒᵖ R)
      ((polynomialRestriction I A B C E δ R).obj K)
      (K.obj (op (op (commaTarget I B C E δ))))
      (fun W ↦ K.map ((postcomposeTarget I B C E δ).map
        (toTop I B E W.unop.target)).op.op) ((polynomialAugmentation R).app K)
  augmentationCompatibility : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    (commaAugmentation R).app K =
      system.map equivalence.functor (RingHom.id R) (coefficient R K).hom ≫
        (polynomialAugmentation R).app K
  augmentationIso : ∀ (R : Type u) [CommRing R]
    (K : (ArbitraryTarget.Target I B C)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R),
    IsIso (DerivedCategory.Q.map ((commaAugmentation R).app K))

/-- The polynomial base-change comma equivalence identifies the canonical evaluation
augmentations, naturally in every module presheaf K, without polynomiality of C or flatness.
Source: Stacks 08QW, case i = 3 (correcting the printed C_{H/C} to C_{H/B}), and 08QV
(blueprint: lem-trf-polynomial-basechange-comma-evaluation).

Proof:
1. Write Q tensor_P B as B[T]. The tensor-pushout universal property
   [lem-weil-pbc-algebra-tensor-pushout-universal-property] identifies α : B[T] → H
   over C with γ : Q → H over C, by γ(q) = α(q tensor 1); conversely the induced
   map sends q tensor b to γ(q)b. This changes no polynomial variables or lower map.
2. For a compatible pair (p,q), tensor base change is h with h(q' tensor b) = q(q') tensor b.
   The comma equation α' = αh is equivalent to γ' = γq. Preserve the lower and upper maps.
   Tensor uniqueness proves the two constructions inverse, giving the displayed equivalence
   and every forward/inverse object and morphism formula.
3. The functors j v e and u p have the same algebra B[T], augmentation and maps. Their
   coefficient identification is identity on K(uU), so it is natural in K.
4. Apply [lem-trf-derived-colimit-bar] to this equivalence and identification. Its bar map
   reindexes every chain by e and retains x. The inverse equivalence gives the inverse in D(R);
   the unit and counit act by the natural-transformation homotopies in that node. The generator
   formulas commute with every coefficient map, giving the natural derived comparison.
5. For W = eZ, the arrow (H → H) → vW is opposite to α. Its image under j is exactly the
   comma arrow a. Thus the polynomial augmentation sends the image of (Z,x) to K(a)x.
   Both maps vanish off degree zero. They are equal as chain maps, with the stated factorization.
6. Apply [lem-trf-cotangent-lower-shriek-polynomial-top] to H = B[E] and G = j⁻¹K.
   Its augmentation is a derived isomorphism. Steps 4 and 5 give the same assertion for the
   comma augmentation. All formulas commute with K → K', including zero modules and rings;
   only H must be polynomial. The common infinite bound contains A, B, C and the variable sets.
-/
theorem polynomial_baseChange_comma_evaluation [Infinite I]
    (_boundA : Nonempty (A ↪ I)) (_boundB : Nonempty (B ↪ I))
    (_boundC : Nonempty (C ↪ I)) (system : CategoryColimitBarSystem.{u}) :
    Nonempty (PolynomialCommaEvaluation I A B C E δ system) := by
  sorry

end Algebra.PolynomialPresentation
