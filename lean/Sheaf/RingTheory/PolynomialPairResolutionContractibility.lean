/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.RingTheory.PolynomialPresentationPairCategories
public import Sheaf.AlgebraicTopology.TrivialKanFibration
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Sheaf.Paper.TrivialKanHomotopyEquivalence

/-!
# Contractibility of polynomial-pair resolutions

Source: Stacks Project, Cotangent Complex, Tag 08QV (`lemma-polynomial-on-top`),
and Simplicial, Tag 08NS (`lemma-trivial-kan-homotopy`)
(blueprint: lem-trf-polynomial-pair-resolution-contractibility).

The identifications with the original simplicial algebras specify the transport to small
representatives. The base-change isomorphism is characterized by its specialization square,
and the representable isomorphism by evaluation on every lower and upper generator.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory

namespace Algebra.PolynomialPresentation

/-- Forget a pair to its lower A-algebra. Source: Stacks 08QV
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def pairLowerAlgebras (I A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (E : Set I) : Pair I A B E ⥤ CommAlgCat.{u} A where
  obj W := CommAlgCat.of A (MvPolynomial W.lowerVars A)
  map f := CommAlgCat.ofHom f.lower

/-- Forget a pair to its upper ring. Source: Stacks 08QV
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def pairUpperRings (I A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (E : Set I) : Pair I A B E ⥤ CommRingCat.{u} where
  obj W := CommRingCat.of (MvPolynomial W.upperVars (MvPolynomial W.lowerVars A))
  map f := CommRingCat.ofHom f.upper

/-- Adjoin E, applying maps to coefficients and fixing variables. Source: Stacks 08QV
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionPolynomialRings (A : Type u) [CommRing A] (E : Type u) :
    CommAlgCat.{u} A ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of (MvPolynomial E R)
  map f := CommRingCat.ofHom (MvPolynomial.map f.hom.toRingHom)
  map_id _R := CommRingCat.hom_ext (RingHom.ext MvPolynomial.map_id)
  map_comp _f _g := CommRingCat.hom_ext
    (RingHom.ext (fun p ↦ (MvPolynomial.map_map _ _ p).symm))

/-- The augmentation P[E] to constant B[E], with canonical constant-functor transport.
Source: Stacks 08QV (blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionPolynomialAugmentation {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (E : Type u) {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) :
    P ⋙ resolutionPolynomialRings A E ⋙ forget CommRingCat ⟶
      (SimplicialObject.const (Type u)).obj (MvPolynomial E B) :=
  Functor.whiskerRight ε (resolutionPolynomialRings A E ⋙ forget CommRingCat) ≫
    (Functor.constComp (J := SimplexCategoryᵒᵖ) (CommAlgCat.of A B)
      (resolutionPolynomialRings A E ⋙ forget CommRingCat)).hom

/-- The actual product of augmentation fibres over prescribed generator values.
Source: Stacks 08QV (blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionGeneratorFibres {D : Type u} {X : SSet.{u}}
    (p : X ⟶ (SimplicialObject.const (Type u)).obj D) {S : Type u} (b : S → D) :
    SSet.{u} :=
  ∏ᶜ (fun s : S ↦ pullback p
    ((SimplicialObject.const (Type u)).map (↾fun (_ : PUnit.{u + 1}) ↦ b s)))

/-- Forget the fibre equation after projecting to one generator coordinate.
Source: Stacks 08QV (blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionGeneratorProjection {D : Type u} {X : SSet.{u}}
    (p : X ⟶ (SimplicialObject.const (Type u)).obj D) {S : Type u} (b : S → D) (s : S) :
    resolutionGeneratorFibres p b ⟶ X :=
  Pi.π (fun t : S ↦ pullback p
    ((SimplicialObject.const (Type u)).map (↾fun (_ : PUnit.{u + 1}) ↦ b t))) s ≫
      pullback.fst p
        ((SimplicialObject.const (Type u)).map (↾fun (_ : PUnit.{u + 1}) ↦ b s))

/-- The lower-generator product occurring in the representable formula. Source: Stacks 08QV
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionLowerFibres {I A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Set I} {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    (W : Pair I A B E) : SSet.{u} :=
  resolutionGeneratorFibres (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))
    (fun s : W.lowerVars ↦ W.lower (MvPolynomial.X s))

/-- The upper-generator product occurring in the representable formula. Source: Stacks 08QV
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
def resolutionUpperFibres {I A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Set I} {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    (W : Pair I A B E) : SSet.{u} :=
  resolutionGeneratorFibres
    (resolutionPolynomialAugmentation E ε)
    W.upperValues

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The complete normalized conclusion of the polynomial-pair resolution lemma.
All displayed isomorphisms are actual categorical isomorphisms. `upperCoefficients` identifies
U with (P,P[E]) as a pair; naturality of `lower` and `upper` specifies every operator.
Source: Stacks 08QV and 08NS
(blueprint: lem-trf-polynomial-pair-resolution-contractibility). -/
structure PairResolutionContractibility (I A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] (E : Set I)
    (P : SimplicialObject (CommAlgCat.{u} A))
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) where
  U : SimplicialObject (Pair I A B E)
  lower : U ⋙ pairLowerAlgebras I A B E ≅ P
  lowerAugmentation : ∀ n : SimplexCategoryᵒᵖ,
    (ε.app n).hom.comp (lower.hom.app n).hom = (U.obj n).lower
  upper : U ⋙ pairUpperRings I A B E ≅ P ⋙ resolutionPolynomialRings A E
  upperCoefficients : ∀ (n : SimplexCategoryᵒᵖ) (p : MvPolynomial (U.obj n).lowerVars A),
    upper.hom.app n (MvPolynomial.C p) = MvPolynomial.C (lower.hom.app n p)
  upperAugmentation : ∀ n : SimplexCategoryᵒᵖ,
    (MvPolynomial.map (ε.app n).hom.toRingHom).comp (upper.hom.app n).hom =
      (U.obj n).augmentation
  baseChangeIso : U ⋙ baseChange I A B E ≅
    (SimplicialObject.const (Target I B E)).obj (topTarget I B E)
  baseChangeNormalization : ∀ n : SimplexCategoryᵒᵖ,
    (baseChangeIso.hom.app n).val.toRingHom.comp (U.obj n).specialize =
      (MvPolynomial.map (ε.app n).hom.toRingHom).comp (upper.hom.app n).hom
  coordinates : ∀ W : Pair I A B E,
    ∃ i : U ⋙ coyoneda.obj (op W) ≅ resolutionLowerFibres ε W ⨯ resolutionUpperFibres ε W,
      (∀ (n : SimplexCategoryᵒᵖ) (f : W ⟶ U.obj n) (s : W.lowerVars),
        ((prod.fst : resolutionLowerFibres ε W ⨯ resolutionUpperFibres ε W ⟶
            resolutionLowerFibres ε W).app n (i.hom.app n f) |>
          (resolutionGeneratorProjection
            (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))
            (fun t : W.lowerVars ↦ W.lower (MvPolynomial.X t)) s).app n) =
              lower.hom.app n (f.lower (MvPolynomial.X s))) ∧
      (∀ (n : SimplexCategoryᵒᵖ) (f : W ⟶ U.obj n) (t : W.upperVars),
        ((prod.snd : resolutionLowerFibres ε W ⨯ resolutionUpperFibres ε W ⟶
            resolutionUpperFibres ε W).app n (i.hom.app n f) |>
          (resolutionGeneratorProjection
            (resolutionPolynomialAugmentation E ε)
            W.upperValues t).app n) = upper.hom.app n (f.upper (MvPolynomial.X t)))
  trivial : ∀ W : Pair I A B E,
    SSet.Enhanced.trivialKanFibration (terminal.from (U ⋙ coyoneda.obj (op W)))
  homotopy : ∀ W : Pair I A B E,
    ∃ g : (⊤_ SSet.{u}) ⟶ U ⋙ coyoneda.obj (op W),
      g ≫ terminal.from (U ⋙ coyoneda.obj (op W)) = 𝟙 _ ∧
      ∃ h : (U ⋙ coyoneda.obj (op W)) ⊗ Δ[1] ⟶ U ⋙ coyoneda.obj (op W),
        SSet.ι₀ ≫ h = 𝟙 _ ∧
          SSet.ι₁ ≫ h = terminal.from (U ⋙ coyoneda.obj (op W)) ≫ g

/-- Polynomial-pair resolutions have contractible representable mapping simplicial sets,
for arbitrary generator sets in the common infinite bound.

Source: Stacks Project, Cotangent Complex, Tag 08QV (`lemma-polynomial-on-top`),
and Simplicial, Tag 08NS (`lemma-trivial-kan-homotopy`)
(blueprint: lem-trf-polynomial-pair-resolution-contractibility).

Proof:
1. Extend each simplicial operator on P to P[E] by applying it to coefficients and fixing
   every X_e. Polynomial uniqueness gives composition and identity and preservation of the
   augmentations (def-weil-pbc-mv-polynomial-ring, def-weil-pbc-simplicial-object).
2. Choose the bounded presentations of P_n, extend them fixing E, and conjugate operators
   by these isomorphisms. Middle inverse pairs cancel, so this is a simplicial object U in
   def-trf-polynomial-presentation-pair-categories. The isomorphisms give lower and upper,
   with the augmentation and coefficient equations (def-weil-size-convention).
3. Base change gives P_n[E] tensor_{P_n} B = B[E], fixing coefficients and variables.
   Every induced operator fixes all X_e and is B-linear, so it is identity. This supplies
   baseChangeIso with its specialization normalization.
4. Send (f,g):W to U_n to the images of all lower and upper generators, transported by
   lower and upper. Conversely polynomial evaluation constructs f first and then g over f.
   The fibre equations give augmentation preservation; polynomial uniqueness gives inverse
   maps. Operators act coordinatewise, giving coordinates and both evaluation equations.
5. Each fibre over a prescribed generator value is a trivial Kan fibration to a point:
   compose its boundary with the projection to P or P[E], lift over the constant prescribed
   value, and retain the resulting simplex in the fibre. The zero-dimensional lifting
   condition gives a vertex (def-weil-pbc-trivial-kan-fibration).
6. Choose fillers and vertices coordinatewise in the product over all lower and upper
   generators. This works for infinite sets by choice; an empty product has its unique
   tuple. Transport through coordinates proves trivial.
7. Apply lem-weil-pbc-trivial-kan-homotopy-equivalence to the map to the terminal singleton.
   Its section and cylinder homotopy supply homotopy, with the stated endpoint equations. -/
theorem polynomial_pair_resolution_contractibility
    (I A B : Type u) [Infinite I] [CommRing A] [CommRing B] [Algebra A B]
    (_boundA : Nonempty (A ↪ I)) (_boundB : Nonempty (B ↪ I)) (E : Set I)
    (P : SimplicialObject (CommAlgCat.{u} A))
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    (_polynomial : ∀ n : SimplexCategoryᵒᵖ, ∃ S : Set I,
      Nonempty (CommAlgCat.of A (MvPolynomial S A) ≅ P.obj n))
    (_hP : SSet.Enhanced.trivialKanFibration
      (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (_hPE : SSet.Enhanced.trivialKanFibration
      (resolutionPolynomialAugmentation E ε)) :
    Nonempty (PairResolutionContractibility I A B E P ε) := by
  sorry

end Algebra.PolynomialPresentation
