/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Sheaf.AlgebraicTopology.TrivialKanFibration

/-!
# Polynomial extension of an augmented simplicial resolution

Source: Stacks Project, cotangent.tex, Tags 08QV (last paragraph) and 08QI;
simplicial.tex, Tag 08P1
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan).

The helpers assemble Mathlib's polynomial coefficient maps, augmented whiskering,
and alternating-face augmentation. All have explicit data. The target algebra is
`P.right`, so its structure map from `A` is part of the augmented algebra data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite Simplicial

namespace AlgebraicTopology.PolynomialResolutionExtension

/-- Adjoin the variables `E`, fixing them on every algebra morphism.
Source: Stacks, Tag 08QV, last paragraph
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan). -/
def polynomialFunctor (A : Type u) [CommRing A] (E : Type w) :
    CommAlgCat.{v} A ⥤ CommAlgCat.{max v w} A where
  obj R := CommAlgCat.of A (MvPolynomial E R)
  map f := CommAlgCat.ofHom (MvPolynomial.mapAlgHom f.hom)
  map_id R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro p
    exact MvPolynomial.map_id p
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro p
    exact (MvPolynomial.map_map f.hom.toRingHom g.hom.toRingHom p).symm

/-- Polynomial extension of the entire augmented simplicial algebra, including
its augmentation. All operators act on coefficients and fix every variable.
Source: Stacks, Tag 08QV, last paragraph
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan). -/
def polynomialExtension {A : Type u} [CommRing A]
    (P : SimplicialObject.Augmented (CommAlgCat.{v} A)) (E : Type w) :
    SimplicialObject.Augmented (CommAlgCat.{max v w} A) :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (polynomialFunctor A E)).obj P

/-- The additive augmentation, reindexed by `n ↦ -n` and extended by zero in
positive cochain degrees. Its target is the target algebra in degree zero.
Source: Stacks, Tag 08QI; simplicial.tex, Tag 019A
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan). -/
def additiveAugmentation {A : Type u} [CommRing A]
    (P : SimplicialObject.Augmented (CommAlgCat.{v} A)) :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ _
        (forget₂ (CommAlgCat.{v} A) CommRingCat ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj P))
    ComplexShape.embeddingDownNat

/-- The augmentation on underlying simplicial sets, with constant target.
Source: Stacks, Tag 08QI
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan). -/
def underlyingAugmentation {A : Type u} [CommRing A]
    (P : SimplicialObject.Augmented (CommAlgCat.{v} A)) :=
  ((SimplicialObject.Augmented.whiskeringObj _ _ (forget (CommAlgCat.{v} A))).obj P).hom

/-- Adjoining any set of variables preserves degreewise surjectivity and the
additive quasi-isomorphism, and both augmentations are trivial Kan fibrations.
No polynomiality condition is imposed on the original terms.

Source: Stacks, cotangent.tex, Tag 08QV, last paragraph, and Tag 08QI;
simplicial.tex, Tag 08P1
(blueprint: lem-trf-polynomial-resolution-extension-trivial-kan).

Proof:
1. By def-weil-pbc-mv-polynomial-ring each polynomial has finitely many monomial
   coefficients. Operators and augmentations apply the corresponding coefficient
   maps and fix variables. Lift those finitely many coefficients using degreewise
   surjectivity to prove surjectivity of the polynomial augmentation, also at zero.
2. A negative-degree polynomial cycle has cycle coefficients. The assumed
   quasi-isomorphism gives a primitive for each of its finitely many coefficients.
   Their polynomial sum is a primitive. Positive terms are zero by extension.
3. In degree zero, surjectivity follows from step 1. An element in the augmentation
   kernel has all coefficients in the original augmentation kernel. The assumed
   degree-zero homology isomorphism makes each a boundary; sum finitely many
   primitives. Thus the polynomial augmentation is a quasi-isomorphism.
4. Apply lem-trf-polynomial-augmentation-boundary's general augmentation criterion,
   from Tags 08QI and 08P1, first to P and then to P[E]. The hypotheses are the
   assumptions for P and steps 1--3 for P[E]. This includes lifting vertices.
   No step uses a finite variable set or polynomial presentations of P's terms. -/
theorem polynomial_resolution_extension_trivial_kan
    {A : Type u} [CommRing A]
    (P : SimplicialObject.Augmented (CommAlgCat.{v} A)) (E : Type w)
    (h_surj : ∀ n : ℕ, Function.Surjective (P.hom.app (op ⦋n⦌)))
    (h_qis : QuasiIso (additiveAugmentation P)) :
    (∀ n : ℕ, Function.Surjective ((polynomialExtension P E).hom.app (op ⦋n⦌))) ∧
      QuasiIso (additiveAugmentation (polynomialExtension P E)) ∧
      SSet.Enhanced.trivialKanFibration (underlyingAugmentation P) ∧
      SSet.Enhanced.trivialKanFibration
        (underlyingAugmentation (polynomialExtension P E)) := by
  sorry

end AlgebraicTopology.PolynomialResolutionExtension
