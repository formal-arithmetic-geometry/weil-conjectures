/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite bases of completed constant quotient sheaves

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59, for the inverse-limit model.
The finite-basis and cofinal-filtration refinement is the agent argument in the DAG
(blueprint: lem-pur-adic-basis-limit).

Levels of the inverse sequence are numbered by n : ℕ and have exponent n+1.
Finite products in module sheaves are the finite direct sums in the statement.
The displayed sums characterize the quotient basis maps and the completed map,
including their columns, without a choice of an unrelated isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)

/-- Ring sheafification on the small site, via Mathlib's small-model construction.
Source: def-weil-pbc-constant-sheaf (blueprint: lem-pur-adic-basis-limit). -/
instance adicBasisRingSheafify : HasSheafify J RingCat.{max uC vC r} :=
  letI : EssentiallySmall.{max uC vC r} C := essentiallySmallSelf.{r} _
  hasSheafifyEssentiallySmallSite J RingCat.{max uC vC r}

/-- The constant quotient ring sheaf at a positive exponent n+1.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
def adicBasisResidue (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1)))

/-- The actual quotient tower, with reduction induced by the identity on A.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
def adicBasisTower (A : Type (max uC vC r)) [CommRing A] (t : A) :
    ℕᵒᵖ ⥤ Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  Functor.ofOpSequence (X := fun n ↦ adicBasisResidue.{uC, vC, r} J A t n)
    (fun n ↦ (constantSheaf J RingCat.{max uC vC r}).map
      (RingCat.ofHom (Ideal.Quotient.factorPowSucc (Ideal.span {t}) (n + 1))))

/-- The limit is Mathlib's limit of ring sheaves and is computed sectionwise.
Source: Bhatt--Scholze, Lemma 6.8.2(1); def-pur-sheaf-inverse-limit
(blueprint: lem-pur-adic-basis-limit). -/
abbrev adicBasisCompletion (A : Type (max uC vC r)) [CommRing A] (t : A) :=
  limit (adicBasisTower.{uC, vC, r} J A t)

/-- The projection at positive exponent n+1.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
def adicBasisProjection (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisResidue.{uC, vC, r} J A t n :=
  limit.π (adicBasisTower.{uC, vC, r} J A t) (op n)

/-- The residue of an element as a constant section, using the sheafification unit.
Source: DAG proof, steps 1--2 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisConstant (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) (U : Cᵒᵖ)
    (a : A) : (adicBasisResidue.{uC, vC, r} J A t n).obj.obj U :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (toSheafify J ((Functor.const Cᵒᵖ).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1))))).app U
      (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1)) a)

/-- A finite direct sum of the coefficient module, represented by its finite product.
Source: DAG proof, step 5; def-weil-sheaf-of-modules-category
(blueprint: lem-pur-adic-basis-limit). -/
abbrev adicBasisFree (R : Sheaf J RingCat.{max uC vC r}) (d : ℕ) :
    ringedSiteModules.{max uC vC r} R :=
  ∏ᶜ (fun _ : Fin d ↦ SheafOfModules.unit R)

/-- Coordinate projections of the finite direct sum on sections.
Source: DAG proof, step 5 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisCoordinate (R : Sheaf J RingCat.{max uC vC r}) (d : ℕ) (U : Cᵒᵖ)
    (x : (adicBasisFree.{uC, vC, r} J R d).val.obj U) (i : Fin d) : R.obj.obj U :=
  (Pi.π (fun _ : Fin d ↦ SheafOfModules.unit R) i).val.app U x

variable {A B : Type r} [CommRing A] [CommRing B] [Algebra A B]

/-- The two ideal inclusions needed for the same-level and cofinal quotient maps.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit).
Proof: t^n maps to u^n v^(en), so t^n B = v^(en) B because u^n is a unit.
Since en ≥ n, this ideal is contained in v^n B. Taking inverse images gives
both displayed inclusions at the positive exponent n+1. The subtraction in the
second exponent merely converts its positive exponent to a natural-number level. -/
theorem adicBasis_ideal_bounds (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    (Ideal.span {t}) ^ (n + 1) ≤
        ((Ideal.span {v}) ^ (n + 1)).comap (algebraMap A B) ∧
      (Ideal.span {t}) ^ (n + 1) ≤
        ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)).comap (algebraMap A B) := by
  sorry

variable {A B : Type (max uC vC r)} [CommRing A] [CommRing B] [Algebra A B]

/-- The canonical quotient map A/t^(n+1) -> B/v^(n+1).
Its underlying ring map is induced by the given algebra map.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisScalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    adicBasisResidue.{uC, vC, r} J A t n ⟶ adicBasisResidue.{uC, vC, r} J B v n :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom
    (Ideal.quotientMap ((Ideal.span {v}) ^ (n + 1)) (algebraMap A B)
      (adicBasis_ideal_bounds.{max uC vC r} t v a e he ht n).1))

/-- The quotient map at exponents n+1 and e(n+1), using t^(n+1)B=v^(e(n+1))B.
Natural-number level e(n+1)-1 denotes positive exponent e(n+1).
Source: DAG proof, steps 3--4 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisCofinalScalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    adicBasisResidue.{uC, vC, r} J A t n ⟶ adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1) :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom
    (Ideal.quotientMap ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)) (algebraMap A B)
      (adicBasis_ideal_bounds.{max uC vC r} t v a e he ht n).2))

/-- The normalization characterizing the ring map of completions.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit). -/
def AdicBasisScalarCondition (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v) : Prop :=
  ∀ n : ℕ, f ≫ adicBasisProjection.{uC, vC, r} J B v n =
    adicBasisProjection.{uC, vC, r} J A t n ≫ adicBasisScalar.{uC, vC, r} J t v a e he ht n

/-- Finite bases pass to completed constant quotient sheaves, with their specified
columns and their cofinal projection factorization.

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59, for the inverse-limit model;
finite-basis/cofinal-filtration refinement: DAG agent argument
(blueprint: lem-pur-adic-basis-limit).

Proof: (1) The basis map A^d -> B descends modulo t^n, with inverse given by
reducing the coordinate maps. Both commute with reductions, including d=0.
(2) Constant presheaves and sheafification carry these maps to quotient basis
isomorphisms, since sheafification preserves finite products
(lem-weil-pbc-sheafification-exact). The module-sheafification universal property
(lem-pc-sites-module-sheafification-interface) and its underlying-set comparison
(lem-pc-sites-sheafification-underlying-sets) identify the target with the ring sheaf.
(3) The ideal identities t^n B=v^(en)B and inclusions t^m B ⊆ v^m B give
compatible quotient ring maps. Their sectionwise limit is f; its coordinates give
uniqueness. (4) Restriction to exponents en identifies the two B-towers cofinally:
the inverse reduces the em-th component to exponent m. The two composites are
identities by tower compatibility. (5) Passing the compatible quotient basis
isomorphisms and their coordinate inverses to sectionwise limits gives Φ.
Finite sums of coordinate inclusions identify the finite product with the direct
sum. (6) At cofinal exponent en the scalar action factors through A/t^n, so Φ
is R-linear. Its columns have residues b_i at every level, and its en-th
projection is precisely the quotient basis map after coordinatewise projection.
-/
theorem adic_basis_limit (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) :
    ∃ f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v,
      AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f ∧
      (∀ g, AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht g → g = f) ∧
      ∃ Φ : adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d ≅
          (SheafOfModules.restrictScalars f).obj
            (SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J B v)),
        (∀ (n : ℕ) (U : Cᵒᵖ)
          (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U),
          (adicBasisProjection.{uC, vC, r} J B v n).hom.app U (Φ.hom.val.app U x) =
            ∑ i : Fin d,
              (adicBasisScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                ((adicBasisProjection.{uC, vC, r} J A t n).hom.app U
                  (adicBasisCoordinate.{uC, vC, r} J
                    (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) *
                adicBasisConstant.{uC, vC, r} J B v n U (b i)) ∧
        (∀ n : ℕ, ∃ β : adicBasisFree.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d ≅
            (SheafOfModules.restrictScalars
              (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n)).obj
                (SheafOfModules.unit (adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1))),
          (∀ (U : Cᵒᵖ)
            (y : (adicBasisFree.{uC, vC, r} J
              (adicBasisResidue.{uC, vC, r} J A t n) d).val.obj U),
            β.hom.val.app U y = ∑ i : Fin d,
              (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                (adicBasisCoordinate.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d U y i) *
                adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i)) ∧
          (∀ (U : Cᵒᵖ)
            (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U),
            (adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1)).hom.app U
                (Φ.hom.val.app U x) =
              ∑ i : Fin d,
                (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                  ((adicBasisProjection.{uC, vC, r} J A t n).hom.app U
                    (adicBasisCoordinate.{uC, vC, r} J
                    (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) *
                  adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i))) := by
  sorry

end CategoryTheory
