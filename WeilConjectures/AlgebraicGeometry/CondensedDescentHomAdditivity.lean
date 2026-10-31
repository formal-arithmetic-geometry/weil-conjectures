/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientFiniteDescentHom
public import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedFlatCoefficientCalculus

/-! # Additive normalized coordinates for condensed coefficient descent

Source: latest Weil blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/_section.md, clause (1), and
sk-lem-coefficient-finite-descent-hom.proof.md, paragraphs (1) and (3)
(blueprint: lem-pur-general-specialization-hom-additivity).

The homomorphisms below are characterized on every input by the already specified
scalar-extension maps. The additive equivalence is characterized on the canonical
colimit generators. Both sides use their existing abelian group structures.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The ambient shifted Hom group at a finite field containing E.
Source: latest blueprint, sk-thm-sfb-qlbar-two-colimit, clause (1)
(blueprint: lem-pur-general-specialization-hom-additivity). -/
abbrev condensedDescentStageHom (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ)
    (F : Set.Ici E) : Type _ :=
  (derivedExtendScalarsSubfield X ℓ F.property).obj C.obj ⟶
    ((derivedExtendScalarsSubfield X ℓ F.property).obj D.obj)⟦r⟧

/-- The ambient shifted Hom group over the finite-subextension condensed closure.
Source: latest blueprint, sk-thm-sfb-qlbar-two-colimit, clause (1)
(blueprint: lem-pur-general-specialization-hom-additivity). -/
abbrev condensedDescentAmbientHom (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) : Type _ :=
  (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
    ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧

open Classical in
/-- The canonical finite-stage transition and evaluation maps are additive, and their
abelian-group colimit has the unique representative-normalized additive inverse to
scalar extension. The existential homomorphisms have completely specified underlying
functions; the comparison equivalence is fixed on every canonical colimit generator.

Source: latest blueprint, sk-thm-sfb-qlbar-two-colimit/_section.md, clause (1), and
sk-lem-coefficient-finite-descent-hom.proof.md, paragraphs (1) and (3)
(blueprint: lem-pur-general-specialization-hom-additivity).

Proof:
1. Restriction of coefficient modules preserves zero and addition on underlying maps.
The scalar adjunction of sk-def-sfb-change-of-scalars and
lem-sp-proetale-additive-left-adjoint make extension additive. The standing finite-type
scheme is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
lem-weil-pbc-condensed-flat-coefficient-calculus identifies the actual left-derived
extensions with their exact termwise functors; lem-sf-exact-functor-derived-triangulated
makes these additive for the inherited ambient Hom laws.
2. Expand coefficientDescentHomTransition and coefficientDescentHomToAlgCl: each is
extension on arrows, precomposition with the inverse source multiplication comparison,
and postcomposition with the shift and target multiplication comparisons. Bilinearity
makes these additive. The unit, pentagon and shift identities in
lem-weil-pbc-condensed-flat-coefficient-calculus give the directed-system identities
and compatibility of evaluation. Package these exact functions as t and b.
3. The universal property of def-weil-directed-colimit-abelian-groups gives beta from b.
Its underlying representative map is the canonical map of
det-lem-coefficient-finite-descent-hom, hence is bijective. Thus beta is an additive
equivalence. Its inverse sends b_F(u) to the canonical class of u. Every ambient arrow
has such a representative, proving uniqueness among all functions with this rule.
4. The inverse of an additive equivalence preserves zero and addition. The colimit
relations identify the classes of u and v with their transitions at any finite common
upper field H. Addition of the two classes is therefore the class of their sum at H.
All additions used here are the existing ambient and algebraic-colimit additions. -/
theorem condensed_descent_hom_additivity
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    ∃ (t : ∀ (F G : Set.Ici E), F ≤ G →
        condensedDescentStageHom X ℓ E C D r F →+
          condensedDescentStageHom X ℓ E C D r G)
      (b : ∀ F : Set.Ici E, condensedDescentStageHom X ℓ E C D r F →+
        condensedDescentAmbientHom X ℓ E C D r),
      (∀ (F G : Set.Ici E) (h : F ≤ G) (f : condensedDescentStageHom X ℓ E C D r F),
        t F G h f = coefficientDescentHomTransition X ℓ F.property h C.obj D.obj r f) ∧
      (∀ (F : Set.Ici E) (f : condensedDescentStageHom X ℓ E C D r F),
        b F f = coefficientDescentHomToAlgCl X ℓ F.property C.obj D.obj r f) ∧
      DirectedSystem (condensedDescentStageHom X ℓ E C D r) (fun {F G} h => t F G h) ∧
      (∀ (F G : Set.Ici E) (h : F ≤ G) (f : condensedDescentStageHom X ℓ E C D r F),
        b G (t F G h f) = b F f) ∧
      ∃ β : AddCommGroup.DirectLimit (condensedDescentStageHom X ℓ E C D r) t ≃+
          condensedDescentAmbientHom X ℓ E C D r,
        (∀ (F : Set.Ici E) (f : condensedDescentStageHom X ℓ E C D r F),
          β (AddCommGroup.DirectLimit.of _ t F f) = b F f) ∧
        (∀ (F : Set.Ici E) (f : condensedDescentStageHom X ℓ E C D r F),
          β.symm (b F f) = AddCommGroup.DirectLimit.of _ t F f) ∧
        (∀ c : condensedDescentAmbientHom X ℓ E C D r →
            AddCommGroup.DirectLimit (condensedDescentStageHom X ℓ E C D r) t,
          (∀ (F : Set.Ici E) (f : condensedDescentStageHom X ℓ E C D r F),
            c (b F f) = AddCommGroup.DirectLimit.of _ t F f) →
          c = (β.symm : condensedDescentAmbientHom X ℓ E C D r →
            AddCommGroup.DirectLimit (condensedDescentStageHom X ℓ E C D r) t)) ∧
        β.symm 0 = 0 ∧
        (∀ f g : condensedDescentAmbientHom X ℓ E C D r,
          β.symm (f + g) = β.symm f + β.symm g) ∧
        (∀ (F G H : Set.Ici E) (hF : F ≤ H) (hG : G ≤ H)
            (f : condensedDescentStageHom X ℓ E C D r F)
            (g : condensedDescentStageHom X ℓ E C D r G),
          β.symm (b F f + b G g) =
            AddCommGroup.DirectLimit.of _ t H (t F H hF f + t G H hG g)) := by
  sorry

end AlgebraicGeometry.ProEtale
