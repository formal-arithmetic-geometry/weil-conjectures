/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Function fields in a dominant affine transition limit

Source: Stacks Project, Tag 0EZJ, generic-fibre limit assertion.
(blueprint: lem-sbc-dominant-function-field-limit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The spectra of the stage function fields have the spectrum of the limit function
field as their limit, compatibly with the generic point inclusions.

Source: Stacks Project, Tag 0EZJ, the function-field part of the generic-fibre limit
assertion; the affine ring calculation is the same limit calculation as Tag 01ZA.
(blueprint: lem-sbc-dominant-function-field-limit)

Proof:
1. Dominance sends the generic point of S to the generic point of every X_i. The
induced stalk maps embed k(X_i) into k(S). For a transition X_i → X_j, dominance
follows because the projection S → X_j factors through it and is dominant. Thus its
map on generic stalks gives a field embedding k(X_j) → k(X_i). Functoriality of stalk
maps supplies the inverse diagram K of their spectra, its cone b, and the natural
transformation t of generic point inclusions. Take e_i to be the identity identification.
2. Fix a nonempty affine open U_j of one stage. Its inverse images U_i on the cofiltered
slice over j are affine, and their limit U in S is nonempty by dominance. The affine
limit calculation identifies Γ(U) with the filtered colimit of Γ(U_i). Dominance makes
these coordinate ring maps injective. All these rings are domains, and their fraction
fields are respectively k(S) and k(X_i).
3. A fraction in k(S) is the quotient of two elements of Γ(U). Both come from one
common stage Γ(U_i), and its denominator is nonzero there by injectivity. Thus it
comes from k(X_i). The same injectivity shows the colimit of these fraction fields
injects into k(S). This proves the field colimit assertion. The slice is cofinal, so
it proves the assertion for the original system. Applying Spec gives the limit cone b.
4. Every K_i is affine, hence qcqs, and every transition between affine schemes is
affine. Naturality of the generic stalk maps gives e_i^{-1}t_i equal to the stage
generic point inclusion and b_i t_i equal to the generic inclusion followed by α_i. -/
theorem exists_dominant_function_field_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S : Scheme.{u}} [IsIntegral S]
    (X : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hXqc : ∀ i, CompactSpace (X.obj i)) (hXqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
    (hdom : ∀ i, IsDominant (α.app i)) :
    ∃ (K : I ⥤ Scheme.{u}) (b : (Functor.const I).obj (Spec S.functionField) ⟶ K)
      (t : K ⟶ X) (e : ∀ i, K.obj i ≅ Spec (X.obj i).functionField)
      (hb : IsLimit (Cone.mk (Spec S.functionField) b)),
      (∀ i, CompactSpace (K.obj i)) ∧ (∀ i, QuasiSeparatedSpace (K.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f)) ∧
      (∀ i, (e i).inv ≫ t.app i = (X.obj i).fromSpecStalk (genericPoint (X.obj i))) ∧
      (∀ i, b.app i ≫ t.app i = S.fromSpecStalk (genericPoint S) ≫ α.app i) := by sorry

end AlgebraicGeometry.Scheme
