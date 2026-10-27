/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Clopen restriction of finite geometric categorical quotients

Source: ILO, Travaux de Gabber, Expose X 2.3 Step 2, diagram (2.c), printed p. 151;
Expose IX 1.4, printed pp. 132--133; Stacks Project, Tags 01HI, 01JB, 01JC, 01WL.
(blueprint: lem-sfb-clopen-geometric-categorical-quotient)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Restricting a finite geometric categorical quotient to a clopen target preserves
all its quotient properties, including admissibility when supplied. The action on the
inverse-image open subscheme is characterized by equivariance of its open inclusion.
No field of definition, separation, finite-type, Noetherian or normality condition is used.

Source: ILO X 2.3 Step 2, diagram (2.c), p. 151; IX 1.4, pp. 132--133.
(blueprint: lem-sfb-clopen-geometric-categorical-quotient)

Proof:
1. Write C = X minus U and D = q inverse C. Invariance of q makes q inverse U and D
   invariant complementary clopens. Restrict the action by unique open factorization
   (lem-weil-pbc-morphism-factors-through-open-subscheme). Uniqueness preserves its
   group laws. The restriction square is cartesian (def-pc-fibre-product), so finite
   base change (lem-weil-pbc-finite-morphism-permanence) gives finiteness. Surjectivity
   restricts pointwise (def-weil-surjective-morphism).
2. Open factorization identifies the field-valued points of each open subscheme with
   the original points landing there. Surjectivity on these points restricts, and the
   given orbit-fibre equivalence restricts to the induced action.
3. For any open W of U, sections on W and its inverse image are the original sections
   with the same pullback maps (def-weil-open-immersion). Thus their invariant subrings
   and the canonical section map are unchanged.
4. For an invariant map a from q inverse U to any T, glue its composite into T coproduct C
   with the composite D to C to T coproduct C. The overlap is empty. The resulting map
   from V is invariant and descends uniquely to X by the supplied categorical property
   (lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-scheme-morphism-gluing).
5. Surjectivity of q shows that the descended map sends U into the open T summand.
   Open factorization gives the required map U to T. Cancel the open inclusion to
   check its composite with q restricted to U equals a.
6. Glue any two candidate descents on U with the identity into C on the complement.
   Both give the same extension on V. Categorical uniqueness for q makes them equal;
   restriction and open-factorization uniqueness give equality of the candidates.
7. If q is admissible (def-per-admissible-finite-scheme-quotient), underlying orbit
   fibres restrict. A subset of U whose inverse image is open is open in X by the
   quotient topology for q, and hence in U. Every orbit in q inverse U lies in the
   inverse image of an affine neighbourhood in U (lem-weil-pbc-affine-opens-basis).
   This inverse image is affine by finite base change and the affine-source clause of
   lem-weil-pbc-finite-morphism-permanence. Together with steps 1 and 3 this is every
   admissibility condition. Empty and full opens, empty schemes and trivial groups
   are covered by the same argument. -/
theorem clopen_geometric_categorical_quotient
    {H : Type v} [Group H] [Finite H] {V X : Scheme.{u}}
    (a : H →* Aut V) (q : V ⟶ X) [IsFinite q] [Surjective q]
    (hinv : ∀ h : H, (a h).hom ≫ q = q)
    (hpoints : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Surjective (fun x : Spec (.of Ω) ⟶ V ↦ x ≫ q) ∧
      ∀ x y : Spec (.of Ω) ⟶ V,
        x ≫ q = y ≫ q ↔ ∃ h : H, x ≫ (a h).hom = y)
    (hsections : ∀ W : X.Opens,
      Function.Injective (q.app W).hom ∧
      ∀ s : Γ(V, q ⁻¹ᵁ W),
        (s ∈ Set.range (q.app W).hom ↔
          ∀ (h : H) (O : V.Opens) (hO : O ≤ q ⁻¹ᵁ W)
            (hOh : O ≤ (a h).hom ⁻¹ᵁ (q ⁻¹ᵁ W)),
            ((a h).hom.appLE (q ⁻¹ᵁ W) O hOh).hom s =
              (V.presheaf.map (homOfLE hO).op).hom s))
    (hcategorical : ∀ (T : Scheme.{u}) (f : V ⟶ T),
      (∀ h : H, (a h).hom ≫ f = f) → ∃! g : X ⟶ T, q ≫ g = f)
    (U : X.Opens) (hU : IsClopen (U : Set X)) :
    IsClopen (q ⁻¹ᵁ U : Set V) ∧
    ∃ aU : H →* Aut (q ⁻¹ᵁ U).toScheme,
      (∀ h : H, (aU h).hom ≫ (q ⁻¹ᵁ U).ι = (q ⁻¹ᵁ U).ι ≫ (a h).hom) ∧
      IsFinite (morphismRestrict q U) ∧ Surjective (morphismRestrict q U) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective
          (fun x : Spec (.of Ω) ⟶ (q ⁻¹ᵁ U).toScheme ↦ x ≫ morphismRestrict q U) ∧
        ∀ x y : Spec (.of Ω) ⟶ (q ⁻¹ᵁ U).toScheme,
          x ≫ morphismRestrict q U = y ≫ morphismRestrict q U ↔
            ∃ h : H, x ≫ (aU h).hom = y) ∧
      (∀ W : U.toScheme.Opens,
        Function.Injective ((morphismRestrict q U).app W).hom ∧
        ∀ s : Γ((q ⁻¹ᵁ U).toScheme, morphismRestrict q U ⁻¹ᵁ W),
          (s ∈ Set.range ((morphismRestrict q U).app W).hom ↔
            ∀ (h : H) (O : (q ⁻¹ᵁ U).toScheme.Opens)
              (hO : O ≤ morphismRestrict q U ⁻¹ᵁ W)
              (hOh : O ≤ (aU h).hom ⁻¹ᵁ (morphismRestrict q U ⁻¹ᵁ W)),
              ((aU h).hom.appLE (morphismRestrict q U ⁻¹ᵁ W) O hOh).hom s =
                ((q ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE hO).op).hom s)) ∧
      (∀ (T : Scheme.{u}) (f : (q ⁻¹ᵁ U).toScheme ⟶ T),
        (∀ h : H, (aU h).hom ≫ f = f) →
          ∃! g : U.toScheme ⟶ T, morphismRestrict q U ≫ g = f) ∧
      (IsAdmissibleFiniteSchemeQuotient a q →
        IsAdmissibleFiniteSchemeQuotient aU (morphismRestrict q U)) := by
  sorry

end AlgebraicGeometry
