/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.H1CotangentFiniteSubfields

/-! # Square-zero lifting for arbitrary separable field extensions

Source: Stacks Project, Algebra, Tag 0322, proposition-characterize-separable-field-extensions;
Tag 0320 (3), lemma-formally-smooth-extensions-easy; Tag 00TI, definition-formally-smooth
(blueprint: lem-sfb-separable-field-square-zero-lifting).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Every algebra map from an arbitrary separable field extension into a square-zero quotient
lifts to the original algebra. Separability here means separable generation of every finitely
generated intermediate field; neither algebraicity nor finite generation of the whole extension
is required.

Source: Stacks Project, Algebra, Tag 0322, proposition-characterize-separable-field-extensions,
characteristic-zero clause (3) and positive-characteristic implication (1) implies (6);
Tag 0320 (3), lemma-formally-smooth-extensions-easy; Tag 00TI, definition-formally-smooth
(blueprint: lem-sfb-separable-field-square-zero-lifting).

Proof:
1. For each finitely generated intermediate field E, `IsSeparableExtension` gives a separating
   transcendence basis (`def-weil-pbc-separable-field-extension`). Apply the separably generated
   vanishing result (`lem-sfb-separably-generated-field-h1-zero`), namely
   `FormallySmooth.of_algebraicIndependent_of_isSeparable` followed by
   `FormallySmooth.subsingleton_h1Cotangent`, to obtain H₁(L_{E/k}) = 0.
2. Apply `subsingleton_h1Cotangent_of_finite_subfields`
   (`lem-weil-pbc-h1-cotangent-finite-subfields`) to get H₁(L_{L/k}) = 0.
   This finite-support argument does not choose compatible lifts on the subfields.
3. The differential module Ω[L⁄k] (`def-weil-pbc-kahler-differentials`) is an L-vector space,
   hence free by `Module.Free.of_divisionRing` and projective by `Module.Projective.of_free`
   (`lem-weil-pbc-vector-space-projective`), with no dimension restriction.
4. These two properties give `FormallySmooth k L`. Apply `FormallySmooth.comp_surjective`
   (`lem-weil-pbc-smooth-ring-map-square-zero-lifting`) to J and g. The resulting lift satisfies
   the stated equation for `Ideal.Quotient.mkₐ k J`
   (`def-weil-pbc-algebra-hom-quotient`). -/
theorem exists_lift_of_isSeparableExtension
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    (hsep : IsSeparableExtension k L)
    (D : Type w) [CommRing D] [Algebra k D]
    (J : Ideal D) (hJ : J ^ 2 = ⊥) (g : L →ₐ[k] D ⧸ J) :
    ∃ f : L →ₐ[k] D, (Ideal.Quotient.mkₐ k J).comp f = g := by
  have h1 : Subsingleton (H1Cotangent k L) :=
    subsingleton_h1Cotangent_of_finite_subfields k L fun E hE ↦ by
      obtain ⟨s, hs, hsepE⟩ := hsep E hE
      have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → E))) E := by
        rw [Subtype.range_coe]
        exact hsepE
      have : FormallySmooth k E :=
        FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
      exact FormallySmooth.subsingleton_h1Cotangent
  have : FormallySmooth k L := ⟨inferInstance, h1⟩
  exact FormallySmooth.comp_surjective k L J hJ g

end Algebra
