/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Agreement of the coefficient and cocone transitivity comparisons

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`, the construction in
`def-sfb-derived-extend-comp-iso.proof.md` and its bounded constructible restriction in
`def-sfb-constructible-extend-comp-iso.proof.md`.
(blueprint: lem-sfb-coefficient-cocone-comparison-agreement)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale

/-- The fixed finite coefficient tensor comparison is the cocone's ambient comparison,
and both components of its restriction are the corresponding ambient arrows.

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`,
`def-sfb-derived-extend-comp-iso.proof.md` (exact-derived composition and the underived
extension comparison), and `def-sfb-constructible-extend-comp-iso.proof.md` (full restriction).
(blueprint: lem-sfb-coefficient-cocone-comparison-agreement)

Proof plan:
1. Unfold `finiteCoefficientDerivedExtension`, `finiteCoefficientDerivedToAlgCl`,
   `derivedExtendScalarsSubfield`, and `derivedExtendScalarsToPadicAlgCl`. They are total
   left derived extensions along the same internal coefficient inclusions. In particular,
   the closure coefficient ring is the specified finite-subfield-valued condensed ring.
2. Both ambient comparisons are the inverse exact-derived composition isomorphism followed
   by derivation of the underived tensor multiplication comparison and the same coefficient
   map equality. Underived multiplication takes the composite adjunction unit to the direct
   unit, so uniqueness in `lem-weil-pbc-conjugate-iso-unit-equation` identifies it with the
   unit-compatible comparison. Substitution gives equality of the specified natural
   isomorphisms, as in `def-weil-pbc-finite-derived-tensor-comparison` and
   `def-sfb-derived-extend-comp-iso`; no existential choice of an isomorphism is used.
3. Evaluate that equality at an ambient object and project to each of `hom` and `inv`.
4. Unfold `constructibleToPadicAlgClCompIso`. Full-faithful cancellation defines its
   components as preimages of the ambient components. The full inclusion maps each preimage
   back to that arrow. Apply step 3 to the underlying object `K.obj` to obtain both displayed
   component equalities. This uses the already-defined constructible restriction, with no
   additional preservation hypothesis.
-/
theorem finiteCoefficient_cocone_comparison_agreement
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ H) :
    finiteCoefficientDerivedTensorCompIso X ℓ h = derivedExtendScalarsCompIso X ℓ h ∧
      ∀ K : PadicSubfieldConstructible X ℓ E,
        ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
            (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj ∧
          ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
            (finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj := by
  refine ⟨rfl, ?_⟩
  intro K
  constructor <;>
    simp only [constructibleToPadicAlgClCompIso,
      ← show finiteCoefficientDerivedTensorCompIso X ℓ h =
        derivedExtendScalarsCompIso X ℓ h from rfl,
      CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app,
      CategoryTheory.Functor.fullyFaithfulCancelRight_inv_app]
  all_goals
    rw [← CategoryTheory.ObjectProperty.ι_map, CategoryTheory.Functor.map_preimage]
    first
    | exact CategoryTheory.Category.id_comp
        ((finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj)
    | exact CategoryTheory.Category.comp_id
        ((finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj)

end AlgebraicGeometry.ProEtale
