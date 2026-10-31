/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# The normalized integer shift on condensed bounded constructible complexes

Source: latest blueprint, sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/
`det-def-sfb-bounded-constructible.md`, specialization to the pulled-back condensed
algebraic closure; Stacks Project, Tag 05QM, `definition-triangulated-subcategory`
and `lemma-triangulated-subcategory`
(blueprint: lem-pur-general-pair-shift-normalization).

The category and the coefficient ring are the existing `BoundedConstructible` and
`Profinite.padicAlgClRingObj`. The normalization fixes the entire coherent shift,
including the zero and addition comparisons, by requiring the inclusion's coherent
shift comparisons to be identity maps. Heterogeneous equality expresses the object
transports in this identity normalization without choosing any new comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- There is a unique coherent additive integer shift on the bounded constructible
category with its ambient object and morphism formulas and identity comparisons for
its inclusion into the ordinary, uncompleted derived category.

Source: latest blueprint, `det-def-sfb-bounded-constructible.md`, condensed algebraic
closure specialization; Stacks Project, Tag 05QM, full triangulated subcategories
(blueprint: lem-pur-general-pair-shift-normalization).

Proof plan:
1. The ordinary derived category is the localization of integer cochain complexes
   at quasi-isomorphisms. Its canonical shifts are additive, send K to K[n] and f
   to f[n], and have the usual zero and addition comparisons
   (`det-def-sfb-derived-categories`, `def-weil-abstract-derived-category`).
2. A finite-type scheme over a field is Noetherian, hence its underlying space is
   Noetherian (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`). For the pulled-back
   condensed algebraic closure, bounded constructible objects form a full
   triangulated subcategory
   (`lem-sfb-bounded-constructible-triangulated-finiteness`). Restrict the ambient
   shifts, their additive action on morphisms, and their zero/addition comparisons
   to this subcategory (`def-weil-triangulated-subcategory`). The inclusion's
   comparisons are identities, so their CommShift laws express exactly that the
   restricted zero/addition comparisons are the ambient ones.
3. Any competing normalized structure has the same object and morphism maps.
   Full faithfulness of the inclusion and its identity comparison components then
   force the same zero and addition comparisons. The maps out of Discrete integers
   are determined by the functor laws, and all remaining coherence fields are
   propositions. Proof irrelevance gives equality of the full HasShift structures.
   No finite cohomological dimension hypothesis is used. -/
theorem padicAlgClShift_existsUnique
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    ∃! s : HasShift (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) ℤ,
      (fun [shiftInst : HasShift (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) ℤ] ↦
        (∀ n : ℤ,
          (shiftFunctor (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) n).Additive) ∧
        (∀ (n : ℤ) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧),
          ((shiftFunctor (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) n).obj K).obj =
            K.obj⟦n⟧) ∧
        (∀ (n : ℤ) (K L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) (f : K ⟶ L),
          HEq ((shiftFunctor (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧) n).map f).hom
            (f.hom⟦n⟧')) ∧
        ∃ c : (boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y.left)).ι.CommShift ℤ,
          (fun [commInst : (boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y.left)).ι.CommShift ℤ] ↦
            ∀ (n : ℤ) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj.{u} ℓ⟧),
              HEq (((boundedConstructible (condensedRingObj
                (Profinite.padicAlgClRingObj.{u} ℓ) Y.left)).ι.commShiftIso n).hom.app K)
                (𝟙 (K.obj⟦n⟧))) (commInst := c)) (shiftInst := s) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
