/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The maximal isomorphism open of a morphism of schemes

For a morphism `q : Z ⟶ X` we define `q.maximalIsomorphismOpen` as the union of all
opens `W ⊆ X` over which `q` restricts to an isomorphism, and prove that `q` is an
isomorphism over it: being an isomorphism is Zariski-local on the target, so the local
inverses glue.
(Blueprint: `def:nagata-maximal-isomorphism-open`,
`lemma:nagata-maximal-isomorphism-open`.)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (q : Z ⟶ X)

/-- The **maximal isomorphism open** of a morphism `q : Z ⟶ X`: the union of all opens
`W ⊆ X` such that `q` restricts to an isomorphism over `W`.
(Blueprint: `def:nagata-maximal-isomorphism-open`.) -/
def Scheme.Hom.maximalIsomorphismOpen : X.Opens :=
  sSup {W : X.Opens | IsIso (q ∣_ W)}

variable {q}

/-- Every open over which `q` restricts to an isomorphism is contained in the maximal
isomorphism open. -/
lemma Scheme.Hom.le_maximalIsomorphismOpen {W : X.Opens} (hW : IsIso (q ∣_ W)) :
    W ≤ q.maximalIsomorphismOpen :=
  le_sSup hW

variable (q)

/-- **The maximal isomorphism open is an isomorphism locus**: `q` restricts to an
isomorphism over `q.maximalIsomorphismOpen`, because being an isomorphism is
Zariski-local on the target and the defining opens cover it.
(Blueprint: `lemma:nagata-maximal-isomorphism-open`.) -/
lemma Scheme.Hom.isIso_restrict_maximalIsomorphismOpen :
    IsIso (q ∣_ q.maximalIsomorphismOpen) := by
  change MorphismProperty.isomorphisms Scheme (q ∣_ q.maximalIsomorphismOpen)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (U := fun W : {W : X.Opens // IsIso (q ∣_ W)} ↦
      q.maximalIsomorphismOpen.ι ⁻¹ᵁ W.1) ?_ fun W ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    have hx : x.1 ∈ q.maximalIsomorphismOpen := x.2
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
  · have himg : q.maximalIsomorphismOpen.ι ''ᵁ
        (q.maximalIsomorphismOpen.ι ⁻¹ᵁ W.1) = W.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (Scheme.Hom.le_maximalIsomorphismOpen W.2)]
    exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
      (morphismRestrictRestrict q _ _ ≪≫ morphismRestrictEq q himg)).mpr W.2

end AlgebraicGeometry
