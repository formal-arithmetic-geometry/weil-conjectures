/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPunctualWeights
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ZlCanonicalImmersionStalkConjugacy

/-! # Punctual spectrum of canonical immersion inverse image

Source: blueprint restriction argument for open--closed reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]
  (W₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The canonical immersion pullback preserves each local eigenvalue and residue
field size. This is independent of the complex embedding and of any weight bound.

Source: blueprint restriction paragraph of lem-zl-morphism-open-closed-reduction;
lem-zl-immersion-weil-local-behavior(1), using the canonical integral pullback
comparisons, and Bhatt--Scholze 6.8.14--6.8.15 for coefficient descent.
(blueprint: lem-zl-canonical-immersion-punctual-spectrum).

Proof: factor the immersion into a closed and an open immersion. Their local-ring
maps induce isomorphisms of residue fields. A closed source point has residue
field finite over k0; the isomorphic image residue field is finite too, so the
image is closed and its cardinality is unchanged. Represent the input Weil pair,
its structure isomorphism and inverse equations over one finite coefficient field.
Use the inverse pullback-composition comparison at compatible geometric points.
The two normalized composition comparisons in zlFrobeniusSquare give exactly the
pullback of this Weil pair. Induction on the residue degree using associativity
and point-transport naturality shows that the stalk comparison intertwines the
three-factor local geometric Frobenius operators. These equations are compatible
with scalar extension. For an arbitrary finite Weil presentation of the output,
pass to a common enlargement with the pulled-back presentation; the presentation
isomorphism also intertwines the iterated structures and the local operators.
The stalk comparison takes a nonzero eigenvector to a nonzero eigenvector of the
same eigenvalue. Its original finite Weil presentation witnesses the input
punctual-eigenvalue predicate. No eigenvector exists on a zero stalk; empty schemes
give no closed-point obligation. The construction does not identify the universe
of Qbar with the universe of the schemes. -/
theorem zlCanonicalImmersionPunctualSpectrum (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left]
    (z : {z : W₀.left // z ∈ closedPoints W₀.left}) :
    ∃ hx : h₀.left z.val ∈ closedPoints X₀.left,
      Nat.card (W₀.left.residueField z.val) =
        Nat.card (X₀.left.residueField (h₀.left z.val)) ∧
      ∀ (F : sfCommonStageWeilSheaf D l hl X₀ Qbar) (α : Qbar),
        SfPunctualEigenvalue D l hl Qbar W₀ ((zlWeilPull D l hl Qbar h₀).obj F) z α →
          SfPunctualEigenvalue D l hl Qbar X₀ F ⟨h₀.left z.val, hx⟩ α := by
  classical
  have : JacobsonSpace X₀.left := LocallyOfFiniteType.jacobsonSpace X₀.hom
  have hx := h₀.left.closePoints_subset_preimage_closedPoints z.property
  have hi := h₀.left.isIso_residueFieldMap z.val
  let := hi
  refine ⟨hx, ?_, ?_⟩
  · exact (Nat.card_congr (Equiv.ofBijective (h₀.left.residueFieldMap z.val)
      (ConcreteCategory.bijective_of_isIso (h₀.left.residueFieldMap z.val)))).symm
  · intro F α hα
    obtain ⟨L, K, hK, ι, hι, heig⟩ := hα
    obtain ⟨L', K', hK', ι', hι', e, he⟩ :=
      zlCanonicalImmersionStalkConjugacy D l hl Qbar W₀ X₀ h₀ z hx F L K hK ι hι
    refine ⟨L', K', hK', ι', hι', ?_⟩
    obtain ⟨x, hx⟩ := heig.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.hom x)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · have he' := congrArg (fun f ↦ f x) he
      simp only [ModuleCat.comp_apply] at he'
      rw [he', hx.apply_eq_smul, map_smul]
    · intro hz
      apply hx.2
      exact e.toLinearEquiv.injective (by simpa using hz)

end WeilConjectures
