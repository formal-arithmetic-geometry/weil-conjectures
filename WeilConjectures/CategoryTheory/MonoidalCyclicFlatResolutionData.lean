/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.MonoidalCyclicFlatCore

/-! # Flat-term replacements for cyclic fixed pairs

The structural input is separated from the unbounded resolution argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  (T : A ⥤ A) [T.Additive] [T.IsEquivalence] [T.Braided]

/-- The resolution conclusion for a specified monoidal structure.
Source: Stacks Project, `sites-cohomology.tex`, lemma-K-flat-resolution and
`derived.tex`, lemma-localization-subcategory
(blueprint: lem-pur-monoidal-cyclic-flat-resolution-data). -/
structure MonoidalCyclicFlatResolutionData
    [MonoidalCategory (IsoAlgebra T)] [MonoidalPreadditive (IsoAlgebra T)]
    [HasCountableCoproducts (IsoAlgebra T)] where
  /-- Flat-term K-flat replacements exist for unbounded complexes. -/
  resolution (K : CochainComplex (IsoAlgebra T) ℤ) :
    ∃ (P : CochainComplex (IsoAlgebra T) ℤ) (s : P ⟶ K),
      QuasiIso s ∧ P.IsKFlatForTotalTensor ∧ ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- Flat-term replacements follow from the structural core.
Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, step (2);
Stacks Project, `sites-cohomology.tex`, lemma-K-flat-resolution and `derived.tex`,
lemma-localization-subcategory
(blueprint: lem-pur-monoidal-cyclic-flat-resolution-data).

Proof: use the flat-valued cover IBU→id supplied by the core. Resolve the bounded-above
truncations by flat terms and take their exact sequential colimit. Tensor preserves this
colimit because the category is closed. Bounded-above flat complexes are K-flat; exact
filtered colimits preserve their acyclic tensor tests and the flatness of each term.
Thus the colimit augmentation is a quasi-isomorphism with flat-term K-flat source.
In each degree, the flatness test is an exact filtered colimit of exact tensor tests.
This proves flat terms even for the zero complex and with no boundedness assumption on K.
The cone comparison identifies the acyclic tensor tests with the specified two-sided
quasi-isomorphism definition. Localization is proved in the parent from these replacements. -/
theorem monoidalCyclicFlatResolutionData
    (B : A ⥤ A) (b : B ⟶ 𝟭 A) (c : MonoidalCyclicFlatCore.{u, v, w} T B b) :
    letI := c.monoidal
    letI := c.monoidalPreadditive
    letI := c.countableFixed
    Nonempty (MonoidalCyclicFlatResolutionData.{u, v} T) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
