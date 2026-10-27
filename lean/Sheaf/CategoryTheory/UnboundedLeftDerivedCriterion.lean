module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated

/-! # An unbounded left-derived existence criterion

Source: Stacks Project, Derived Categories, Tag 0794, hypotheses (1)--(5),
and Tags 05S8--05S9 for pointwise definedness.
(blueprint: lem-trf-unbounded-left-derived-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.Functor

/-- A right exact additive functor satisfying the bounded-above acyclicity criterion
and commuting with exact sequential colimits has an everywhere defined left derived
functor. The conclusion unfolds `IsTriangulatedLeftDerivedDefinedAt`: its denominator
pro-diagram has a value in the unbounded derived category of the target.

Source: Stacks Project, Derived Categories, Tag 0794 and Definition 05S9(2).
(blueprint: lem-trf-unbounded-left-derived-criterion)

Proof:
1. Replace `P` by its isomorphism closure. Conjugating differentials by termwise
isomorphisms preserves the upper bound and acyclicity, so the hypotheses persist.
2. The cone criterion (lem-pur-quasi-iso-cone-acyclic) and additivity imply that `F`
preserves quasi-isomorphisms between bounded-above complexes with terms in this class.
3. Apply lem-sfb-subcategory-truncation-resolution-system to the good truncations of
any complex. Their compatible resolutions have a termwise sequential colimit mapping
quasi-isomorphically to that complex: src-weil-homology-preserves-exact-colimits reduces
this to the eventually constant cohomology of the good truncations.
4. Let the resolving class consist of these colimit presentations, with the stage `n`
augmentation inducing isomorphisms in degrees at most `n` and vanishing above `n`.
The preceding construction supplies a quasi-isomorphism from this class to every complex.
5. For a quasi-isomorphism between two such colimits, apply
lem-trf-bounded-stage-roof-comparison. It supplies stage cohomology isomorphisms
compatible both with transitions and with the actual map between the colimits;
that map need not come from a map of towers.
6. Preservation and exactness of sequential colimits identify the target cohomology
with the colimits of stage cohomology. The compatible stage isomorphisms induce inverse
maps on colimits, and the augmentation equations identify the resulting map with the
cohomology of `F` applied to the given quasi-isomorphism.
7. Use lem-pur-resolving-class-essential-constancy in the homotopy category.
The fraction calculus and two-out-of-three follow from
lem-pur-quasi-isos-saturated-triangulated. Thus each denominator pro-diagram is
essentially constant. Additivity preserves shifts and cone matrices, so the composite
with `DerivedCategory.Qh` is exact and the setup is Situation 05S8. Definition 05S9(2)
then gives precisely the asserted everywhere definedness. -/
theorem unbounded_leftDerived_definedAt_of_resolvingClass
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : A → Prop) (hzero : P (0 : A))
    (hsum : ∀ (X Y : A), P X → P Y → P (X ⊞ Y))
    (hcover : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X), P Y ∧ Epi p)
    (hacyclic : ∀ K : CochainComplex A ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) →
      (∀ i : ℤ, P (K.X i)) → K.Acyclic →
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    ∃ Y : DerivedCategory B,
      IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
          Over.forget X ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y := by
  sorry

end CategoryTheory.Functor
