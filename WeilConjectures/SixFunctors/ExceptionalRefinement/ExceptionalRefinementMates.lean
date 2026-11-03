/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementSystemData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalRefinementMate
import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementLeftConstruction
import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementSystemRealization
import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementRightSquare

/-! # Normalized refinement mates of the transported exceptional adjunctions

Source: Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24;
Stacks 0F7B, 0F7I; blueprint exceptional construction, retained steps 20--21
(blueprint: lem-sf-exceptional-refinement-mates).

`Transport` retains the given operations and their prescribed compact-support realizations.
`Mates` records the two adjunction equations, normalizations and both descent equations.
`SystemRealization` retains the actual strict-system map before taking total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients
open WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]


variable {c d : Compactification f}

/-- Normalized refinement mates at all four coefficient stages, for the fixed transported
adjunctions. No separatedness of X or Y over k and no Cartesian refinement square is used.
Source: Zheng 2.23, 2.29, 3.16, 5.22, 5.24; Stacks 0F7B and 0F7I
(blueprint: lem-sf-exceptional-refinement-mates).

Proof:
1. Use exceptional finite operations and compactification coherence to invert the
   open-unit-normalized proper/open comparison, followed by proper composition.
   The refinement coefficient mate identifies this map under the canonical site comparisons.
2. Use integral compactification system realization and semilinear derived sections to
   form the intrinsic whole-system proper/open word. Integral reconstruction and exceptional
   system transport give normalized, etale-origin inputs and common finite bounds for both
   endpoints and the open/proper intermediates. Finite operations and conservative evaluation
   prove invertibility; evaluation is never used to infer equality of system maps.
3. Take total limit of this inverse and transport through the prescribed realizations.
   The system realization's primitive equalities give integralMap and the ambient ring
   normalization, as actual-map equalities with the original compact-support representative.
4. The diagram open/clopen shift models, adjunction shift uniqueness and whiskering rules
   give the finite and system shift squares. Integral realization shift coherence matches
   these with the same termwise and Roos-cone shifts under the prescribed realizations.
5. Define the right comparison by the transpose of the displayed left comparison and
   counit, and its inverse using the inverse left map. Conjugate equivalence proves they
   are inverse. Transpose the two sides of the unit equation; both become alpha by
   naturality and the two triangles. Units, counits and whiskering give the right shift square.
6. Apply the system proper/open scalar square to the refinement with r=identity and
   whisker by the proper image. Integral scalar mates and mate pasting give the same square
   for both maps before total limit, retaining ramified indices en and their cofinality.
7. Exceptional field descent localizes these actual maps and all equations on the same
   representatives. Naturality on an arbitrary fraction follows by multiplying integral
   naturality by its denominator inverse. This gives both rational formulas.
8. Define the closed-stage components over a common finite field. Scalar compatibility
   from step 6 proves independence of enlargement; common-stage morphisms give naturality.
   Units, counits, inverses and shifts descend, giving both common-field formulas.
-/
theorem exceptional_refinement_mates
    (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d)
    (o : ∀ E : FieldStage.{max u v} l, Operations l E.carrier)
    (R : ∀ E : FieldStage.{max u v} l, Realizations l E.carrier D (o E)) :
    ∃ P : Mates.{u, v} l Ω D hl A B r,
      ∀ E : FieldStage.{max u v} l, Nonempty (SystemRealization.{u, v} l Ω D hl A B r P E
        (o E) (R E)) := by
  obtain ⟨N⟩ := exceptional_refinement_left_construction l Ω D hl A B r
  let comparison (s : Stage.{max u v} l) :
      RefinementComparison.{u, v} l Ω (A.operation s) (B.operation s) :=
    let q := refinementComparisonOfLeft (A.operation s).adjunction (B.operation s).adjunction
      (N.left s) (N.leftShift s) (A.operation s).unitShift (B.operation s).counitShift
    { left := q.left, right := q.right, counit := q.counit, unit := q.unit,
      leftShift := q.leftShift, rightShift := q.rightShift }
  let P : Mates.{u, v} l Ω D hl A B r := {
    comparison := comparison
    normalized := N.normalized
    transpose := by
      intro s L
      change (conjugateEquiv (B.operation s).adjunction (A.operation s).adjunction
        (N.left s).hom).app L = _
      simp only [comparison, refinementComparisonOfLeft, conjugateEquiv_apply_app,
        Adjunction.homEquiv_unit, Functor.map_comp]
    inverseTranspose := by
      intro s L
      change (conjugateEquiv (A.operation s).adjunction (B.operation s).adjunction
        (N.left s).inv).app L = _
      simp only [comparison, refinementComparisonOfLeft, conjugateEquiv_apply_app,
        Adjunction.homEquiv_unit, Functor.map_comp]
    rationalLeft := N.rational
    rationalRight := fun E L ↦
      right_coefficient_square_of_left.{u, v} l Ω
        (A.operation (.integral E)) (B.operation (.integral E))
        (A.operation (.rational E)) (B.operation (.rational E))
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
        (A.localization E) (B.localization E)
        (comparison (.integral E)) (comparison (.rational E)) (N.rational E) L
    commonLeft := N.common
    commonRight := fun E L ↦
      right_coefficient_square_of_left.{u, v} l Ω
        (A.operation (.rational (commonField.{u, v} l Ω E)))
        (B.operation (.rational (commonField.{u, v} l Ω E)))
        (A.operation .closed) (B.operation .closed)
        (commonInclusion.{u, v} l Ω X E) (commonInclusion.{u, v} l Ω Y E)
        (A.common E) (B.common E)
        (comparison (.rational (commonField.{u, v} l Ω E)))
        (comparison .closed) (N.common E) L }
  exact ⟨P, fun E ↦ exceptional_refinement_system_realization l Ω D hl A B r P E (o E) (R E)⟩

end WeilConjectures.ExceptionalRefinement
