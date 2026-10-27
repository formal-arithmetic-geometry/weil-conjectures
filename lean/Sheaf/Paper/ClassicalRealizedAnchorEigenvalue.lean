/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # An eigenvalue at a nonzero classical lisse fibre

Source: blueprint latest, thm-zl-real-mixed-by-curves.proof.md, paragraph 3.
(blueprint: lem-zl-classical-realized-anchor-eigenvalue).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- A nonzero classical lisse Weil sheaf on a geometrically connected base has an
actual finite-presentation punctual eigenvalue at every closed point.

Source: blueprint latest, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 3; step 1 of the anchored criterion.
(blueprint: lem-zl-classical-realized-anchor-eigenvalue).

Proof: the geometric fibre is connected by geometric connectedness and is
Noetherian and separated by finite-type base change. Lift the closed point to the
algebraic closure using finiteness of its residue field. The lisse sheaf/fundamental
representation equivalence identifies its fibre functor with a faithful equivalence,
so a zero fibre would force the classical carrier to be zero. The fibre is thus a
nonzero finite-dimensional vector space. Apply the normalized classical local
Frobenius comparison at the positive residue degree to identify this fibre and its
operator with the normalized realization's local fibre. Descend the Weil object,
its structure isomorphism and inverse to one finite coefficient stage. The point
pullback and scalar cohomology comparisons identify the normalized fibre operator
with the scalar extension of that stage's localClosedFrobeniusCohomology in degree
zero. Over the algebraically closed coefficient field, exists_eigenvalue supplies
an eigenvalue of this endomorphism of a nonzero finite-dimensional vector space.
The finite model, its Weil isomorphism and the chosen residue embedding witness
SfPunctualEigenvalue. No nonvanishing of the eigenvalue or curve-purity assumption
is used. -/
theorem classicalRealized_anchor_eigenvalue
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [Nonempty X₀.left] [GeometricallyConnected X₀.hom]
    (A : @ZlClassicalRealization D l _ hl Ω _ _ _ X₀ _ _ _
      (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩))
    (S : @ZlClassicalWeil D l _ Ω _ _ _ X₀ _ _ _ (⟨fun x ↦ @isUnit_of_invertible _ _ _
        (zlClassicalStalkInvertible D l hl X₀ x)⟩))
    (hne : ¬ IsZero S.carrier)
    (anchor : {x : X₀.left // x ∈ closedPoints X₀.left}) :
    ∃ α : Ω, SfPunctualEigenvalue D l hl Ω X₀
      ((@ZlClassicalRealization.weil D l _ hl Ω _ _ _ X₀ _ _ _
        (⟨fun x ↦ @isUnit_of_invertible _ _ _
          (zlClassicalStalkInvertible D l hl X₀ x)⟩) A).obj S) anchor α := by sorry

end WeilConjectures
