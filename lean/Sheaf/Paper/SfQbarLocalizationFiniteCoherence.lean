/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.SfQbarLocalizationFiniteData

/-! # Normalized finite localization coefficient compatibility

Source: the finite-stage compatibility steps of the localization argument.
(blueprint: lem-sf-qbar-localization-finite-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Descent
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Z U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ z : Z, Invertible (l : Z.residueField z)]
  [∀ t : U, Invertible (l : U.residueField t)]

/-- The normalized finite localization packages admit coherent coefficient actions.
Source: algebraically closed-stage localization proof, steps 1--2 and the finite
normalizations in step 5 (blueprint: lem-sf-qbar-localization-finite-coherence).

Proof: take the rational localization package at each finite coefficient field.
Use its open compact-support functor for the compactification (j,id), and its
ordinary closed direct image. Restrict the canonical pullback scalar comparison
to the two immersions and identify the stage transitions by
operationStageTransitionIso. Its tower law follows from balanced tensor
associativity, and its identity law from multiplication of the coefficient unit.
The compact-support coefficient action is the localized integral tensor-unit
mate; its tower and unit equations are the compact-support scalar equations.
For closed direct image take the adjunction mate of the inverse pullback
comparison. Finite free scalar extension makes this mate invertible. The mate
counit equation and adjunction injectivity prove its tower and unit equations.
All finite shifts are the normalized rational localization shifts. The ringed
scalar/pullback and compact-support scalar shift normalization lemmas give
the actual integral comparison squares. Compute the
coefficient maps degreewise on resolving complexes: scalar factors have degree
zero, so shifting multiplies both differentials by the same sign. Localization
then preserves each shift square, using the shift equations in the rational
exact-functor records. Scalar shift tower transport supplies the repeated-field
and coefficient-unit cases. The normalized integral units and counits,
and hence their localized rational maps, obey the coefficient mate equations.
These equations are precisely the compatibility conditions for the four
StageSystem.Morphism.Hom families in the conclusion. The normalized finite
adjunctions commute with shifts because their integral maps are degree zero.
This constructs only finite data and its coefficient laws; it makes no claim
about the descended category or arbitrary common-stage morphisms.
-/
theorem sfQbarLocalizationFiniteCoherence
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Nonempty (SfQbarLocalizationFiniteData l Ω D hl i j) := by
  sorry

end Descent
end WeilConjectures
