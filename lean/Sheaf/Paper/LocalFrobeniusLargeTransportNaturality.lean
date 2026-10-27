/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.LocalFrobeniusLargeCoefficients

/-! # Naturality of positive point transports

Source: Bhatt--Scholze, Remark 6.8.15; the point restriction-and-coprojection recipe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.commonStageDerivedPullback
  WeilConjectures.LocalFrobeniusLarge.composition
  WeilConjectures.LocalFrobeniusLarge.pointFibre
  WeilConjectures.LocalFrobeniusLarge.transportIterate
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocalFrobeniusLarge

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The prescribed positive transport is natural in every common-stage morphism.
Source: BS Remark 6.8.15; restriction naturality and the concatenation calculation
in lem-zl-large-transport-iterate-addition, step 1
(blueprint: lem-zl-large-transport-iterate-natural).

Proof: restriction of sections commutes with every module morphism, and the colimit
coprojections and sheafification map are natural. On a good flat complex this gives
an equality of chain maps, compatible with every quotient transition and with the
completed comparison. The same equation therefore holds after localization to the
integral derived category. Rationalization extends it linearly. For a common-stage
arrow choose its actual representative at a field containing both coefficient stages.
The tensor-normalized scalar comparisons commute with restriction and coprojection;
conjugating the finite-stage equation by these comparisons gives the one-step equation
for this representative, independent of further enlargement. For successive steps,
apply this square at each pulled-back morphism and use naturality of the specified
pullback compositor. Adjacent comparisons cancel. Induction on n then proves the
stated equation for the recursive transportIterate, including n = 0. -/
theorem transportIterate_naturality
    {N M : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))}
    (f : N ⟶ M) (n : ℕ) :
    letI := frobeniusPointPrimeInvertible D l hl
    (pointFibre D l hl Ω).map f ≫ transportIterate D l hl Ω M n =
      transportIterate D l hl Ω N n ≫ (pointFibre D l hl Ω).map
        ((commonStageDerivedPullback l Ω
          (localPositivePower (frobeniusPointIso D).hom n)).map f) := by sorry

end WeilConjectures.LocalFrobeniusLarge
