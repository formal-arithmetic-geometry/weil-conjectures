/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar


/-! # BoundedConstructibleLowerStarSingleUpperBound

The remaining single-sheaf cohomological finiteness input for ordinary direct image.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- An upper direct-image bound for a constructible module placed in degree zero.

Source: Bhatt--Scholze, Section 6.8, and blueprint `lem-sfb-dc-lower-star-preserves`,
steps 1--8. For integral coefficients, the integral stratified-perfect characterization
identifies F[0] with a derived-complete object whose finite reductions lie in one finite
interval. Direct image preserves the completion tower and commutes with reduction, by the
perfect projection formula for each finite coefficient quotient. Finite-torsion direct-image
finiteness and its uniform cohomological-dimension bound put all these direct images in
one finite interval. The reverse stratified-perfect characterization bounds the ambient,
uncompleted direct image. For rational coefficients, choose an integral constructible
representative and use the rationalization equivalence and direct-image continuity for
uniformly bounded-below diagrams. For algebraic-closure coefficients, descend to a finite
extension, apply that case, and use the finite-free scalar-extension comparison and filtered
continuity. Unit-ball coefficients identify with the integral coefficients using their given
norm. Finite discrete ell-power-torsion coefficients follow from the finite-type etale
direct-image theorem and etale/pro-etale comparison. The zero ring and the zero sheaf give
zero direct image, including on the empty scheme.
(blueprint: lem-sfb-dc-lower-star-single-upper-bounded) -/
theorem constructible_single_rightDerivedLowerStar_upper_bounded
    [IsFinitenessCoefficient ℓ Λ]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Λ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
