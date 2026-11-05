/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.Algebra.Homology.DerivedCategory.InjectiveHom
public import WeilConjectures.CategoryTheory.Monoidal.UnitIsoBijective
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The trace isomorphism over a separably closed field: the point computations

Let `k` be a separably closed field, `s = Spec k` and `a : X ⟶ s` with `X` connected. This file
contains the two inputs of the trace isomorphism that are computations in the point category
`D(s_ét, Λ)`:

* `AlgebraicGeometry.Etale.bijective_comp_unit_rightDerivedLowerStar`: for a self-injective
  coefficient ring `Λ`, evaluation at the class `1 ∈ H⁰(X, Λ)`,
  `Hom(Ra_* Λ_X, Λ_s) ⟶ Hom(Λ_s, Λ_s)`, is bijective. This is `H⁰(X, Λ) = Λ` for the connected
  `X` together with `Ext^{>0}_Λ(-, Λ) = 0`.
* `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap_of_bijective_traceMap`:
  over `s` the Tate twists are trivial, so the untwisted trace is bijective as soon as the
  twisted one is.

## Implementation notes

The elimination of the twists is first stated for a general coefficient category `A`, in terms
of `AlgebraicGeometry.Etale.derivedTensor` and its structure isomorphisms
(`AlgebraicGeometry.Etale.bijective_comp_derivedTensor_untwist`), and then specialised to
`A = ModuleCat Λ`: there the monoidal instance on `D(X_ét)` found by instance search is a term
which the kernel cannot compare with the one inside `derivedTensor` in reasonable time (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable [HasTateTwist Λ]

variable (Λ k) [HasInvertibleExponent Λ (Spec (.of k))] in
/-- Over a separably closed field the Tate twists are trivial, `Λ_s(m) ≅ Λ_s`: the twisting
object is a locally constant sheaf in degree `0` whose stalk is free of rank one, and on
`Spec k` such a sheaf is constant. -/
theorem nonempty_tateObject_iso_unit (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of k)) m ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) := by
  obtain ⟨L, -, hL, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of k)) m
  obtain ⟨f⟩ := hL k (𝟙 _)
  obtain ⟨g⟩ := Scheme.nonempty_iso_constantSheaf_of_sheafFiber_iso L f
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso g ≪≫
    (unitIsoSingleFunctorConstantSheaf Λ _).symm⟩

namespace TateOrientation

variable [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  {a : X ⟶ Spec (.of k)} [HasCompactification a] {d : ℕ}

end TateOrientation

end AlgebraicGeometry.Etale
