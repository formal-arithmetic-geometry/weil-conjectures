/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.TraceFormula.Specialization.TraitDirectImageUnit
public import WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Deligne's finiteness theorem for the nearby cycles of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait, with
geometric generic point `j : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`. The geometric
nearby cycles `Li^* Rj_* Lj^*` of `S` carry bounded constructible complexes of `ℚ̄_ℓ`-sheaves
on `S` to bounded constructible complexes on `Spec k'`
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj`). This is the case
`𝔸⁰_S = S` of Deligne's finiteness theorem for nearby cycles (SGA 4½, [Th. finitude], Thm. 3.2),
and the base case of its proof by induction on the dimension.

The proof is a direct computation on the pro-étale site:
* `Lj^*` preserves bounded constructible complexes, and by dévissage along the truncation
  triangles (`ProEtale.boundedConstructible_obj_of_forall_singleFunctor`) it suffices to treat a
  constructible sheaf `M` on `Spec Ω` placed in degree `0`;
* such an `M` is finitely presented (`Spec Ω` is a separably closed point,
  `ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject`);
* `i^*` kills the higher direct images `Rⁿ j_* N`, `n > 0`, of every sheaf `N` on `Spec Ω`
  (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos`), so
  `Li^* Rj_* (M[0]) = (i^* j_* M)[0]`, and the long exact sequence of `Rj_*` shows that
  `i^* j_*` is exact (`ProEtale.CondensedRing.preservesFiniteColimits_traitNearbyFunctor`);
* `i^* j_*` sends `ℚ̄_ℓ` to `ℚ̄_ℓ` (`ProEtale.isIso_upperStar_traitClosedPoint_map_unit_app`),
  hence finitely presented modules to finitely presented modules, which are constructible.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (k' : Type u) [Field k'] [IsSepClosed k']

variable {ℓ : ℕ} [Fact ℓ.Prime]

namespace NearbyCyclesModel

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
