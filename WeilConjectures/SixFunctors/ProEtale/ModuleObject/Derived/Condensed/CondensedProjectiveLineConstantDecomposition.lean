/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import Mathlib.Algebra.CharP.Invertible
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedInverseTateScalarComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProjectiveLineConstantDecomposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedProjectiveLineScalarEndpoints
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Constant condensed coefficients on the relative projective line

Source: current blueprint, sec-six-functors-basics/sk-lem-geo-p1-cohomology,
thm-amb-p1-decomposition.proof.md, constant-coefficient calculation and its
strict-tower extension in sk-prop-diagonal-tower-trace.proof.md, paragraph (1).
(blueprint: lem-pur-condensed-p1-constant-decomposition)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 1000000 in
-- The endpoint types contain several independently specified derived functors.
/-- The relative projective-line decomposition for the pulled-back finite-subextension-valued
condensed algebraic closure, in the ordinary uncompleted module derived category.
The first summand is the actual derived-adjunction unit, followed by direct image of
the canonical identification of the pulled-back coefficient unit.

Source: current blueprint, thm-amb-p1-decomposition.proof.md, constant-coefficient
calculation, and sk-prop-diagonal-tower-trace.proof.md, paragraph (1).
(blueprint: lem-pur-condensed-p1-constant-decomposition).

Proof: finite type over the field makes S Noetherian. The distinct primes make
ell a unit in the field and hence in the global sections of S. Obtain the integral
unit-plus-dual-line isomorphism from the strict-system calculation. Extend its
coefficients by the actual integral-to-algebraic-closure map. The inverse-Tate scalar
comparison identifies the shifted internal dual. The scalar endpoint theorem identifies
the direct image with the required unit square.
Derived scalar extension is additive by its adjunction to exact restriction, so it
preserves this biproduct.
Conjugate its image of the integral isomorphism by the three endpoint isomorphisms.
The first-inclusion formula for the biproduct comparison reduces its first component
to the image of the integral first component. Substitute the two unit equations
and cancel the source unit isomorphism. The result is precisely the displayed
adjunction unit, with the specified left-derived upper-star unit comparison.
-/
theorem exists_condensed_projectiveLine_constant_decomposition
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (S : Scheme.{u}) (s : S ⟶ Spec (CommRingCat.of k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s] :
    ∃ d :
      (𝟙_ (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))) ⊞
        (shiftFunctor _ (-2 : ℤ)).obj (tateTwistDerived S ℓ (-1)) ≅
      (moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ)
        (ProjectiveLine S ↘ S)).obj (𝟙_ _),
      biprod.inl ≫ d.hom =
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
          (ProjectiveLine S ↘ S)).unit.app (𝟙_ _) ≫
        (moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ)
          (ProjectiveLine S ↘ S)).map
          (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ)
            (ProjectiveLine S ↘ S)).hom := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian S := ⟨⟩
  have hℓk : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓp.symm)
  have hℓS : IsUnit (ℓ : Γ(S, ⊤)) := by
    simpa only [map_natCast] using
      hℓk.map (s.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  let C := Profinite.continuousMapRingObj.{u} ℤ_[ℓ]
  let M := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj C S)
  let a := coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S
  let E := Mod.extendScalars a
  let F := E.leftDerivedFunctor
  have : E.Monoidal := Mod.extendScalarsMonoidal a
  have : F.Monoidal := E.leftDerivedFunctorMonoidal
  let u : F.obj (𝟙_ (DerivedCategory M)) ≅ 𝟙_ _ := (Functor.Monoidal.εIso F).symm
  obtain ⟨d, hd⟩ := exists_integral_projectiveLine_constant_decomposition
    ℓ S hℓS
  obtain ⟨v⟩ := exists_condensed_inverse_tate_scalar_comparison ℓ S hℓS
  obtain ⟨e, he⟩ := condensed_projectiveLine_scalar_endpoints ℓ S u
  have : F.Additive :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S)).left_adjoint_additive
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  let D := (biprod.mapIso u.symm v.symm) ≪≫ (F.mapBiprod (𝟙_ _) _).symm ≪≫
    F.mapIso d ≪≫ e
  refine ⟨D, ?_⟩
  change biprod.inl ≫ biprod.map u.inv v.inv ≫ (F.mapBiprod (𝟙_ _) _).inv ≫
    F.map d.hom ≫ e.hom = _
  rw [biprod.inl_map_assoc, Functor.mapBiprod_inv, biprod.inl_desc_assoc,
    ← F.map_comp_assoc, hd, he]
  simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
