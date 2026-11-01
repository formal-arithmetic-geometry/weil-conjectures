/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
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
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The integral constant-coefficient projective-line splitting

Source: current blueprint, sk-prop-diagonal-tower-trace.proof.md, paragraph (1).
(blueprint: lem-pur-integral-p1-constant-decomposition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The strict unit/Chern splitting after integral completion, with its actual unit.

Source: current blueprint, sk-prop-diagonal-tower-trace.proof.md, paragraph (1);
steps 1--4 of lem-pur-condensed-p1-constant-decomposition.
(blueprint: lem-pur-integral-p1-constant-decomposition).

Proof: the base is Noetherian by hypothesis. Its projective line and their fibre
square are Noetherian by finite type over the base. The projective-line projection
is proper and ell is invertible by hypothesis. Use the single strict-system unit/Chern
isomorphism of the diagonal
tower trace theorem, restricted to constant Z_l scalars. Apply total derived inverse
limit; it preserves finite biproducts and shifts. The epimorphic residue tower has
limit the pulled-back condensed Z_l ring. On a compatible-root cover the negative
tower is the residue tower tensored with the dual of tateModule, and its transition
is scalar reduction, so its derived limit is that dual in degree zero. The normalized
ringed-tower direct-image comparison identifies the target with Rq_* of the integral
unit. Both summands and the target are complete, by local rank one and preservation
of completeness under direct image. Full faithfulness of complete scalar restriction
lifts the whole isomorphism. The first strict-system component is the unit; the
composition and restriction comparisons preserve its adjunct, the identity of the
pulled-back unit. The triangle identity therefore identifies the lifted component
with the actual derived unit followed by leftDerivedUpperStarUnitIso. This reasoning
uses the whole strict diagram and never infers equality of derived arrows from their
individual finite reductions. -/
theorem exists_integral_projectiveLine_constant_decomposition
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Scheme.{u}) [IsNoetherian S]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let C := Profinite.continuousMapRingObj.{u} ℤ_[ℓ]
    let M := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj C S)
    let L := (DerivedCategory.singleFunctor M 0).obj ((ihom (tateModule S ℓ)).obj (𝟙_ M))
    ∃ d : (𝟙_ (DerivedCategory M)) ⊞ (shiftFunctor _ (-2 : ℤ)).obj L ≅
        (moduleObjectDerivedPushforward C (ProjectiveLine S ↘ S)).obj (𝟙_ _),
      biprod.inl ≫ d.hom =
        (derivedUpperStarLowerStarAdjunction C (ProjectiveLine S ↘ S)).unit.app (𝟙_ _) ≫
          (moduleObjectDerivedPushforward C (ProjectiveLine S ↘ S)).map
            (leftDerivedUpperStarUnitIso C (ProjectiveLine S ↘ S)).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
