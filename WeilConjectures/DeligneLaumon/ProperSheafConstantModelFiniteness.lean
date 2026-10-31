/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# Proper higher images retain finite constant models

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Sections 6.7--6.8,
Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15 (blueprint:
lem-dla1-proper-sheaf-constant-model-finiteness).

The statement records proper direct-image finiteness for the two native coefficient
objects used here: a finite extension of `ℚ_[ℓ]` and the finite-subextension-valued
algebraic closure object. The proof is postponed to the proper constructibility
argument and the comparison of constructibility predicates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper higher images of a finite-constant-model module have finite constant models.
Source: Bhatt--Scholze, Sections 6.7--6.8, Lemma 6.7.2, Proposition 6.8.14 and
Remark 6.8.15 (blueprint: lem-dla1-proper-sheaf-constant-model-finiteness).

The first conjunct is the finite-extension coefficient case and the second is the
finite-subextension-valued algebraic-closure case. In each case the input is placed
in degree zero using `DerivedCategory.singleFunctor`; the conclusion is required for
every integer cohomological degree of the ordinary total derived pushforward.

Proof:
1. `Spec k` is Noetherian since `k` is a field; `aZ` and `aY` are of finite type, so `Z`
   and `Y` are Noetherian (lem-weil-pbc-finite-type-over-noetherian). Both coefficient
   objects are covered by the proper direct-image finiteness theorem used in step 3.
2. `M[0]` has cohomology `M` in degree zero and zero elsewhere, so it is bounded. On the
   Noetherian scheme `Z`, `adicConstructibilityPredicateComparison`
   (lem-sfb-adic-constructibility-predicate-comparison) identifies the finite constant
   model predicate with stratified local finite presentation for `E` and for `Ω`.
3. Apply the proper constructibility theorem
   (lem-sfb-noetherian-proper-constructible-cohomology:
   `properLowerStar_constructible_cohomology_ellAdic_continuousMapRingObj` and
   `properLowerStar_constructible_cohomology_ellAdic_padicAlgClRingObj`) to `p` and `M[0]`:
   every `H^q(Rp_*M[0])`, `q : ℤ`, is constructible in the stratified local finite
   presentation sense on `Y`.
4. The same comparison on the Noetherian scheme `Y` turns this back into a finite
   constant local model on a finite constructible stratification, for every `q`.
-/
theorem properHigherImagesRetainFiniteConstantModels
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] (hp : p ≫ aY = aZ) :
    (∀ (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
        [FiniteDimensional ℚ_[ℓ] E]
        (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Z)),
        IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E) Z M →
          ∀ q : ℤ, IsConstantModelConstructible
            (Profinite.continuousMapRingObj.{u} E) Y
            ((DerivedCategory.homologyFunctor _ q).obj
              (R((p)_*⟦Profinite.continuousMapRingObj.{u} E⟧).obj
                ((DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z)),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Z M →
        ∀ q : ℤ, IsConstantModelConstructible
          (Profinite.padicAlgClRingObj.{u} ℓ) Y
          ((DerivedCategory.homologyFunctor _ q).obj
            (R((p)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  clear hp
  constructor
  · intro E _ _ _ M hM q
    have hZ := (adicConstructibilityPredicateComparison ℓ Z
      (Profinite.continuousMapRingObj E) (.continuous E)).1 M
    have hY := (adicConstructibilityPredicateComparison ℓ Y
      (Profinite.continuousMapRingObj E) (.continuous E)).1
    have hK : boundedConstructible (condensedRingObj
        (Profinite.continuousMapRingObj E) Z)
        ((DerivedCategory.singleFunctor _ 0).obj M) :=
      boundedConstructible_singleFunctor_zero_obj _ _ (hZ.mpr hM)
    exact (hY _).mp
      (properLowerStar_constructible_cohomology_ellAdic_continuousMapRingObj
        ℓ E aY p _ hK q)
  · intro M hM q
    have hZ := (adicConstructibilityPredicateComparison ℓ Z
      (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).1 M
    have hY := (adicConstructibilityPredicateComparison ℓ Y
      (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).1
    have hK : boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) Z)
        ((DerivedCategory.singleFunctor _ 0).obj M) :=
      boundedConstructible_singleFunctor_zero_obj _ _ (hZ.mpr hM)
    exact (hY _).mp
      (properLowerStar_constructible_cohomology_ellAdic_padicAlgClRingObj
        ℓ aY p _ hK q)

end AlgebraicGeometry.ProEtale.CondensedRing
