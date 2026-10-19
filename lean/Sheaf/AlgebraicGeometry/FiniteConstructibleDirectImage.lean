/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import Sheaf.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Finite direct images of constructible module sheaves

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-morphism.md`,
order 1580 (blueprint: lem-fin-finite-morphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a finite morphism with target of finite type over a field, direct image preserves
constructible module sheaves and its positive higher direct images vanish.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-morphism.md`, order 1580
(blueprint: lem-fin-finite-morphism).

Proof:
1. The coefficient convention makes Λ finite. Since Spec k is Noetherian, the finite
   type structure morphism makes S Noetherian.
2. Forget F to abelian groups and then sets using
   `isConstructibleEtaleSheafOfSets_of_module`. Apply the Noetherian finite-pushforward
   constructibility theorem to its underlying abelian sheaf. Direct image is
   precomposition, so its underlying set sheaf is definitionally that of f_*F.
3. Apply `isConstructibleSheaf_of_finite_coefficient_underlying_sets` with the zero
   ideal. The quotient Λ/0 is finite by surjectivity of the quotient map, and the zero
   ideal annihilates every section. Convert the resulting module constructibility
   with `isConstructibleEtaleModuleSheaf_iff`.
4. The finite-direct-image exactness instance applies directly to ModuleCat Λ.
   Its bounded below right derived functor is therefore its levelwise derived functor,
   which commutes with homology. The degree-q homology of F[0] is zero for q > 0;
   applying f_* preserves this zero object, and the comparison isomorphisms give
   the required vanishing. -/
theorem finite_directImage_constructible_and_higher_vanishing
    (k : Type u) [Field k] {X S : Scheme.{u}}
    [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsFinite f] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ∧
    ∀ q : ℤ, 0 < q → IsZero
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have : Finite Λ := hcoeff.2.1
  have : IsNoetherian S := isNoetherian_of_locallyOfFiniteType (S ↘ Spec (.of k))
  constructor
  · apply (Scheme.isConstructibleEtaleModuleSheaf_iff _).mpr
    have hsets := Scheme.isConstructibleEtaleSheafOfSets_of_module Λ F hF
    let E := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    have hpush := Scheme.isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian f E hsets
    refine Scheme.isConstructibleSheaf_of_finite_coefficient_underlying_sets Λ _
      hpush ⊥ (Finite.of_surjective (Ideal.Quotient.mk ⊥) Ideal.Quotient.mk_surjective) ?_
    intro U r hr m
    have : r = 0 := hr
    subst r
    exact zero_smul Λ m
  · intro q hq
    let G := lowerStar (ModuleCat.{u + 1} Λ) f
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    have hz := DerivedCategory.Plus.isZero_homology_of_isLE K 0 q hq
    let e := (G.mapDerivedCategoryPlusHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app K).symm
    exact (G.map_isZero hz).of_iso e.symm

end AlgebraicGeometry.Etale
