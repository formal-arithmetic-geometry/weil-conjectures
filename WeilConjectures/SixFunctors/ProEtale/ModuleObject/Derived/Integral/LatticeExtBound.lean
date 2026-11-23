/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientULift
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullback
import WeilConjectures.AlgebraicGeometry.Open.LocallyClosedExtensionConstantModelConstructible
import WeilConjectures.CategoryTheory.Integral.IntegralStratumLocallyFreeCompleteExtBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# An `Ext` bound between extensions by zero of lattices

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, `X` a noetherian scheme on
which `ℓ` is invertible, `i : Z ⟶ X` a closed immersion with open complement `j : V ⟶ X`,
`u : S ⟶ Z` an open immersion, `a = i ∘ u`, and `L₀` a locally free `𝒪_{E,S}`-module of finite
rank. For every locally closed immersion `b = i' ∘ u' : T ⟶ X` and every locally free
`𝒪_{E,T}`-module `M₀` of finite rank,

`Ext^q_{𝒪_E}(a_! L₀, b_! M₀) = 0` for `q > cd_ℓ(j) + cd_ℓ(S) + 2`

(`AlgebraicGeometry.ProEtale.CondensedRing.eq_zero_of_cohomologicalDimension_add_two_lt`).

## Implementation details

The locally closed immersion `b` is given by a factorisation `T ⟶ Z' ⟶ X` into an open immersion
followed by a closed immersion, and `b_! = i'_* u'_!`.

After restriction of scalars along `𝒪_E ≅ 𝒪_{E'}` for `E' = ULift E`, this is the case
`N = b_! M₀` of
`CategoryTheory.subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree`,
which holds for every constructible target `N`; `b_! M₀` is constructible by
`AlgebraicGeometry.ProEtale.isConstantModelConstructible_lowerStar_openImmersionLowerShriek`.
That theorem bounds `RΓ(S, L₀^∨ ⊗ u^* RΓ_Z N_n)` for the reductions `N_n` of `N` in degrees
`≤ cd_ℓ(j) + cd_ℓ(S) + 1` and passes to the derived limit over `n` by the Milnor triangle, which
costs one degree.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction of scalars along an isomorphism `φ : Λ' ≅ Λ` of coefficient rings transports
vanishing of `Hom(i_* u_! L[0], i'_* u'_! M[q])`. -/
private theorem subsingleton_hom_of_comap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ]
    {X Z S Z' T : Scheme.{u}} (i : Z ⟶ X) (u : S ⟶ Z) (i' : Z' ⟶ X) (u' : T ⟶ Z')
    [IsOpenImmersion u] [IsOpenImmersion u']
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) (q : ℤ)
    (h : Subsingleton ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ' i).obj
        ((openImmersionLowerShriek Λ' u).obj ((Mod.comap (coefficientMap φ S)).obj L))) ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ' i').obj
        ((openImmersionLowerShriek Λ' u').obj ((Mod.comap (coefficientMap φ T)).obj M)))))) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ i).obj
        ((openImmersionLowerShriek Λ u).obj L)) ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ i').obj
        ((openImmersionLowerShriek Λ u').obj M)))) := by
  let Φ := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientMap φ X)
  have : Φ.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).isEquivalence_functor
  let G := Φ.mapDerivedCategory
  have : G.IsEquivalence := Functor.isEquivalence_mapDerivedCategory _
  let a := (Φ.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((comapLowerStarIso φ i).app _ ≪≫
      (lowerStar Λ' i).mapIso ((comapOpenImmersionLowerShriekIso φ u).app L))
  let b := (G.commShiftIso q).app _ ≪≫ (shiftFunctor _ q).mapIso
    ((Φ.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso ((comapLowerStarIso φ i').app _ ≪≫
        (lowerStar Λ' i').mapIso ((comapOpenImmersionLowerShriekIso φ u').app M)))
  refine ⟨fun f g ↦ G.map_injective ?_⟩
  apply (cancel_epi a.inv).mp
  apply (cancel_mono b.hom).mp
  exact h.elim _ _

/-- Let `i : Z ⟶ X` be a closed immersion of noetherian schemes with open complement
`j : V ⟶ X`, with `ℓ` invertible on `X`, let `u : S ⟶ Z` be an open immersion, `a = i ∘ u`, and
`L₀` a locally free `𝒪_{E,S}`-module of finite rank. For every locally closed immersion
`b = i' ∘ u' : T ⟶ X` and locally free `𝒪_{E,T}`-module `M₀` of finite rank,
`Ext^q_{𝒪_E}(a_! L₀, b_! M₀) = 0` for `q > cd_ℓ(j) + cd_ℓ(S) + 2`. -/
theorem eq_zero_of_cohomologicalDimension_add_two_lt
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z V S Z' T : Scheme.{u}} [IsNoetherian X] (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] [IsOpenImmersion u] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (i' : Z' ⟶ X) (u' : T ⟶ Z') [IsClosedImmersion i'] [IsOpenImmersion u'] :
    letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType u
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    ∀ (c s : ℕ), relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c →
      cohomologicalDimension l (Fact.out : l.Prime) S ≤ s →
    ∀ (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)),
      LocallyFree (condensedRingObj A S) L₀ →
    ∀ (M₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T)),
      LocallyFree (condensedRingObj A T) M₀ →
    ∀ (q : ℤ), (c : ℤ) + s + 2 < q →
    ∀ f : (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar A i).obj ((openImmersionLowerShriek A u).obj L₀)) ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar A i').obj ((openImmersionLowerShriek A u').obj M₀))),
      f = 0 := by
  intro A c s hc hs L₀ hL₀ M₀ hM₀ q hq f
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType u
  let e : A ≅ DerivedNakayama.integerRing l (ULift.{u} E) :=
    IntegralQuotient.continuousMapRingObjIntegerRingIso.{u} l E
  have : IsMonHom e.inv := IntegralQuotient.isMonHom_continuousMapRingObjIntegerRingIso_inv l E
  apply (subsingleton_hom_of_comap e.inv i u i' u' L₀ M₀ q ?_).elim f 0
  apply subsingleton_hom_lowerStar_openImmersionLowerShriek_shift_of_isLocallyFree l
    (ULift.{u} E) X Z S V hl i u j hij c s hc hs _
    (IsLocallyFree.comap (coefficientMap e.inv S) hL₀) _ _ q hq
  exact isConstantModelConstructible_lowerStar_openImmersionLowerShriek _ i' u' _
    (IsLocallyFree.hasFiniteConstantLocalModel _
      (IsLocallyFree.comap (coefficientMap e.inv T) hM₀))

end AlgebraicGeometry.ProEtale.CondensedRing
