/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom

/-!
# Global derived Hom out of sheaves supported on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X` and let `RΓ_Z` be the
derived functor of sections with support in `Z`. Global derived Hom is
`RHom_X(A, K) = RΓ(X, RHom(A, K))`.

* `ProEtale.CondensedRing.formalClosedSupport_globalDerivedHom_lowerStar`: naturally in `K`,
  `RHom_X(i_*N, K) ≅ RHom_Z(N, RΓ_Z K)` (blueprint `lemma-sections-support-closed-subscheme--2`).
* `ProEtale.CondensedRing.formalClosedSupport_globalDerivedHom_lowerShriek`: for an open
  immersion `u : S ⟶ Z` and a finite locally projective `Λ_S`-module `L`, naturally in `K`,
  `RHom_X(i_*u_!L, K) ≅ RΓ(S, L^∨ ⊗ u^*RΓ_Z K)`
  (blueprint `lemma-sections-support-closed-subscheme--3`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Derived adjunction for sections with closed support, in `RHom` form.** For a closed
immersion `i : Z ⟶ X` with quasi-compact open complement `j : U ⟶ X` and `N ∈ D(Z_proét, Λ)`,
there is an isomorphism `RHom_X(i_*N, K) ≅ RHom_Z(N, RΓ_Z K)` natural in `K ∈ D(X_proét, Λ)`.
Here global derived Hom is `RΓ(-, RHom(-, -))`, with `RΓ` the right derived functor of global
sections.
(blueprint: lemma-sections-support-closed-subscheme--2) -/
theorem formalClosedSupport_globalDerivedHom_lowerStar {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (N : DerivedCategory (FormalSupportModules Λ Z)) :
    Nonempty ((derivedHom Λ X).obj (op ((lowerStar Λ i).rightDerivedFunctor.obj N)) ⋙
        (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
      (formalClosedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op N) ⋙
        (formalClosedSupportSections Λ Z).rightDerivedFunctor) := by
  classical
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  let := closedSupport_lowerStarExact Λ i j hij
  obtain ⟨_, _, a, -⟩ := formal_closed_support_adjunction Λ i j hji
  obtain ⟨_, _, c, _, _, _, _, hc⟩ := openClosedInternalHomFormulas Λ i j hij
  let eH : (derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj N)) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op N) ⋙
        (lowerStar Λ i).mapDerivedCategory := NatIso.ofComponents (c N) (by
    intro K K' f
    have h := hc N N K K' (𝟙 N) f
    rw [(lowerStar Λ i).mapDerivedCategory.map_id, op_id, (derivedHom Λ X).map_id,
      NatTrans.id_app, Category.id_comp, op_id, (derivedHom Λ Z).map_id,
      NatTrans.id_app, Category.id_comp] at h
    exact h)
  have : (lowerStar Λ i).PreservesKInjectiveComplexes :=
    (formalSupportPullbackAdjunction Λ i).preservesKInjectiveComplexes
  let eΓ : lowerStar Λ i ⋙ formalClosedSupportSections Λ X ≅ formalClosedSupportSections Λ Z :=
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Z))
      (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} i)
  let eS : (lowerStar Λ i).rightDerivedFunctor ⋙
      (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
      (formalClosedSupportSections Λ Z).rightDerivedFunctor :=
    Functor.rightDerivedFunctorCompIso' _ _ eΓ
  let eM := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  let eC : (formalClosedSupport Λ i j).rightDerivedFunctor ≅
      (closedSupport Λ i j).rightDerivedFunctor :=
    a.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq
      (closedSupportDerivedAdjunction Λ i j hij)
  exact ⟨Functor.isoWhiskerRight ((derivedHom Λ X).mapIso (eM.app N).symm.op ≪≫ eH)
      (formalClosedSupportSections Λ X).rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft ((closedSupport Λ i j).rightDerivedFunctor ⋙
      (derivedHom Λ Z).obj (op N)) (Functor.isoWhiskerRight eM.symm _ ≪≫ eS) ≪≫
    Functor.isoWhiskerRight eC.symm
      ((derivedHom Λ Z).obj (op N) ⋙ (formalClosedSupportSections Λ Z).rightDerivedFunctor)⟩

/-- **Global derived Hom out of a stratum extension.** Let `X` be separated of finite type over
a field `k` of characteristic `p ≠ ℓ`, let `i : Z ⟶ X` be a closed immersion with open
complement `j`, let `u : S ⟶ Z` be an open immersion and let `L` be a finite locally projective
`Λ_S`-module (pro-étale locally a direct summand of a finite free module), with dual
`L^∨ = Hom(L, Λ_S)`. Then, naturally in `K ∈ D(X_proét, Λ)`, for `a = i ∘ u`,
`RHom_X(a_!L, K) ≅ RΓ(S, L^∨ ⊗ u^*RΓ_Z K)`.
(blueprint: lemma-sections-support-closed-subscheme--3) -/
theorem formalClosedSupport_globalDerivedHom_lowerShriek (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {S : Scheme.{u}} (u : S ⟶ Z) [IsOpenImmersion u] (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ,
        Nonempty (Retract ((formalSupportPullback Λ (𝒰.f c)).obj L)
          (Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n))) :
    Nonempty
      ((derivedHom Λ X).obj
          (op ((DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0).obj
            ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ u).obj L)))) ⋙
          (formalClosedSupportSections Λ X).rightDerivedFunctor ≅
        (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
          (formalSupportPullback Λ u).mapDerivedCategory ⋙
          (derivedTensor Λ S).obj
            ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj
              ((ihom L).obj (𝟙_ (FormalSupportModules Λ S)))) ⋙
          (formalClosedSupportSections Λ S).rightDerivedFunctor) :=
  (formalClosedSupportAssertions Λ ℓ k p hpℓ i j hij).some.stratum u L hL

end AlgebraicGeometry.ProEtale.CondensedRing
