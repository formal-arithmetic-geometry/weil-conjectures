/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# Acyclicity of open extensions in proper commutative squares

## References

* Stacks Project, More on Etale Cohomology, Tag 0F7B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Positive integral degrees reduce to classical injective acyclicity (Stacks 05TH).
private theorem injective_vanishing
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] (f : X ⟶ Y)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj J))) := by
  lift q to ℕ using le_of_lt hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact (Functor.isZero_rightDerived_obj_injective_succ
    (lowerStar (ModuleCat.{u + 1} Λ) f) n J).of_iso
    (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (lowerStar (ModuleCat.{u + 1} Λ) f) J (n + 1))

-- Proper base change and exact inverse image give the degreewise comparison (Stacks 095T).
private noncomputable def proper_homology_baseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f] (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
    (DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f').obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F))) := by
  have := isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
    (isAddTorsion_of_finite : IsAddTorsion Λ) sq
  rw [baseChange_eq_derivedBaseChangeMapPlus] at this
  exact ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f').mapIso
        (((upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlusSingleFunctor 0).app F))

/-- In a commutative square with open horizontal maps and proper vertical maps,
the extension by zero of an injective etale module sheaf is acyclic for the
right vertical direct image. No Cartesian hypothesis is required. (Stacks, Tag 0F7B) -/
theorem isZero_higherDirectImage_openImmersionLowerShriek_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
    (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (hcomm : k ≫ p = r ≫ i)
    (J : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J)))) := by
  -- The source is a clopen component of the restriction of B over C.
  let V := pullback p i
  let b : V ⟶ B := pullback.fst p i
  let s : V ⟶ C := pullback.snd p i
  let t : A ⟶ V := pullback.lift k r hcomm
  have ht : t ≫ b = k := pullback.lift_fst _ _ _
  have hts : t ≫ s = r := pullback.lift_snd _ _ _
  have : IsOpenImmersion b := inferInstance
  have : IsOpenImmersion (t ≫ b) := ht.symm ▸ inferInstance
  have : IsOpenImmersion t := IsOpenImmersion.of_comp t b
  have : IsProper s := inferInstance
  have : IsProper (t ≫ s) := hts.symm ▸ inferInstance
  have : IsProper t := IsProper.of_comp t s
  have hclosed : IsClosed (Set.range t.base) := t.isClosedMap.isClosed_range
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) t hclosed
  have : (lowerStar (ModuleCat.{u + 1} Λ) t).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t)
  let Jv := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) t).obj J
  have : Injective Jv :=
    Injective.of_iso
      (asIso ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) t).app J)).symm
      inferInstance
  let F := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J
  have eF : (upperStar (ModuleCat.{u + 1} Λ) b).obj F ≅ Jv := by
    have e : F ≅ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).obj Jv := by
      dsimp only [F, Jv]
      simpa only [ht, Functor.comp_obj] using
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) t b).app J
    exact (upperStar (ModuleCat.{u + 1} Λ) b).mapIso e ≪≫
      (asIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) b).unit.app Jv)).symm
  -- Over C, extension by zero is injective and proper base change applies.
  have hC : IsZero ((upperStar (ModuleCat.{u + 1} Λ) i).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
    exact (injective_vanishing Λ s Jv q hq).of_iso
      (proper_homology_baseChange Λ (IsPullback.of_hasPullback p i) F q ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) s).mapIso
            ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)))
  -- Over the complement, the geometric fibre is disjoint from the support.
  apply isZero_of_forall_isZero_upperStar_algClosurePoint Λ
  intro d
  let x := D.algClosurePoint d
  by_cases hx : x.base (IsLocalRing.closedPoint _) ∈ Set.range i.base
  · let y := IsOpenImmersion.lift i x (Scheme.range_base_subset_of_closedPoint_mem x hx)
    exact ((upperStar (ModuleCat.{u + 1} Λ) y).map_isZero hC).of_iso
      ((upperStarComp (ModuleCat.{u + 1} Λ) y i x
        (IsOpenImmersion.lift_fac _ _ _).symm).app _)
  · have hdisj := disjoint_range_of_closedPoint_not_mem i x hx
    have hdisj' : Disjoint (Set.range k.base) (Set.range (pullback.fst p x).base) := by
      rw [Set.disjoint_iff]
      rintro _ ⟨⟨a, rfl⟩, ⟨v, hv⟩⟩
      refine hdisj.ne_of_mem ⟨r.base a, rfl⟩ ⟨(pullback.snd p x).base v, rfl⟩ ?_
      rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, ← hv,
        ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hz := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
      (ModuleCat.{u + 1} Λ) k (pullback.fst p x) hdisj' J
    have : Injective ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p x)).obj F) :=
      hz.injective
    exact (injective_vanishing Λ (pullback.snd p x) _ q hq).of_iso
      (proper_homology_baseChange Λ (IsPullback.of_hasPullback p x) F q)

end AlgebraicGeometry.Etale
