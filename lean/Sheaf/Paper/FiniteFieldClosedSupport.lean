/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.Data.Int.Interval

/-! # Finite-field closed-support constructibility

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.11,
closed-immersion support-triangle proof, specialized to R = A and m = 0
(blueprint: lem-sfb-finite-field-closed-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private abbrev intrinsicBC (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) := fun K ↦
  Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
    (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)} ∧
  ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
    ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj K)

private theorem finite_homology_support_iff
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
  · rintro ⟨a, b, _, h⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun hia ↦ hi (h i (Or.inl hia))),
      le_of_not_gt (fun hbi ↦ hi (h i (Or.inr hbi)))⟩

private theorem etaleBC_iff (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X K ↔
      Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K := by
  constructor
  · rintro ⟨hc, a, b, _, hv⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 ?_⟩⟩, ?_⟩
    · exact fun i hi ↦ hv i (Or.inl hi)
    · exact fun i hi ↦ hv i (Or.inr hi)
    · exact fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).mp ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).mp hb i (lt_of_le_of_lt (le_max_right _ _) hi)

private theorem realizationBC_iff (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    intrinsicBC X A ((sfIntrinsicDerivedEquivalence X A).functor.obj K) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K := by
  let R := (sfIntrinsicModuleEquivalence X A).functor
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  have h := (finiteRing_constructibleDerived_origin X A).2.2.1
  constructor
  · rintro ⟨hb, hc⟩
    obtain ⟨G, ⟨e⟩⟩ := (h _).mpr ⟨hc, (finite_homology_support_iff _).mp hb⟩
    refine ⟨G.obj, (etaleBC_iff X A G.obj).mp G.property, ⟨?_⟩⟩
    exact R.mapDerivedCategory.preimageIso
      ((Functor.mapDerivedCategoryCompIso C R).symm.app G.obj ≪≫ e)
  · rintro ⟨G, hG, ⟨e⟩⟩
    have he : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).essImage
        ((sfIntrinsicDerivedEquivalence X A).functor.obj K) :=
      ⟨⟨G, (etaleBC_iff X A G).mpr hG⟩,
        ⟨(Functor.mapDerivedCategoryCompIso C R).app G ≪≫
          R.mapDerivedCategory.mapIso e⟩⟩
    obtain ⟨hc, hb⟩ := (h _).mp he
    exact ⟨(finite_homology_support_iff _).mpr hb, hc⟩

private noncomputable def constantDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A ≅ proEtaleConstantModuleDirectImage f A := by
  have := constantComparison_isIso f A
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
  rw [show proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (sfConstantCoefficientIso f A) =
        proEtaleCoefficientDirectImageMap f A from
      proEtaleConstantModulePullback_ring_direct f A]
  exact Iso.refl _

/-- The ambient closed exceptional inverse image preserves bounded constructible
cohomology for finite-field coefficients prime to the positive characteristic.
The complementary open is the actual open subscheme with underlying set
`(Set.range g)ᶜ`. The ordinary right derived functor is precisely the one in
`sfIntrinsicClosedAmbientAdjunction`; no completed or restricted category is used.
Source: Bhatt--Scholze, Lemma 6.7.11, closed-immersion proof, R = A and m = 0
(blueprint: lem-sfb-finite-field-closed-support).

Proof:
1. The finite-type target is Noetherian, so its actual complementary open immersion `j` is
quasi-compact. Its image is complementary to that of `g`.
2. Under `sfIntrinsicDerivedEquivalence`, intrinsic bounded constructibility is equivalent to
the fixed-module predicate of étale origin. Indeed, finite cohomological support is equivalent
to vanishing outside an integer interval. The finite-ring derived-origin criterion identifies
the intrinsic predicate with the essential image of bounded constructible étale complexes.
The étale constructibility comparison and the standard derived t-structure identify the two
étale predicates. Cancel the fully faithful intrinsic realization to obtain the equivalence.
3. Normalize the intrinsic closed direct image by the adjoint constant-ring map. Its derived
comparison commutes the realization equivalences with fixed-module direct image. Compose
both closed ambient adjunctions with the realization adjunctions; uniqueness of right adjoints
then identifies intrinsic `Rg!` with fixed-module `Rg!` under those equivalences.
4. Apply the already formalized closed-support argument
`ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj` from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible`,
with coefficient ring `ULift A` and annihilator `ℓ`. The scalar `ℓ` is nonzero in `k` because
`ℓ` is prime and `p ≠ ℓ`, and it vanishes in `ULift A`. This existing proof is exactly the
support-triangle argument of the source: the open direct-image term is bounded constructible,
so the closed-support term is too, and closed pullback recovers the exceptional inverse image.
Finally use steps 2 and 3 and isomorphism invariance to obtain the stated intrinsic conclusion.
No separatedness or bound on the absolute cohomological dimension of `k` is used. The integer
interval conversion also covers zero complexes, so empty schemes require no extra assumption.
-/
theorem finiteFieldClosedSupport_bounded_constructible
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (A : Type u) [Field A] [Finite A] [CharP A ℓ]
    {Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (g : Z ⟶ T) [IsClosedImmersion g] [g.IsOver (Spec (.of k))]
    (K : proEtaleDerivedCategory T A)
    (_hK : Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)} ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) :
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Z (proEtaleConstantRing Z A)) q).obj
        ((sfIntrinsicClosedUpperShriek g
          (Scheme.Opens.ι
            (⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : T.Opens))
          A).rightDerivedFunctor.obj K))} ∧
    ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf Z A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Z (proEtaleConstantRing Z A)) q).obj
          ((sfIntrinsicClosedUpperShriek g
            (Scheme.Opens.ι
            (⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : T.Opens))
            A).rightDerivedFunctor.obj K)) := by
  classical
  let U : T.Opens := ⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := U.ι
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have : IsNoetherian T := {}
  have : QuasiCompact j := inferInstance
  have hij : IsCompl (Set.range g.base) (Set.range j.base) := by
    rw [show Set.range j.base = (Set.range g.base)ᶜ from U.range_ι]
    exact isCompl_compl
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let ET := sfIntrinsicDerivedEquivalence T A
  let P := (sfConstantModuleDirectImage g A).rightDerivedFunctor
  let H := (sfIntrinsicClosedUpperShriek g j A).rightDerivedFunctor
  let F := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor
  let G := (ProEtale.closedUpperShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g j).rightDerivedFunctor
  let a : P ⊣ H := (sfIntrinsicClosedAmbientAdjunction A g j hij).2.some
  let b : F ⊣ G := ProEtale.derivedLowerStarClosedUpperShriekAdjunction g j hij
  let e : EZ.functor ⋙ P ≅ F ⋙ ET.functor :=
    Functor.isoWhiskerLeft EZ.functor (Functor.rightDerivedFunctorNatIso
      (constantDirectIso g A)) ≪≫ sfIntrinsicDerivedDirectImageComparison g A
  let r : H ⋙ EZ.inverse ≅ ET.inverse ⋙ G :=
    (EZ.toAdjunction.comp a).rightAdjointUniq
      ((b.comp ET.toAdjunction).ofNatIsoLeft e.symm)
  have htri := proEtale_bounded_constructible_isTriangulated T A
  have : (intrinsicBC T A).IsClosedUnderIsomorphisms := htri.1
  have : (intrinsicBC Z A).IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated Z A).1
  have hK' : intrinsicBC T A (ET.functor.obj (ET.inverse.obj K)) :=
    (intrinsicBC T A).prop_of_iso (ET.counitIso.app K).symm _hK
  have hfixed := (realizationBC_iff T A (ET.inverse.obj K)).mp hK'
  have hellk : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) _hpℓ
  have hG : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z (G.obj (ET.inverse.obj K)) :=
    ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj g j
      ℓ hellk (CharP.cast_eq_zero (ULift.{u + 1, u} A) ℓ) (T ↘ Spec (.of k)) hij hfixed
  have hresult := (realizationBC_iff Z A (G.obj (ET.inverse.obj K))).mpr hG
  exact (intrinsicBC Z A).prop_of_iso
    ((EZ.counitIso.app (H.obj K)).symm ≪≫ EZ.functor.mapIso (r.app K)).symm hresult

end AlgebraicGeometry.Scheme

