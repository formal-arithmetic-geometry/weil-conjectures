/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Descent of open direct image and exchange along finite radicial covers

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md
(blueprint: lem-fin-radicial-exchange-descent).

All base changes are arbitrary Cartesian presentations. The canonical module exchange
is `Etale.derivedBaseChangeMap`, retained by the recorded base-change-map dependency.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem boundedConstructible_compare
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Z : Scheme.{u})
    (K : DerivedCategoryModule Λ Z) :
    DerivedCategory.isBoundedConstructible Λ Z K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K := by
  constructor
  · rintro ⟨hc, a, b, hab, hvan⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb i
        (lt_of_le_of_lt (le_max_right _ _) hi)

private theorem cover_exchange_iso
    (Λ : Type (u + 1)) [CommRing Λ]
    {Z Z' W W' : Scheme.{u}} {f : Z ⟶ W} {f' : Z' ⟶ W'}
    {p : Z' ⟶ Z} {q : W' ⟶ W} (sq : CommSq p f' f q)
    [IsUniversalHomeomorphism p] [IsUniversalHomeomorphism q] :
    IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) p
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) q
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (L((q)^*[ModuleCat.{u + 1} Λ])) (L((p)^*[ModuleCat.{u + 1} Λ]))
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq)

private theorem finite_reflect_surjective
    (Λ : Type (u + 1)) [CommRing Λ]
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) [Surjective q]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteSheaf ((upperStar (ModuleCat.{u + 1} Λ) q).obj G)] :
    Scheme.IsFiniteSheaf G := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  constructor
  intro Ω _ _ s
  obtain ⟨z, hz⟩ := q.surjective (s (IsLocalRing.closedPoint Ω))
  let Ω' := SeparableClosure (Z'.residueField z)
  let t : Spec (.of Ω') ⟶ Z' :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z'.residueField z) Ω')) ≫
      Z'.fromSpecResidueField z
  have ht : (t ≫ q) (IsLocalRing.closedPoint Ω') = s (IsLocalRing.closedPoint Ω) := by
    change q (Z'.fromSpecResidueField z _) = _
    rw [Scheme.fromSpecResidueField_apply]
    exact hz
  obtain ⟨β, -⟩ := Scheme.exists_geometricStalkComparison_constant (Λ := Λ) s (t ≫ q) ht.symm
  have h : ConcreteCategory.IsFinitelyGenerated
      ((Scheme.pointSmallEtale t).sheafFiber.obj
        ((upperStar (ModuleCat.{u + 1} Λ) q).obj G)) :=
    Scheme.IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (F := (upperStar (ModuleCat.{u + 1} Λ) q).obj G) Ω' t
  exact (h.of_iso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) q t).app G)).of_iso
    (β.app G).symm

private theorem finiteLC_reflect_cover
    (Λ : Type (u + 1)) [CommRing Λ]
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) [IsUniversalHomeomorphism q]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf ((upperStar (ModuleCat.{u + 1} Λ) q).obj G)] :
    Scheme.IsFiniteLocallyConstantSheaf G :=
  { toIsLocallyConstantSheaf := Scheme.IsLocallyConstantSheaf.of_upperStar q G
    toIsFiniteSheaf := finite_reflect_surjective Λ q G }

private theorem exists_immersed_stratum {Z : Scheme.{u}} {s : Set Z}
    (hs : IsLocallyClosed s) :
    ∃ (D : Scheme.{u}) (ι : D ⟶ Z), IsImmersion ι ∧ Set.range ι = s := by
  obtain ⟨U, V, hU, hV, rfl⟩ := hs
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨V, hV⟩ : TopologicalSpace.Closeds Z)
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ ⟨U, hU⟩
  have hI : Set.range I.subschemeι = V := by simp [I]
  refine ⟨W, W.ι ≫ I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, hI ▸ ⟨y, rfl⟩⟩
  · rintro ⟨hxU, hxV⟩
    rw [← hI] at hxV
    obtain ⟨y, rfl⟩ := hxV
    exact ⟨y, hxU, rfl⟩

private theorem constructible_reflect_cover
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) [IsUniversalHomeomorphism q]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) q).obj G)) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  classical
  have hG' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hG
  obtain ⟨S, hS⟩ := hG'.exists_stratification
  let e := IsUniversalHomeomorphism.homeomorph q
  have hlc (i : Fin S.n) : IsLocallyClosed (q '' S.stratum i) := by
    exact (S.isLocallyClosed_stratum i).image e.isInducing
      (by rw [q.surjective.range_eq]; exact isOpen_univ.isLocallyClosed)
  choose D ι hι hr using fun i ↦ exists_immersed_stratum (hlc i)
  let T : Scheme.Stratification Z :=
    { n := S.n
      stratum := fun i ↦ q '' S.stratum i
      isLocallyClosed_stratum := hlc
      isConstructible_stratum := fun i ↦
        (S.isConstructible_stratum i).image_of_isOpenEmbedding
          e.isOpenEmbedding (by rw [q.surjective.range_eq]; exact IsRetrocompact.univ)
      iUnion_stratum_eq_univ := by
        rw [← Set.image_iUnion, S.iUnion_stratum_eq_univ, Set.image_univ, q.surjective.range_eq]
      pairwise_disjoint_stratum := fun i k hik ↦
        Set.disjoint_image_of_injective q.injective (S.pairwise_disjoint_stratum hik)
      domain := D
      immersion := ι
      isImmersion := hι
      range_immersion := hr }
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  refine ⟨T, fun i ↦ ?_⟩
  have : IsImmersion (ι i) := hι i
  let P := pullback (ι i) q
  let a : P ⟶ D i := pullback.fst (ι i) q
  let b : P ⟶ Z' := pullback.snd (ι i) q
  have hrange : Set.range b = Set.range (S.immersion i) := by
    rw [show b = pullback.snd (ι i) q from rfl, Scheme.Pullback.range_snd, hr i,
      S.range_immersion]
    exact Set.preimage_image_eq _ q.injective
  have hb : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) b).obj
        ((upperStar (ModuleCat.{u + 1} Λ) q).obj G)) := by
    have := hS i
    exact Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset b
      (S.immersion i) hrange.le _
  have hcomp : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (ι i)).obj G)) := by
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (upperStar (ModuleCat.{u + 1} Λ) b).obj
        ((upperStar (ModuleCat.{u + 1} Λ) q).obj G))
      (((upperStarComp (ModuleCat.{u + 1} Λ) b q).app G).symm ≪≫
        eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} Λ) f).obj G)
          (pullback.condition (f := ι i) (g := q)).symm) ≪≫
        (upperStarComp (ModuleCat.{u + 1} Λ) a (ι i)).app G)
  exact finiteLC_reflect_cover Λ a _

private theorem bounded_reflect_cover
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) [IsUniversalHomeomorphism q]
    (K : DerivedCategoryModule Λ Z)
    (hK : DerivedCategory.isBoundedConstructible Λ Z'
      ((L((q)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    DerivedCategory.isBoundedConstructible Λ Z K := by
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) q
  let c (i : ℤ) := (leftDerivedUpperStarHomologyFunctorIso
    (ModuleCat.{u + 1} Λ) q i).app K
  refine ⟨fun i ↦ constructible_reflect_cover Λ q _ ?_, ?_⟩
  · have hc := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hK.1 i)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso (c i).symm
        (F := (_root_.DerivedCategory.homologyFunctor _ i).obj
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj K)))
  · obtain ⟨a, b, hab, hvan⟩ := hK.2
    refine ⟨a, b, hab, fun i hi ↦ ?_⟩
    have hz := (hvan i hi).of_iso (c i)
    exact IsZero.of_full_of_faithful_of_isZero
      (upperStar (ModuleCat.{u + 1} Λ) q) _ hz

/-- Bounded constructibility and universal Noetherian exchange for an open direct image
 descend along a finite surjective radicial morphism of bases.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md
(blueprint: lem-fin-radicial-exchange-descent).

Proof:
A finite surjective radicial cover and its base changes are universal homeomorphisms.
Topological invariance and the mate lemma make the canonical cover exchange invertible.
For constructibility reflection, transport a finite constructible stratification through
its homeomorphism. Realize each image stratum by an actual immersed scheme. Pull it back
to the cover, use immersion independence there, then descend local constancy. Finite
stalks descend along any surjective morphism: choose a geometric point over a point
upstairs and compare its composite stalk with the given stalk over the same image.
Exact inverse image commutes with cohomology and reflects zero objects, hence reflects
the cohomological bounds as well. Apply this to the cover exchange to prove the global
bounded-constructibility conclusion, including on non-Noetherian bases.

For exchange on Noetherian tests use the already stated source-library theorem
`HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`
(blueprint dependency: lem-fin-radicial-noetherian-test-descent). Its hypothesis is only
about Noetherian tests: derive the tested boundedness from `hbounded` by pullback and
`hexchange`, using the single-complex/pullback comparison. Apply the source descent
and project its exchange clause. That source theorem does not assert global boundedness
on a non-Noetherian base; the separate argument above supplies it.
-/
theorem finite_radicial_exchange_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S S' X Y : Scheme.{u}} (v : S' ⟶ S)
    [IsFinite v] [Surjective v] [UniversallyInjective v]
    (aX : X ⟶ S) (aY : Y ⟶ S)
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    {X' Y' : Scheme.{u}} (pX : X' ⟶ X) (pY : Y' ⟶ Y)
    (bY : Y' ⟶ S') (j' : X' ⟶ Y')
    (hY : IsPullback pY bY aY v) (hX : IsPullback pX j' j pY)
    (hbounded : DerivedCategory.isBoundedConstructible Λ Y'
      ((R((j')_*[ModuleCat.{u + 1} Λ])).obj
        ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (hexchange : ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S')
      (XT YT : Scheme.{u}) (qX : XT ⟶ X') (qY : YT ⟶ Y')
      (bT : YT ⟶ T) (jT : XT ⟶ YT),
      IsPullback qY bT bY t → ∀ sq : IsPullback qX jT j' qY,
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) :
    DerivedCategory.isBoundedConstructible Λ Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S)
      (XT YT : Scheme.{u}) (qX : XT ⟶ X) (qY : YT ⟶ Y)
      (bT : YT ⟶ T) (jT : XT ⟶ YT),
      IsPullback qY bT aY t → ∀ sq : IsPullback qX jT j qY,
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  have _ := hj
  have _ := hF
  have hbounded' := (boundedConstructible_compare Λ Y' _).mp hbounded
  let F' := (upperStar (ModuleCat.{u + 1} Λ) pX).obj F
  let e := (singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} Λ) pX).app F
  have hup : HasConstructibleDirectImageBaseChangeOn Λ bY j' F' Set.univ := by
    intro T hT t ht YT XT qY bT qX jT hqY sq
    have he := hexchange T t XT YT qX qY bT jT hqY sq
    have hi : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        sq.toCommSq).app ((_root_.DerivedCategory.singleFunctor _ 0).obj F')) :=
      (NatTrans.isIso_app_iff_of_iso _ e).mp he
    refine ⟨?_, hi⟩
    apply ObjectProperty.prop_of_iso _
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F')))
    apply boundedConstructible_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) qY
    exact ObjectProperty.prop_of_iso _ ((R((j')_*[ModuleCat.{u + 1} Λ])).mapIso e)
      hbounded'
  have hdown := HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective
    Λ v aY j pY bY hY pX j' hX F hup
  refine ⟨?_, ?_⟩
  · have : IsUniversalHomeomorphism v := {}
    have : IsUniversalHomeomorphism pY :=
      MorphismProperty.of_isPullback hY.flip inferInstance
    have : IsUniversalHomeomorphism pX :=
      MorphismProperty.of_isPullback hX.flip inferInstance
    have := cover_exchange_iso Λ hX.toCommSq
    apply bounded_reflect_cover Λ pY
    apply (boundedConstructible_compare Λ Y' _).mpr
    exact ObjectProperty.prop_of_iso _
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) hX.toCommSq).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).symm hbounded'
  · intro T hT t XT YT qX qY bT jT hqY sq
    exact (hdown T t (Set.subset_univ _) YT XT qY bT qX jT hqY sq).2

end AlgebraicGeometry.Etale
