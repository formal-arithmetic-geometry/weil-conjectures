/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.AlgebraicGeometry.CartesianStratumModuleRestriction
import WeilConjectures.AlgebraicGeometry.SfClosedPartitionModuleTest
import WeilConjectures.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleClosedEssentialImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite-stage immersion constructibility and unchanged cohomological intervals

Source: main-20261015, proof of prop-sf-open-closed-triangle-all-stages, finite-stage
paragraph; Stacks Tags 09AA, 09BM, 09AH, 093R and 015F
(blueprint: lem-sf-finite-immersion-constructibility-interval).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The restriction clause of a constructibility witness, using the existing local
constancy and geometric stalk definitions. This merely names the clause for a supplied
immersion, without choosing or changing its domain.
Source: finite-stage paragraph of prop-sf-open-closed-triangle-all-stages; Stacks 093R
(blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionStratum (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (s : S ⟶ X) (M : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf S A (proEtaleConstantModulePullback s A M) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
      Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing S A)
        (proEtaleConstantModulePullback s A M))

/-- All the assertions about one of the three specified ordinary operations: exactness,
triangulated termwise descent, natural cohomology comparison, bounded constructibility,
and preservation of each identical interval. The predicates `P` and `Q` will be the
recorded intrinsic bounded-constructibility predicates at the same coefficient level.
Source: finite-stage paragraph of prop-sf-open-closed-triangle-all-stages; Stacks 015F
(blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionAction (A : Type u) [CommRing A] (X Y : Scheme.{u})
    (P : ObjectProperty (proEtaleDerivedCategory X A))
    (Q : ObjectProperty (proEtaleDerivedCategory Y A))
    (F : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A)) [F.Additive]
    (DF : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A)
    [DF.CommShift ℤ] : Prop :=
  PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧ DF.IsTriangulated ∧
    Nonempty (DerivedCategory.Q ⋙ DF ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    (∀ r : ℤ, Nonempty (DF ⋙ DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) r ≅
        DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) r ⋙ F)) ∧
    (∀ C, P C → Q (DF.obj C)) ∧
    ∀ (a b : ℤ) (C : proEtaleDerivedCategory X A),
      proEtaleCohomologicalSupport C ⊆ Set.Icc a b →
        proEtaleCohomologicalSupport (DF.obj C) ⊆ Set.Icc a b

/-- The actual fibre-product partition of a supplied constructibility witness still
witnesses constructibility after inverse image. `Stratification.pullback` retains the
index set and uses the schemes `S.domain ν ×[X] Y` with their second projections.
Source: finite-stage paragraph of prop-sf-open-closed-triangle-all-stages; Stacks 093R
(blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionPullbackPartitions (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (S : Stratification X),
    (∀ ν : Fin S.n, sfFiniteImmersionStratum A (S.immersion ν) M) →
      ∀ ν : Fin (S.pullback g).n,
        sfFiniteImmersionStratum A ((S.pullback g).immersion ν)
          (proEtaleConstantModulePullback g A M)

/-- Extend a given closed-side partition by precisely the complementary open scheme.
The equivalence of indices and the isomorphisms over `X` specify every domain, including
its scheme structure. The last two clauses identify the restrictions with the original
ones and zero, respectively. Empty strata are allowed.
Source: finite-stage paragraph of prop-sf-open-closed-triangle-all-stages; Stacks 09AA
(blueprint: lem-sf-finite-immersion-constructibility-interval). -/
def sfFiniteImmersionClosedPartitions (A : Type u) [CommRing A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) : Prop :=
  ∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (S : Stratification Z),
    (∀ μ : Fin S.n, sfFiniteImmersionStratum A (S.immersion μ) N) →
      (∃ (T : Stratification X) (e : Fin S.n ⊕ Unit ≃ Fin T.n),
        (∀ μ : Fin S.n, ∃ h : T.domain (e (.inl μ)) ≅ S.domain μ,
          h.hom ≫ S.immersion μ ≫ i = T.immersion (e (.inl μ))) ∧
        (∃ h : T.domain (e (.inr ())) ≅ U,
          h.hom ≫ j = T.immersion (e (.inr ()))) ∧
        ∀ ν : Fin T.n, sfFiniteImmersionStratum A (T.immersion ν)
          ((proEtaleConstantModuleDirectImage i A).obj N)) ∧
      (∀ μ : Fin S.n,
        Nonempty (proEtaleConstantModulePullback (S.immersion μ ≫ i) A
          ((proEtaleConstantModuleDirectImage i A).obj N) ≅
            proEtaleConstantModulePullback (S.immersion μ) A N)) ∧
      IsZero (proEtaleConstantModulePullback j A
        ((proEtaleConstantModuleDirectImage i A).obj N))

private theorem locallyConstant_universes {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    (h : IsLocallyConstantProEtaleModuleSheaf Y A M) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A M := by
  obtain ⟨I, V, f, hf, h⟩ := h
  exact ⟨I, V, f, hf, fun a ↦ by obtain ⟨N, e⟩ := h a; exact ⟨N, trivial, e⟩⟩

private theorem locallyConstant_of_universes {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    (h : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} Y A M) :
    IsLocallyConstantProEtaleModuleSheaf Y A M := by
  obtain ⟨I, V, f, hf, h⟩ := h
  exact ⟨I, V, f, hf, fun a ↦ by obtain ⟨N, _, e⟩ := h a; exact ⟨N, e⟩⟩

private theorem stratum_of_iso (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (s : S ⟶ X) {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ≅ N) (h : sfFiniteImmersionStratum A s N) :
    sfFiniteImmersionStratum A s M := by
  let es := (proEtaleConstantRingPullback A s).mapIso e
  constructor
  · obtain ⟨I, V, f, hf, hv⟩ := h.1
    refine ⟨I, V, f, hf, fun a ↦ ?_⟩
    obtain ⟨L, ⟨eL⟩⟩ := hv a
    exact ⟨L, ⟨(SheafOfModules.overFunctor _ (V a)).mapIso es ≪≫ eL⟩⟩
  · intro Ω _ _ y
    have : Finite ((geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).obj
        ((proEtaleConstantRingPullback A s).obj N)) := h.2 Ω y
    let et := (geometricRingModuleStalkFunctor y (proEtaleConstantRing S A)).mapIso es
    exact Finite.of_injective et.hom (ConcreteCategory.bijective_of_isIso et.hom).1

private theorem constructible_of_iso (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ≅ N) (h : IsConstructibleProEtaleModuleSheaf X A N) :
    IsConstructibleProEtaleModuleSheaf X A M := by
  obtain ⟨S, hp, hS⟩ := h
  exact ⟨S, hp, fun a ↦ stratum_of_iso A (S.immersion a) e (hS a)⟩

private theorem pullback_partitions (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : Y ⟶ X) : sfFiniteImmersionPullbackPartitions A g := by
  intro M S hS a
  have := S.isImmersion a
  obtain ⟨_, _, _, _, _, h⟩ :=
    proEtale_cartesianStratum_moduleRestriction (S.immersion a) g A
  obtain ⟨hl, hs⟩ := h M ⟨locallyConstant_universes (hS a).1, (hS a).2⟩
  exact ⟨locallyConstant_of_universes hl, hs⟩

private theorem pullback_constructible (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (hM : IsConstructibleProEtaleModuleSheaf X A M) :
    IsConstructibleProEtaleModuleSheaf Y A ((proEtaleConstantRingPullback A g).obj M) := by
  obtain ⟨S, hp, hS⟩ := hM
  exact ⟨S.pullback g, hp, pullback_partitions A g M S hS⟩

private theorem over_iso_of_eq {X W V : Scheme.{u}} (f : W ⟶ X) (g : V ⟶ X)
    (h : (⟨W, f⟩ : Σ T : Scheme.{u}, T ⟶ X) = ⟨V, g⟩) :
    ∃ e : W ≅ V, e.hom ≫ g = f := by
  cases h
  exact ⟨Iso.refl _, Category.id_comp _⟩

private theorem closed_partitions (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hji : Set.range j = (Set.range i)ᶜ)
    (hi : ∀ N, Nonempty (proEtaleConstantModulePullback i A
      ((proEtaleConstantModuleDirectImage i A).obj N) ≅ N))
    (hj : ∀ N, IsZero (proEtaleConstantModulePullback j A
      ((proEtaleConstantModuleDirectImage i A).obj N))) :
    sfFiniteImmersionClosedPartitions A i j := by
  intro N S hS
  let S₀ : FiniteLocallyClosedStratification Z :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  obtain ⟨_, _, T, e, he, ht⟩ :=
    sf_closed_partition_module_test i j hji S₀ S.isConstructible_stratum
  obtain ⟨ei⟩ := hi N
  obtain ⟨hres, _, hT⟩ := ht A ((proEtaleConstantModuleDirectImage i A).obj N) N ei (hj N)
  have hT := (hT (fun a ↦ ⟨locallyConstant_universes (hS a).1, (hS a).2⟩)).1.2
  let e₀ : Fin S.n ⊕ Unit ≃ Fin (S.n + 1) :=
    (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
  refine ⟨⟨T, e₀.trans e, ?_, ?_, hT⟩, hres, hj N⟩
  · intro a
    have ha := he a.castSucc
    simp only [Fin.snoc_castSucc] at ha
    exact over_iso_of_eq _ _ ha
  · have he₀ : e₀ (.inr ()) = Fin.last S.n := by
      apply Fin.ext
      rfl
    apply over_iso_of_eq
    change (⟨T.domain (e (e₀ (.inr ()))), T.immersion (e (e₀ (.inr ())))⟩ :
      Σ W : Scheme.{u}, W ⟶ X) = ⟨U, j⟩
    rw [he₀]
    simpa only [Fin.snoc_last] using he (Fin.last S₀.n)

private theorem closed_constructible (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (h : sfFiniteImmersionClosedPartitions A i j)
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A))
    (hN : IsConstructibleProEtaleModuleSheaf Z A N) :
    IsConstructibleProEtaleModuleSheaf X A ((proEtaleConstantModuleDirectImage i A).obj N) := by
  obtain ⟨S, _, hS⟩ := hN
  obtain ⟨⟨T, e, _, _, hT⟩, _⟩ := h N S hS
  refine ⟨T, ?_, hT⟩
  exact Nat.zero_lt_of_lt (e (.inr ())).isLt

private theorem directImage_eq (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPushforward A f = proEtaleConstantModuleDirectImage f A := by
  unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage proEtaleConstantRingComparison
  rw [proEtaleConstantModulePullback_ring_direct]

section DerivedAssembly

private abbrev modules_abelian (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian (proEtaleRingModules X (proEtaleConstantRing X A)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      (ProEt.topology X) (A := AddCommGrpCat.{u + 1}))

attribute [local instance] modules_abelian proEtaleRingModules_hasDerivedCategory

private theorem action_of_exact (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) [Finite (Padic.coefficientExtensionRing l E n)]
    (X Y : Scheme.{u})
    (F : proEtaleRingModules X
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n)))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (DF : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n))
    [DF.CommShift ℤ] [DF.IsTriangulated] (e : DF ≅ F.mapDerivedCategory)
    (hc : ∀ M, IsConstructibleProEtaleModuleSheaf X
        (Padic.coefficientExtensionRing l E n) M →
      IsConstructibleProEtaleModuleSheaf Y (Padic.coefficientExtensionRing l E n) (F.obj M)) :
    sfFiniteImmersionAction (Padic.coefficientExtensionRing l E n) X Y
      (intrinsicFiniteTorsionConstructible l E n hn X)
      (intrinsicFiniteTorsionConstructible l E n hn Y) F DF := by
  let he (r : ℤ) : DF ⋙ DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) r ≅
      DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) r
        ⋙ F := Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ r) ≪≫
    (F.mapDerivedCategoryHomologyFunctorIso r).symm
  have hs (C) : proEtaleCohomologicalSupport (DF.obj C) ⊆
      proEtaleCohomologicalSupport C := by
    intro r hr
    by_contra h
    exact hr ((F.map_isZero (not_not.mp h)).of_iso ((he r).app C))
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, fun r ↦ ⟨he r⟩, ?_, ?_⟩
  · exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q e ≪≫ F.mapDerivedCategoryFactors⟩
  · intro C hC
    exact ⟨hC.1.subset (hs C), fun r ↦
      constructible_of_iso (Padic.coefficientExtensionRing l E n) ((he r).app C) (hc _ (hC.2 r))⟩
  · intro a b C hC
    exact (hs C).trans hC

end DerivedAssembly

/-- Closed direct image and the two inverse images preserve bounded constructibility,
the original stratifications in the specified way, and every unchanged interval.
No reducedness assumption is made on the closed subscheme.

Source: main-20261015, prop-sf-open-closed-triangle-all-stages.proof.md, finite stage;
Stacks 09AA, 09BM, 09AH, 093R and 015F
(blueprint: lem-sf-finite-immersion-constructibility-interval).

Proof plan (the seven reviewed DAG steps):
1. Every open of the Noetherian X is quasi-compact. Thus j is quasi-compact and every
locally closed subset is constructible, by the constructible-subset definition.
2. The canonical constant-ring comparison is invertible. Immersion inverse images are
exact, and ringed open-closed localization gives exact closed direct image, its counit
isomorphism and its zero restriction to U (proEtale_ringed_open_closed).
3. Use Stratification.pullback for each original partition. Composition comparisons
identify restrictions on each fibre product with pullbacks of the old restrictions.
The finite-local-constancy pullback lemma preserves local constancy and finite stalks.
4. Compose each original closed-side immersion with i and adjoin U. Closed-embedding
and immersion-composition properties make this the required constructible partition.
5. The closed counit identifies restrictions with those of N; on U the restriction is
zero. This proves constructibility on those very strata, without reducing Z.
6. Exact-functor derived factorization and exactFunctor_derivedFunctor give triangulated
termwise descent on all unbounded complexes, identifying Ri_* with ordinary i_*.
7. Exactness preserves kernels, images and cokernels, giving the natural cohomology
isomorphisms. Additivity preserves zero, hence every same interval, including a > b.
Constructibility of each cohomology sheaf and finite support give the restrictions to
D^b_c. No resolution by bounded complexes of constructible terms is required. -/
theorem finiteImmersion_constructibility_interval
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Z U : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (_hX : IsUnit (l : Γ(X, ⊤))) (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] (_hU : Set.range j = (Set.range i)ᶜ) :
    sfFiniteImmersionAction (Padic.coefficientExtensionRing l E n) X Z
      (intrinsicFiniteTorsionConstructible l E n hn X)
      (intrinsicFiniteTorsionConstructible l E n hn Z)
      (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E n) i)
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) i) ∧
    sfFiniteImmersionAction (Padic.coefficientExtensionRing l E n) X U
      (intrinsicFiniteTorsionConstructible l E n hn X)
      (intrinsicFiniteTorsionConstructible l E n hn U)
      (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E n) j)
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) j) ∧
    sfFiniteImmersionAction (Padic.coefficientExtensionRing l E n) Z X
      (intrinsicFiniteTorsionConstructible l E n hn Z)
      (intrinsicFiniteTorsionConstructible l E n hn X)
      (proEtaleConstantModuleDirectImage i (Padic.coefficientExtensionRing l E n))
      (proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n)) ∧
    sfFiniteImmersionPullbackPartitions (Padic.coefficientExtensionRing l E n) i ∧
    sfFiniteImmersionPullbackPartitions (Padic.coefficientExtensionRing l E n) j ∧
    sfFiniteImmersionClosedPartitions (Padic.coefficientExtensionRing l E n) i j := by
  let A := Padic.coefficientExtensionRing l E n
  let : Abelian (proEtaleRingModules X (proEtaleConstantRing X A)) := modules_abelian X A
  let : Abelian (proEtaleRingModules Z (proEtaleConstantRing Z A)) := modules_abelian Z A
  let : Abelian (proEtaleRingModules U (proEtaleConstantRing U A)) := modules_abelian U A
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let V : X.ProEt := ProEt.mk j
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion j)
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact j)
  obtain ⟨hlim, hcol, hcount, _⟩ := proEtaleIdentifiedOpenClosed i V _hU
    (proEtaleConstantRing X A) (proEtaleConstantRing Z A) (proEtaleConstantRing U A)
    (proEtaleConstantRingComparison i A) (proEtaleConstantRingComparison j A)
  have heq := directImage_eq A i
  change PreservesFiniteLimits (proEtaleConstantRingPushforward A i) at hlim
  change PreservesFiniteColimits (proEtaleConstantRingPushforward A i) at hcol
  rw [heq] at hlim hcol
  have : PreservesFiniteLimits (proEtaleConstantModuleDirectImage i A) := hlim
  have : PreservesFiniteColimits (proEtaleConstantModuleDirectImage i A) := hcol
  have hi (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
      Nonempty (proEtaleConstantModulePullback i A
        ((proEtaleConstantModuleDirectImage i A).obj N) ≅ N) := by
    let e : proEtaleConstantRingPushforward A i ≅ proEtaleConstantModuleDirectImage i A :=
      eqToIso heq
    have := hcount
    exact ⟨(proEtaleConstantRingPullback A i).mapIso (e.app N).symm ≪≫
      asIso ((proEtaleConstantRingAdjunction A i).counit.app N)⟩
  have hj (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
      IsZero (proEtaleConstantModulePullback j A
        ((proEtaleConstantModuleDirectImage i A).obj N)) := by
    have h := (proEtaleRingModule_closed_essImage_iff_and_unit_isIso i j _hU
      (proEtaleConstantRing X A) (proEtaleConstantRing Z A) (proEtaleConstantRing U A)
      (proEtaleConstantRingComparison i A) (proEtaleConstantRingComparison j A)
      ((proEtaleConstantModuleDirectImage i A).obj N)).1
    apply h.mp
    exact ⟨N, ⟨(eqToIso heq).app N⟩⟩
  have hp := closed_partitions A i j _hU hi hj
  refine ⟨?_, ?_, ?_, pullback_partitions A i, pullback_partitions A j, hp⟩
  · exact action_of_exact l E n hn X Z _ _ (Iso.refl _)
      (pullback_constructible A i)
  · exact action_of_exact l E n hn X U _ _ (Iso.refl _)
      (pullback_constructible A j)
  · exact action_of_exact l E n hn Z X _ _
      (proEtaleConstantModuleDirectImage i A).rightDerivedFunctorIsoMapDerivedCategory
      (closed_constructible A i j hp)

end AlgebraicGeometry.Scheme
