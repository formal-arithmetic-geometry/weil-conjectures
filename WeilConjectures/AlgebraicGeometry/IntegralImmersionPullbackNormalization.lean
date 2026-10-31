/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralImmersionPullbackNormalizationData
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.IntegralImmersionCoefficientLinearity
import WeilConjectures.AlgebraicGeometry.IntegralImmersionShiftCompatibility
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfectSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.CharP.CharAndCard

/-! # Assembly of normalized integral immersion pullbacks

The normalized coefficient presentations and comparison clauses are reexported from
`IntegralImmersionPullbackNormalizationData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.IntegralImmersionNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem interval_iso
    {T : Scheme.{u}} {K L : DerivedCategory (scalarReductionSource.{u, u} l E T)}
    (e : K ≅ L) (a b : ℤ) (hK : HasReductionInterval l E T K a b) :
    HasReductionInterval l E T L a b := by
  intro n q hq
  apply hK n
  intro hz
  exact hq (((DerivedCategory.homologyFunctor _ q).mapIso
    ((scalarReductionDerivedExtension.{u, u} l E T n).mapIso e)).isZero_iff.mp hz)

private theorem comparison_of_immersion
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsImmersion g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparison l E g) := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  obtain ⟨C⟩ := IntegralCompletedComparison.integralPullback_completedComparison l E g hY hX
  have hback (K : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E X
        ((ImmersionCompletedPullback.transport l E X).obj ((back l E X).obj K.obj)) :=
    ObjectProperty.prop_of_iso _ ((roundTrip l E X).symm.app K.obj) K.property
  have hc (K : sfIntegralConstructibleCategory l E X) :
      IntegralCompletedComparison.Complete l E ((back l E X).obj K.obj) := by
    exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E X D₀ hl₀ _).mp (hback K).1⟩
  let B : sfIntegralConstructibleCategory l E X ⥤
      ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)) :=
    { obj := fun K ↦ ⟨(back l E X).obj K.obj, C.intrinsic _ (hc K)⟩
      map := fun f ↦ ObjectProperty.homMk ((back l E X).map f.hom) }
  let β : (sfIntegralConstructible l E X).ι ⋙ back l E X ⋙
        ImmersionCompletedPullback.transport l E X ⋙ integralDerivedPullback l E g ≅
      (sfIntegralConstructible l E X).ι ⋙ back l E X ⋙
        IntegralCompletedComparison.completed l E g :=
    NatIso.ofComponents (fun K ↦ C.gamma _ (hc K))
      (fun f ↦ C.naturality _ _ (hc _) (hc _) ((back l E X).map f.hom))
  let γ : (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E g :=
    isoWhiskerLeft (sfIntegralConstructible l E X).ι
      (isoWhiskerRight (roundTrip l E X).symm (integralDerivedPullback l E g)) ≪≫
      β ≪≫ isoWhiskerRight (isoWhiskerLeft B (IntegralCompletedComparison.towerIso l E g).symm)
        (ImmersionCompletedPullback.transport l E Y)
  have hγ (K : sfIntegralConstructibleCategory l E X) :
      γ.hom.app K =
        (integralDerivedPullback l E g).map ((roundTrip l E X).inv.app K.obj) ≫
        (C.gamma ((back l E X).obj K.obj) (hc K)).hom ≫
        (ImmersionCompletedPullback.transport l E Y).map
          ((IntegralCompletedComparison.towerIso l E g).inv.app
            ⟨(back l E X).obj K.obj, C.intrinsic _ (hc K)⟩) := by
    rfl
  have himm := ImmersionCompletedPullback.immersion_completed_pullback_comparison l E g
  have hunit (K : sfIntegralConstructibleCategory l E X) :
      IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app
        ((back l E X).obj K.obj)) := (himm.2.2.2.1 _ (hc K)).2.1
  have hcIso : IsIso (whiskerLeft (sfIntegralConstructible l E X).ι
      (completionComparison l E g)) := by
    have : ∀ K : sfIntegralConstructibleCategory l E X,
        IsIso ((whiskerLeft (sfIntegralConstructible l E X).ι
          (completionComparison l E g)).app K) := by
      intro K
      dsimp only [completionComparison, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
      refine IsIso.comp_isIso' ?_ ?_
      · exact ((ordinaryPresentation l E g).symm.app K.obj).isIso_hom
      · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (hunit K)
    exact NatIso.isIso_of_isIso_app _
  let c := asIso (whiskerLeft (sfIntegralConstructible l E X).ι
    (completionComparison l E g))
  obtain ⟨sc, hγs, hcs⟩ := immersion_comparison_shifts l E g C hc γ hγ c rfl
  let := C.derivedShift
  let := sc
  have : NatTrans.CommShift γ.hom ℤ := hγs
  have : NatTrans.CommShift c.hom ℤ := hcs
  obtain ⟨hcoeff, hlinear⟩ := immersion_coefficient_linearity l E g
  have := hlinear
  have hδ : NatTrans.CommShift (γ ≪≫ c.symm).hom ℤ := by
    change NatTrans.CommShift (γ.hom ≫ c.inv) ℤ
    infer_instance
  have : NatTrans.CommShift (γ ≪≫ c.symm).symm.hom ℤ :=
    NatTrans.CommShift.of_iso_symm (γ ≪≫ c.symm) ℤ
  have hordinary (K : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y ((ordinary l E g).obj K.obj) := by
    obtain ⟨a, b, hab, hred⟩ := (hback K).2
    have h := (himm.2.2.2.2 _ a b hab (hback K) (fun n ↦ (hred n).2)).1
    exact ObjectProperty.prop_of_iso _ ((ordinaryPresentation l E g).app K.obj) h
  have hint (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
      (hab : a ≤ b) (hK : HasReductionInterval l E X K.obj a b) :
      HasReductionInterval l E Y ((ordinary l E g).obj K.obj) a b := by
    have hs := interval_iso l E ((roundTrip l E X).symm.app K.obj) a b hK
    have ht := (himm.2.2.2.2 _ a b hab (hback K) hs).2
    exact interval_iso l E ((ordinaryPresentation l E g).app K.obj) a b ht
  refine ⟨{
    coefficients := hcoeff
    integralComparison := C
    complete_back := hc
    gamma := γ
    gamma_normalization := hγ
    c := c
    c_hom := rfl
    completion_projections := ?_
    completion_transitions := ?_
    completedShift := sc
    gamma_shifts := hγs
    completion_shifts := hcs
    composite_shifts := hδ
    ordinary_exact := inferInstance
    integral_exact := ?_
    completed_exact := ?_
    ordinary_linear := hlinear
    integral_linear := ?_
    completed_linear := ?_
    constructible := ?_
    interval := ?_ }⟩
  · intro K n
    change ((ordinaryPresentation l E g).inv.app K.obj ≫
      (ImmersionCompletedPullback.transport l E Y).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app
            ((back l E X).obj K.obj))) ≫
        (ImmersionCompletedPullback.transport l E Y).map
          (ImmersionCompletedPullback.actualCompletedProjection l E g
            ((back l E X).obj K.obj) n) = _
    rw [Category.assoc, ← Functor.map_comp]
    rw [(ImmersionCompletedPullback.actualCompletedProjection_compatibility l E g).1]
  · intro K b a h
    change (ImmersionCompletedPullback.transport l E Y).map _ ≫
      (ImmersionCompletedPullback.transport l E Y).map _ = _
    rw [← Functor.map_comp]
    rw [(ImmersionCompletedPullback.actualCompletedProjection_compatibility l E g).2]
    rfl
  · exact Functor.isTriangulated_of_iso (γ ≪≫ c.symm).symm
  · exact Functor.isTriangulated_of_iso c
  · exact Functor.linear_of_iso (Padic.coefficientExtensionIntegers l E) (γ ≪≫ c.symm).symm
  · exact Functor.linear_of_iso (Padic.coefficientExtensionIntegers l E) c
  · intro K
    exact ⟨hordinary K, ObjectProperty.prop_of_iso _ (c.app K) (hordinary K),
      ObjectProperty.prop_of_iso _ (γ.app K ≪≫ (c.app K).symm).symm (hordinary K)⟩
  · intro K a b hK
    apply interval_iso l E (γ.app K ≪≫ (c.app K).symm).symm a b
    by_cases hab : a ≤ b
    · exact hint K a b hab hK
    · have hzero (r : ℤ) : HasReductionInterval l E X K.obj r r := by
        intro n q hq
        have h := hK n hq
        exact False.elim (hab (h.1.trans h.2))
      have h0 := hint K 0 0 (by omega) (hzero 0)
      have h1 := hint K 1 1 (by omega) (hzero 1)
      intro n q hq
      have hq0 := h0 n hq
      have hq1 := h1 n hq
      exfalso
      have := hq0.2
      have := hq1.1
      omega

/-- Normalized integral pullbacks for the complementary closed and open immersions.
All functors act on modules over the completed coefficient sheaves, and the domain is
the recorded full derived-complete integral constructible category.
Source: main-20261015, prop-sf-open-closed-triangle-all-stages.proof.md, integral and
rational paragraphs; Stacks 09AA, 099N(2),(5), 0941 and 015F
(blueprint: lem-sf-integral-immersion-pullback-normalization).

Proof:
1. A field is Noetherian; finite type makes X Noetherian. Closed immersion is finite
   type, so Z is Noetherian; the open-subscheme theorem gives U Noetherian. These
   schemes are compact and quasi-separated. The qcqs permanence lemma makes j qc.
2. The coefficient DVR has finite residue field. Standard-quotients-perfect gives
   the finite quotients and their displayed free resolutions. Profinite-coefficient-
   inverse-image identifies the completed coefficient sheaves, keeping constants,
   projections and all transitions. Restriction along the existing projection-normalized
   coefficient isomorphisms and its sectionwise identity round trip only change presentation.
3. Apply immersion-completed-pullback-comparison to i and j. It gives invertibility
   of the actual strict quotient unit, ordinary exact inverse image, preservation of
   completeness and constructibility, and the unchanged reduction interval.
4. The coefficient prime is invertible over the characteristic-p base. Apply
   integral-pullback-completed-comparison and finite-pullback-strict-tower-comparison.
   Their finite comparisons identify generators, strict transitions and every limit
   projection. Compose with the existing unit-normalized strict/reflector iso; this
   is exactly gamma_normalization, after the sectionwise coefficient round trip.
5. Immersion inverse image preserves products, which are exact on these sites.
   Exact-product-functor-strict-limit identifies the Roos augmentation and its zero
   second coordinate. Normalized-Roos-shift-comparison uses (y,x) mapped to
   ((-1)^r y,x), so both gamma and the actual completion comparison respect the
   canonical shifts. Their composite therefore identifies integral and termwise shifts.
6. Exact termwise inverse image induces a triangulated functor by the exact-functor
   theorem. Constant sections are preserved, giving R-linearity on complexes and
   localization. Conjugate by the normalized comparisons to get R-linearity and
   exactness of the other two functors. Finite-reduction comparisons transfer
   completeness, constructibility and the same interval. Empty sources are allowed.
-/
theorem integralImmersionPullbackNormalization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X U Z : Scheme.{u}) (aX : X ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hcomplement : Set.range j = (Set.range i)ᶜ) :
    IsNoetherian X ∧ IsNoetherian U ∧ IsNoetherian Z ∧
    QuasiSeparatedSpace X ∧ QuasiSeparatedSpace U ∧ QuasiSeparatedSpace Z ∧
    QuasiCompact j ∧ FinitePerfectQuotients l E ∧
    Nonempty (Comparison l E i) ∧ Nonempty (Comparison l E j) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let : IsNoetherian X := {}
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  let : IsNoetherian Z := {}
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.noetherianSpace
  let : IsNoetherian U := {}
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (l : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) _hl.symm)
  have stalkUnit (T : Scheme.{u}) (aT : T ⟶ Spec (CommRingCat.of D.k))
      (t : T) : IsUnit (l : T.presheaf.stalk t) := by
    simpa only [map_natCast] using hunit.map
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫ aT.appTop) ≫
        T.presheaf.germ (⊤ : T.Opens) t (by trivial)).hom
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨P, hge, hle, hterms, _, em, e0, hd, φ, ε, hQ, hε, _, hfin⟩ :=
      (standard_quotients_perfect l n hn).2 E
    refine ⟨hfin, P, hge, hle, hterms, em, e0, ε, hd, ?_, ?_⟩
    · have : IsIso (DerivedCategory.Q.map ε) := by rw [hQ]; infer_instance
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ ε).1 inferInstance
    · ext x
      exact congrArg (fun f ↦ f x) hε
  · exact comparison_of_immersion l E i (stalkUnit X aX) (stalkUnit Z (i ≫ aX))
  · exact comparison_of_immersion l E j (stalkUnit X aX) (stalkUnit U (j ≫ aX))

end WeilConjectures.IntegralImmersionNormalization
