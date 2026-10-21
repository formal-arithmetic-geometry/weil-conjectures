/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.FiniteCompactSupportScalarComparison

/-!
# Finite-level bounded constructibility for proper support

Source: Stacks Project, Tags 0GL0, 095U and 0GL6; current blueprint,
sec-six-functors-basics/sk-prop-sf-cbc/prop-finite-compact-support-constructibility
(blueprint: prop-finite-compact-support-constructibility).

We use intrinsic finite-torsion constructibility and the recorded compactification
candidate. The scalar comparison is the adjunct of compact support of the tensor unit,
followed by the recorded, normalized restriction-of-scalars comparison. In particular
it is the canonical B-linear map, not an unspecified isomorphism of underlying objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The recorded intrinsic compact-support candidate specialized to the actual finite
quotient, supplying its proved finiteness rather than asking for extra data.
Source: blueprint, compactification formula preceding the proposition; Stacks Tag 0GL0
(blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelCompactSupport (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  @sfIntrinsicCompactSupport X Y f c (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn)

/-- The canonical composite shift structure: exact extension by zero followed by the
K-injective right derived direct image. Source: blueprint exactness clause; Stacks Tag 0GL0
(blueprint: prop-finite-compact-support-constructibility). -/
instance finiteLevelCompactSupport_commShift (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (finiteLevelCompactSupport l E n hn c).CommShift ℤ :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  inferInstanceAs (((sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E n)).mapDerivedCategory ⋙
      proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E n)).CommShift ℤ)

/-- The actual quotient map, sheafified on the original small pro-etale site.
Source: blueprint, finite reduction clause; Stacks Tag 0GL6
(blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelReductionMap (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u}) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))))

/-- Ordinary unbounded derived extension along A_{E,n} to A_{E,m}.
This specializes the published K-flat derived-change-of-rings construction, retaining
its canonical universal counit and tensor-unit-normalized scalar adjunction.
Source: Stacks Tags 06YY and 0GL6 (blueprint: prop-finite-compact-support-constructibility). -/
abbrev finiteLevelDerivedReduction (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u}) :=
  pbcDerivedExtend (finiteLevelReductionMap l E m n hmn T)

/-- The canonical coefficient comparison is the scalar-adjunction transpose of
compact support of the tensor unit followed by the specified restriction comparison.
The latter is normalized on sections, on open adjunction units and on K-injectives.
Source: Stacks Tag 0GL6 and the blueprint proof, Steps 6--7
(blueprint: prop-finite-compact-support-constructibility). -/
def finiteLevelCompactSupportReductionComparison
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) :
    (finiteLevelDerivedReduction l E m n hmn Y).obj
        ((finiteLevelCompactSupport l E n (hm.trans hmn) c).obj K) ⟶
      (finiteLevelCompactSupport l E m hm c).obj
        ((finiteLevelDerivedReduction l E m n hmn X).obj K) :=
  letI := Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)
  letI := Padic.finite_coefficientExtensionRing l E m hm
  ((pbcDerivedScalarAdjunction (finiteLevelReductionMap l E m n hmn Y)).homEquiv _ _).symm
    ((finiteLevelCompactSupport l E n (hm.trans hmn) c).map
        ((pbcDerivedScalarAdjunction (finiteLevelReductionMap l E m n hmn X)).unit.app K) ≫
      (sfCompactSupportRestriction c (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m)
        (Ideal.pow_le_pow_right hmn))).hom.app
          ((finiteLevelDerivedReduction l E m n hmn X).obj K))

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

private theorem intrinsic_bc_iff_etale_origin
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    intrinsicFiniteTorsionConstructible l E n hn T K ↔
      ∃ G : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T,
        Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T G ∧
        Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T
          (Padic.coefficientExtensionRing l E n)).obj G ≅ K) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  have h := (finiteRing_constructibleDerived_origin T
    (Padic.coefficientExtensionRing l E n)).2.2.1 K
  rw [intrinsicFiniteTorsionConstructible, finite_homology_support_iff]
  rw [and_comm, ← h]
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact ⟨G.obj, G.property, ⟨e⟩⟩
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact ⟨⟨G, hG⟩, ⟨e⟩⟩

private noncomputable def intrinsic_compact_support_comparison
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let J := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let o : EX.functor ⋙ sfIntrinsicExtensionByZero c.i A ≅ J ⋙ EZ.functor :=
    EX.funInvIdAssoc (J ⋙ EZ.functor)
  let od := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ Functor.mapDerivedCategoryCompIso _ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight od _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

private theorem coefficient_has_invertible_exponent
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀)) (n : ℕ) (_hn : 1 ≤ n) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of K₀)) := by
  let v := Padic.coefficientExtensionAbsoluteValue l E
  have hv := spectralNorm_extends (K := Padic l) (L := E)
  have h := (Padic.extension_integers_dvr l E v hv).choose_spec.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change v (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E) l]
    change spectralNorm (Padic l) E ((algebraMap (Padic l) E) (l : Padic l)) < 1
    rw [hv]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : (l ^ n : Padic.coefficientExtensionRing l E n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · apply ULift.ext
    change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
    simpa only [Nat.cast_pow] using hkill
  · have hu := (hl.pow n).map (Scheme.ΓSpecIso (.of K₀)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hu

private theorem etale_bc_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (G : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T G ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T G := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    exact ⟨⟨⟨a, (DerivedCategory.isGE_iff G a).2 fun i hi ↦ hab i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff G b).2 fun i hi ↦ hab i (Or.inr hi)⟩⟩,
      fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff G a).1 ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff G b).1 hb i ((le_max_right _ _).trans_lt hi)

private theorem intrinsic_bc_realization_iff
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (L : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    intrinsicFiniteTorsionConstructible l E n hn T
      ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E n)).functor.obj L) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) T L := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let F := sfIntrinsicDerivedEquivalence T A
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let r : C.mapDerivedCategory ⋙ F.functor ≅
      ProEtale.finiteCoefficientIntrinsicDerivedComparison T A :=
    (Functor.mapDerivedCategoryCompIso C (sfIntrinsicModuleEquivalence T A).functor).symm
  rw [intrinsic_bc_iff_etale_origin l E n hn]
  constructor
  · rintro ⟨G, hG, ⟨e⟩⟩
    refine ⟨G, (etale_bc_iff _ _ G).1 hG, ⟨?_⟩⟩
    exact F.fullyFaithfulFunctor.preimageIso ((r.app G) ≪≫ e)
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact ⟨G, (etale_bc_iff _ _ G).2 hG, ⟨(r.app G).symm ≪≫ F.functor.mapIso e⟩⟩

private theorem intrinsic_bc_iso
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)}
    (e : K ≅ L) (hK : intrinsicFiniteTorsionConstructible l E n hn T K) :
    intrinsicFiniteTorsionConstructible l E n hn T L := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  obtain ⟨G, hG, ⟨eG⟩⟩ := (intrinsic_bc_iff_etale_origin l E n hn T K).1 hK
  exact (intrinsic_bc_iff_etale_origin l E n hn T L).2 ⟨G, hG, ⟨eG ≪≫ e⟩⟩

private noncomputable def fixed_compact_support_comparison
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] [HasCompactification f] (c : Compactification f)
    (L : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hL : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X L) :
    (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L ≅
      (ProEtale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj L := by
  let G := Classical.choose hL
  have hG : Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X G :=
    (Classical.choose_spec hL).1
  let e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj G ≅ L :=
    Classical.choice (Classical.choose_spec hL).2
  let G' : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G, hG.1.1⟩
  exact (ProEtale.rightDerivedLowerShriekOfCompactification _ c).mapIso e.symm ≪≫
    (ProEtale.rightDerivedLowerShriekCompactificationIso
      (ULift.{u + 1, u} A) c).symm.app G' ≪≫
    (ProEtale.rightDerivedLowerShriek _ f).mapIso e

private theorem finite_compact_support_triangulated
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : (finiteLevelCompactSupport l E n hn c).IsTriangulated := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  change ((sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E n)).mapDerivedCategory ⋙
      proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing l E n)).IsTriangulated
  infer_instance

private theorem finite_compact_support_preserves
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))] [QuasiCompact f]
    (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn X K) :
    intrinsicFiniteTorsionConstructible l E n hn Y
      ((finiteLevelCompactSupport l E n hn c).obj K) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let FX := sfIntrinsicDerivedEquivalence X A
  let FY := sfIntrinsicDerivedEquivalence Y A
  let L := FX.inverse.obj K
  let e : FX.functor.obj L ≅ K := FX.counitIso.app K
  have hL := (intrinsic_bc_realization_iff l E n hn X L).1
    (intrinsic_bc_iso l E n hn X e.symm hK)
  let := c.hasCompactification
  let := coefficient_has_invertible_exponent l E K₀ hl n hn
  have hR := ProEtale.boundedConstructible_rightDerivedLowerShriek
    (ULift.{u + 1, u} A) f (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀))
    (by simp) L hL
  let eR : FY.functor.obj
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1}
        (ULift.{u + 1, u} A)) f).obj L) ≅
      (finiteLevelCompactSupport l E n hn c).obj K :=
    FY.functor.mapIso (fixed_compact_support_comparison A c L hL).symm ≪≫
      (intrinsic_compact_support_comparison A c).symm.app L ≪≫
      (finiteLevelCompactSupport l E n hn c).mapIso e
  exact intrinsic_bc_iso l E n hn Y eR
    ((intrinsic_bc_realization_iff l E n hn Y _).2 hR)

private theorem finite_compact_support_amplitude
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))] [QuasiCompact f]
    (c : Compactification f) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn X K)
    (hab : DerivedCategory.homologyConcentratedIn a b K) :
    DerivedCategory.homologyConcentratedIn a (b + 2 * (e : ℤ))
      ((finiteLevelCompactSupport l E n hn c).obj K) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let FX := sfIntrinsicDerivedEquivalence X A
  let FY := sfIntrinsicDerivedEquivalence Y A
  let L := FX.inverse.obj K
  let eK : FX.functor.obj L ≅ K := FX.counitIso.app K
  have hL := (intrinsic_bc_realization_iff l E n hn X L).1
    (intrinsic_bc_iso l E n hn X eK.symm hK)
  have habL : DerivedCategory.homologyConcentratedIn a b L :=
    Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (sfIntrinsicModuleEquivalence X A).functor
        ((DerivedCategory.homologyConcentratedIn a b).prop_of_iso eK.symm hab)
  let := c.hasCompactification
  let := coefficient_has_invertible_exponent l E K₀ hl n hn
  have hR := ProEtale.constructibleIn_rightDerivedLowerShriek
    (ULift.{u + 1, u} A) f (X ↘ Spec (.of K₀)) (Y ↘ Spec (.of K₀))
    (by simp) e he a b L ⟨hL, habL⟩
  let eR : FY.functor.obj
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1}
        (ULift.{u + 1, u} A)) f).obj L) ≅
      (finiteLevelCompactSupport l E n hn c).obj K :=
    FY.functor.mapIso (fixed_compact_support_comparison A c L hL).symm ≪≫
      (intrinsic_compact_support_comparison A c).symm.app L ≪≫
      (finiteLevelCompactSupport l E n hn c).mapIso eK
  exact (DerivedCategory.homologyConcentratedIn a (b + 2 * (e : ℤ))).prop_of_iso eR
    (Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (sfIntrinsicModuleEquivalence Y A).functor hR.2)

/-- Finite-level compact support restricts to an exact triangulated functor on the
intrinsic bounded constructible subcategories. The interval is chosen before both the
compactification and the input. Reduction is asserted only when its actual derived
scalar extension is bounded constructible; there is no finite-Tor-amplitude assumption.
Both endpoints of the canonical comparison belong to Dbc. Its reduced output has the
specified interval [c,d+2e], uniformly in the positive reduction level and compactification.
The coherent candidate and its identity/cocycle comparisons are those of the recorded
compactification-coherence theorem, restricted to these etale-origin objects.

Source: blueprint prop-finite-compact-support-constructibility, statement and proof,
Steps 1--7; Stacks Tags 0GL0, 095U and 0GL6
(blueprint: prop-finite-compact-support-constructibility).

Proof:
1. The finite quotient is killed by a power of l, which is invertible on the schemes.
   Every compactification is finite type over the field and hence Noetherian.
2. Descend the bounded intrinsically constructible input to the etale site. Exact,
   fully faithful comparison pullback commutes with cohomology and reflects its zero
   objects, so it preserves and reflects the input interval.
3. Exact etale extension by zero preserves constructible cohomology. Proper direct
   image preserves bounded constructibility. The proper/open site comparison carries
   this result back to the intrinsic pro-etale candidate.
4. The finite-type compact-support vanishing theorem, applied to the original f,
   gives [0,2e] for a constructible sheaf. Apply successive truncation triangles and
   their cohomology long exact sequences to obtain [a,b+2e] for a complex in [a,b].
   This does not transfer the fibre bound to the boundary of a compactification.
5. The ambient candidate is triangulated. Preservation from Step 3 restricts this
   exact functor to the full bounded constructible subcategories with induced triangles.
   The recorded canonical refinement comparisons give the identity and cocycle laws.
6. For ordinary derived scalar extension, proper torsion projection formula and the
   open tensor comparison give the coefficient isomorphism on the etale site. Their
   tensor-unit/counit normalizations identify it with the displayed scalar-adjunction
   transpose. Restriction of scalars detects isomorphisms. No perfectness of B is used.
7. Exact site comparison and its K-flat scalar comparison identify the reduced input.
   Full faithfulness reflects constructibility and vanishing, so its assumed bounded
   constructibility permits the comparisons at both coefficient levels. Transport
   Step 6 back. Step 3 gives bounded constructibility of the target, and the isomorphism
   gives it for the source. Step 4 at B yields [c,d+2e], uniformly in m and the candidate.
   If c > d, the reduced input is zero, and its image satisfies every interval bound. -/
theorem finiteCompactSupportConstructibility
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ c : Compactification f,
      (finiteLevelCompactSupport l E n hn c).IsTriangulated ∧
      ∀ K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n),
        intrinsicFiniteTorsionConstructible l E n hn X K →
        intrinsicFiniteTorsionConstructible l E n hn Y
          ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ (e : ℕ),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) →
      ∃ a' b' : ℤ, a' ≤ b' ∧ ∀ (c : Compactification f)
        (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
        intrinsicFiniteTorsionConstructible l E n hn X K →
        DerivedCategory.homologyConcentratedIn a b K →
        intrinsicFiniteTorsionConstructible l E n hn Y
            ((finiteLevelCompactSupport l E n hn c).obj K) ∧
          DerivedCategory.homologyConcentratedIn a' b'
            ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (c : Compactification f)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
      intrinsicFiniteTorsionConstructible l E n hn X K →
      intrinsicFiniteTorsionConstructible l E m hm X
        ((finiteLevelDerivedReduction l E m n hmn X).obj K) →
      IsIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K) ∧
      intrinsicFiniteTorsionConstructible l E m hm Y
        ((finiteLevelDerivedReduction l E m n hmn Y).obj
          ((finiteLevelCompactSupport l E n hn c).obj K)) ∧
      intrinsicFiniteTorsionConstructible l E m hm Y
        ((finiteLevelCompactSupport l E m hm c).obj
          ((finiteLevelDerivedReduction l E m n hmn X).obj K)) ∧
      ∀ (e : ℕ),
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) →
        ∀ (a b : ℤ),
          DerivedCategory.homologyConcentratedIn a b
            ((finiteLevelDerivedReduction l E m n hmn X).obj K) →
          DerivedCategory.homologyConcentratedIn a (b + 2 * (e : ℤ))
            ((finiteLevelCompactSupport l E m hm c).obj
              ((finiteLevelDerivedReduction l E m n hmn X).obj K))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact ⟨finite_compact_support_triangulated l E n hn c,
      finite_compact_support_preserves l E K₀ hl n hn f c⟩
  · intro a b hab e he
    refine ⟨a, b + 2 * (e : ℤ), by omega, ?_⟩
    intro c K hK hbound
    exact ⟨finite_compact_support_preserves l E K₀ hl n hn f c K hK,
      finite_compact_support_amplitude l E K₀ hl n hn f c e he a b K hK hbound⟩
  · intro m hm hmn c K hK hKm
    have hi : IsIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K) := by
      simpa only [finiteLevelCompactSupportReductionComparison, finiteLevelDerivedReduction,
        finiteLevelReductionMap, finiteLevelCompactSupport, sfAmbientCompactSupportCandidate,
        sfIntrinsicCompactSupport,
        Functor.id_obj] using
        finiteCompactSupportScalarComparison l E K₀ hl n hn m hm hmn f c K hK hKm
    let := hi
    have ht := finite_compact_support_preserves l E K₀ hl m hm f c
      ((finiteLevelDerivedReduction l E m n hmn X).obj K) hKm
    refine ⟨hi, ?_, ht, ?_⟩
    · exact intrinsic_bc_iso l E m hm Y
        (asIso (finiteLevelCompactSupportReductionComparison l E m n hm hmn c K)).symm ht
    · intro e he a b hbound
      exact finite_compact_support_amplitude l E K₀ hl m hm f c e he a b
        ((finiteLevelDerivedReduction l E m n hmn X).obj K) hKm hbound

end AlgebraicGeometry.Scheme
