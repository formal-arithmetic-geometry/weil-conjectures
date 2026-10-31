/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.FiniteScalarTensorRealization
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-! # Tensor closure of ordinary uniformly constructible finite-Tor towers

Source: blueprint smooth-purity base-change factors, proof (2), tensor domains;
blueprint lem-sf-tensor-ctf (i),(ii), applied levelwise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.UniformTowerTensorClosure

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, tor_of_iso T A e ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

private theorem etaleBounded_iff (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private theorem comparison_tor_iff (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (a b : ℤ) (hab : a ≤ b)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
      HasProEtaleTorAmplitude T A
        ((finiteCoefficientIntrinsicDerivedComparison T A).obj K) a b := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let R := finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso C R).app K
  have h := comparison_torAmplitudeIn_iff A T a b hab ⟨K, hK⟩
  exact h.trans ⟨fun h ↦ tor_of_iso T A e.symm h, fun h ↦ tor_of_iso T A e h⟩

/-- At a finite coefficient ring, tensor preserves constructibility and adds the
specified Tor intervals. Testing on the unit gives cohomology in the same interval. -/
private theorem finite_tensor_bounds (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (S : SemilinearSections.Closed.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T A))
    (models : SemilinearSections.Models.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T A) S)
    (K L : proEtaleDerivedCategory T A)
    (hK : spFiniteConstructibleTor T A K) (hL : spFiniteConstructibleTor T A L)
    (a b c d : ℤ) (htK : HasProEtaleTorAmplitude T A K a b)
    (htL : HasProEtaleTorAmplitude T A L c d) :
    spFiniteConstructibleTor T A (S.tensor.obj (K, L)) ∧
      (∀ i : ℤ, (i < a + c ∨ b + d < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (S.tensor.obj (K, L)))) ∧
      HasProEtaleTorAmplitude T A (S.tensor.obj (K, L)) (a + c) (b + d) := by
  classical
  let B := ULift.{u + 1, u} A
  let U := comparisonUpperStar (ModuleCat.{u + 1} B) T
  let R := finiteCoefficientIntrinsicRealization T A
  let F := (sfIntrinsicDerivedEquivalence T A).functor
  let j := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives T (proEtaleConstantRing T A))
    (P' := CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology T) (R := proEtaleConstantRing T A))
    (fun P hP ↦ (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP.1)
  let model : ProEtaleTensorModel T (proEtaleConstantRing T A) :=
    { tensor := S.tensor
      representative := Functor.isoWhiskerLeft (j.prod j) models.comparison }
  let t := finiteScalarTensorRealization T A model
  obtain ⟨ak, bk, habk, hvk⟩ := hK.1
  obtain ⟨al, bl, habl, hvl⟩ := hL.1
  obtain ⟨P, ⟨eP⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1 K).mpr
    ⟨hK.2.1, ak, bk, habk, hvk⟩
  obtain ⟨Q, ⟨eQ⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1 L).mpr
    ⟨hL.2.1, al, bl, habl, hvl⟩
  have hP := (etaleBounded_iff T B P.obj).mp P.property
  have hQ := (etaleBounded_iff T B Q.obj).mp Q.property
  have htP := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp
    ((comparison_tor_iff T A a b htK.1 P.obj hP.1.1).mpr
      (tor_of_iso T A eP.symm htK))
  have htQ := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp
    ((comparison_tor_iff T A c d htL.1 Q.obj hQ.1.1).mpr
      (tor_of_iso T A eQ.symm htL))
  let V := ((Etale.derivedTensor (ModuleCat.{u + 1} B) T).obj P.obj).obj Q.obj
  have hV : Etale.DerivedCategory.isBoundedConstructible B T V :=
    (etaleBounded_iff T B V).mpr (Etale.boundedConstructible_tensor B T hP hQ ⟨c, d, htQ⟩)
  have htV := Etale.torAmplitudeIn_tensor (ModuleCat.{u + 1} B) T a b c d htP htQ
  let ep : F.obj (U.mapDerivedCategory.obj P.obj) ≅ K :=
    ((Functor.mapDerivedCategoryCompIso U R).app P.obj).symm ≪≫ eP
  let eq : F.obj (U.mapDerivedCategory.obj Q.obj) ≅ L :=
    ((Functor.mapDerivedCategoryCompIso U R).app Q.obj).symm ≪≫ eQ
  let eV : (finiteCoefficientIntrinsicDerivedComparison T A).obj V ≅
      S.tensor.obj (K, L) :=
    (Functor.mapDerivedCategoryCompIso U R).app V ≪≫
      F.mapIso (asIso ((U.mapDerivedCategoryTensorComparison.app P.obj).app Q.obj)) ≪≫
      ((t.app (U.mapDerivedCategory.obj P.obj)).app (U.mapDerivedCategory.obj Q.obj)) ≪≫
      S.tensor.mapIso (ep.prod eq)
  have himage := ((finiteRing_constructibleDerived_origin T A).2.2.1
    (S.tensor.obj (K, L))).mp ⟨⟨V, hV⟩, ⟨eV⟩⟩
  have ht : HasProEtaleTorAmplitude T A (S.tensor.obj (K, L)) (a + c) (b + d) :=
    tor_of_iso T A eV ((comparison_tor_iff T A (a + c) (b + d)
      (add_le_add htK.1 htL.1) V ((etaleBounded_iff T B V).mp hV).1.1).mp
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr htV))
  have hv : ∀ i : ℤ, (i < a + c ∨ b + d < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (S.tensor.obj (K, L))) := by
    have hbounds := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htV
    intro i hi
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj V) := by
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff V (a + c)).1 hbounds.1 i hi
      · exact (DerivedCategory.isLE_iff V (b + d)).1 hbounds.2 i hi
    exact ((finiteCoefficientIntrinsicComparison T A)
      |>.isZero_homologyFunctor_mapDerivedCategory_obj hz).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso eV).symm
  exact ⟨⟨himage.2, himage.1, a + c, b + d, ht⟩, hv, ht⟩

/-- Ordinary tensor preserves the uniform constructible finite-Tor domain, without
any normalization assumption on either tower.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, proof (2), domains;
lem-sf-tensor-ctf (i),(ii).
(blueprint: lem-sp-uniform-tower-tensor-closure).

Proof: choose common cohomological and Tor intervals for K and L. Exact evaluation,
the realization counit, and tensorEvaluation identify each level of the displayed
object with the ordinary derived tensor of the two corresponding finite levels.
For each finite constant coefficient ring, descend the two bounded constructible
complexes to the etale site. Reflect their specified Tor intervals through finite
coefficient comparison. The bounded constructible tensor theorem proves
constructibility, and the Tor tensor theorem adds the two Tor intervals. The
comparison tensor isomorphism carries both conclusions back to the intrinsic
pro-etale tensor. Testing its Tor interval against the coefficient unit also gives
cohomology in that same sum interval. All four endpoints are independent of the
level, so these conclusions supply the required common intervals. Transport along
the evaluation isomorphisms. This uses no transition map being invertible and
includes zero towers, empty schemes, the first positive level, coincident interval
endpoints, and ramified coefficient extensions. -/
theorem tensor_mem
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (b : SpTowerShriek.Base ell E) (q : SpTowerCalculus.Coordinates ell E b)
    (T : Scheme.{u}) [IsNoetherian T]
    (K L : spDerivedCoefficientTowers ell E T (q.abelian T))
    (hK : spConstructibleTorTowers ell E T (q.abelian T) K)
    (hL : spConstructibleTorTowers ell E T (q.abelian T) L) :
    spConstructibleTorTowers ell E T (q.abelian T)
      ((SpTowerCalculus.realization ell E b T (q.abelian T)).inverse.obj
        ((SpTowerShriek.tensor ell E b T).obj
          ((SpTowerCalculus.realization ell E b T (q.abelian T)).functor.obj K,
            (SpTowerCalculus.realization ell E b T (q.abelian T)).functor.obj L))) := by
  classical
  let F := SpTowerCalculus.realization ell E b T (q.abelian T)
  let V := (SpTowerShriek.tensor ell E b T).obj (F.functor.obj K, F.functor.obj L)
  let M := F.inverse.obj V
  let ev := spDerivedCoefficientEvaluation ell E T (q.abelian T)
  let e (n : ℕ) : (ev n).obj M ≅
      ((b.calculus T).levelClosed n).tensor.obj ((ev n).obj K, (ev n).obj L) :=
    ((SpTowerCalculus.levelComparison ell E b q T n).app M).symm ≪≫
      (SpTowerShriek.Ev ell E T n).mapIso (F.counitIso.app V) ≪≫
      ((b.calculus T).tensorEvaluation n).app (F.functor.obj K, F.functor.obj L) ≪≫
      ((b.calculus T).levelClosed n).tensor.mapIso
        (((SpTowerCalculus.levelComparison ell E b q T n).app K).prod
          ((SpTowerCalculus.levelComparison ell E b q T n).app L))
  obtain ⟨rK, sK, a, b', hrsK, hab, hboundsK⟩ := hK.2
  obtain ⟨rL, sL, c, d, hrsL, hcd, hboundsL⟩ := hL.2
  have hlevel (n : ℕ) := finite_tensor_bounds T (SpTowerShriek.R ell E n)
    ((b.calculus T).levelClosed n) ((b.calculus T).levelTensorModels n)
    ((ev n).obj K) ((ev n).obj L) (hK.1 n) (hL.1 n)
    a b' c d (hboundsK n).2 (hboundsL n).2
  refine ⟨fun n ↦ finite_of_iso T _ (e n).symm (hlevel n).1,
    a + c, b' + d, a + c, b' + d, add_le_add hab hcd, add_le_add hab hcd, ?_⟩
  intro n
  refine ⟨?_, tor_of_iso T _ (e n).symm (hlevel n).2.2⟩
  intro i hi
  exact ((hlevel n).2.1 i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (e n))

end AlgebraicGeometry.ProEtale.UniformTowerTensorClosure
