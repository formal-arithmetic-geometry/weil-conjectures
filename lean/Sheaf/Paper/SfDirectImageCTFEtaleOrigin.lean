/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.SfDirectImageCTFNonproper
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Pro-etale direct image of a bounded constructible etale-origin complex

Source: latest Weil blueprint, sec-six-functors-basics/sk-cor-sf-direct-image-ctf,
cor-sf-direct-image-ctf-etale-origin.md and its proof
(blueprint: cor-sf-direct-image-ctf-etale-origin).

The canonical intrinsic realization expresses the comparison in modules over the
constant commutative ring sheaf. The final clause uses intrinsic constructibility,
separately from the preceding bounded constructible etale-origin witness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

attribute [local instance 2000] CommRing.toRing

private theorem boundedConstructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hz q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q
        (hq.trans_le (min_le_left a b))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem intrinsicTor_of_iso (T : Scheme.{u}) (B : Type u) [CommRing B]
    {K L : Scheme.proEtaleDerivedCategory T B} (e : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T B K a b) :
    Scheme.HasProEtaleTorAmplitude T B L a b := by
  refine ⟨h.1, ?_⟩
  intro M P he f hf hP N i hi
  obtain ⟨eM⟩ := he
  exact h.2 M P ⟨eM ≪≫ e.symm⟩ f hf hP N i hi

/-- Ordinary pro-etale derived direct image preserves bounded constructible etale origin,
with Tor interval enlarged by twice the source dimension, and belongs to intrinsic Dctf.

Source: latest Weil blueprint, sec-six-functors-basics/sk-cor-sf-direct-image-ctf,
cor-sf-direct-image-ctf-etale-origin.md and its proof
(blueprint: cor-sf-direct-image-ctf-etale-origin).

Proof plan:
1. Finite type gives quasi-compactness; separatedness gives quasi-separatedness by
   lem-pc-separated-quasi-separated. Boundedness of K' implies boundedness below.
2. Apply cor-sf-direct-image-ctf-nonproper to K'. Its etale direct image L is bounded
   constructible with Tor amplitude [a,b+2d]. Convert the equivalent finite-ring etale
   constructibility predicates when applying that recorded interface.
3. Apply prop-weil-pbc-comparison-direct-image and compose with direct image of the
   given origin isomorphism. Factor exact derived comparison through the canonical
   intrinsic coefficient realization. This gives nu_Y^* L isomorphic to Rf_* K and
   supplies the bounded constructible etale-origin witness in the first conclusion.
4. Since a <= b <= b+2d, lem-exc-comparison-tor-interval transfers the Tor interval
   of L to its comparison image. Tensor the preceding isomorphism with each arbitrary
   module sheaf in degree zero and transport cohomological vanishing. This gives the
   recorded intrinsic HasProEtaleTorAmplitude condition for Rf_* K.
5. Exact comparison identifies the output cohomology with the intrinsic comparison
   of each cohomology sheaf of L. The scalar-restriction isomorphism and the
   constructibility comparison identify its intrinsic constructibility with the
   fixed-coefficient condition, which etale inverse image preserves. The same
   cohomology isomorphisms bound the nonzero degrees by the finite interval for L.
   Combine this with the Tor interval using def-weil-finite-torsion-constructibility
   and def-weil-finite-tor-amplitude.
-/
theorem directImageCTFEtaleOrigin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (_hab : a ≤ b)
    (K' : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK' : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) X K')
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K')
    (K : Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hOrigin : Nonempty (K ≅
      (@finiteCoefficientIntrinsicDerivedComparison.{u} X
        (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn)).obj K')) :
    (∃ L : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y,
      @Etale.DerivedCategory.isBoundedConstructible.{u}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
        (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) Y L ∧
      Nonempty
        ((@finiteCoefficientIntrinsicDerivedComparison.{u} Y
          (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn)).obj L ≅
        (Scheme.proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E n)).obj K)) ∧
    Scheme.HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
      ((Scheme.proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E n)).obj K) a (b + 2 * (d : ℤ)) ∧
    WeilConjectures.finiteTorConstructible l E n hn Y
      ((Scheme.proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E n)).obj K) := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  let A := ULift.{u + 1, u} B
  have : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have : Finite A := Equiv.ulift.finite_iff.mpr inferInstance
  let ν := fun T : Scheme.{u} ↦ comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicRealization T B
  let Cp := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicDerivedComparison T B
  let re := Etale.lowerStar (ModuleCat.{u + 1} A) f
  let rp := lowerStar (ModuleCat.{u + 1} A) f
  let L := re.rightDerivedFunctor.obj K'
  have hK' := (boundedConstructible_iff A X K').mp _hK'
  obtain ⟨hL, hLTor⟩ := Etale.directImageCTFNonproper D l _hl E n hn f d _hd a b hK' _hTor
  have hL' := (boundedConstructible_iff A Y L).mpr hL
  let J : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨K', hK'.1.1⟩
  have := isIso_comparisonDirectImagePlus A f
  let efix : (ν Y).mapDerivedCategory.obj L ≅
      rp.rightDerivedFunctor.obj ((ν X).mapDerivedCategory.obj K') :=
    (ν Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app J).symm ≪≫
      ((ν Y).mapDerivedCategoryPlusCompatibility.app
        (re.rightDerivedFunctorPlus.obj J)).symm ≪≫
      _root_.DerivedCategory.Plus.ι.mapIso
        ((asIso (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)))).app J) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((ν X).mapDerivedCategoryPlus.obj J)) ≪≫
      rp.rightDerivedFunctor.mapIso ((ν X).mapDerivedCategoryPlusCompatibility.app J)
  let eC (T : Scheme.{u}) (M : Etale.DerivedCategoryModule A T) :
      (Cp T).obj M ≅ (R T).mapDerivedCategory.obj ((ν T).mapDerivedCategory.obj M) :=
    (Functor.mapDerivedCategoryCompIso (ν T) (R T)).app M
  let direct := Scheme.proEtaleConstantDerivedDirectImage f B
  obtain ⟨origin⟩ := _hOrigin
  let e : (Cp Y).obj L ≅ direct.obj K :=
    eC Y L ≪≫ (R Y).mapDerivedCategory.mapIso efix ≪≫
      (Scheme.sfIntrinsicDerivedDirectImageComparison f B).symm.app
        ((ν X).mapDerivedCategory.obj K') ≪≫
      direct.mapIso ((eC X K').symm ≪≫ origin.symm)
  have hab : a ≤ b + 2 * (d : ℤ) := by omega
  let JL : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨L, hL.1.1⟩
  have ht := (comparison_torAmplitudeIn_iff B Y a (b + 2 * (d : ℤ)) hab JL).mp hLTor
  let eTor : (R Y).mapDerivedCategory.obj
      ((siteComparisonDerivedPullbackPlus Y A).obj JL).obj ≅ (Cp Y).obj L :=
    (R Y).mapDerivedCategory.mapIso ((ν Y).mapDerivedCategoryPlusCompatibility.app JL) ≪≫
      (eC Y L).symm
  have ht' := intrinsicTor_of_iso Y B (eTor ≪≫ e) a (b + 2 * (d : ℤ)) ht
  refine ⟨⟨L, hL', ⟨e⟩⟩, ht', ?_, a, b + 2 * (d : ℤ), ht'⟩
  let F := finiteCoefficientIntrinsicComparison Y B
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
  let H' := _root_.DerivedCategory.homologyFunctor
    (Scheme.proEtaleRingModules Y (Scheme.proEtaleConstantRing Y B))
  let eH (i : ℤ) : F.obj ((H i).obj L) ≅ (H' i).obj (direct.obj K) :=
    (F.mapDerivedCategoryHomologyFunctorIso i).app L ≪≫ (H' i).mapIso e
  change Set.Finite {i : ℤ | ¬ IsZero ((H' i).obj (direct.obj K))} ∧ _
  constructor
  · obtain ⟨c, g, _, hvan⟩ := hL'.2
    apply (Set.finite_Icc c g).subset
    intro i hi
    change c ≤ i ∧ i ≤ g
    constructor
    · by_contra h
      exact hi ((F.map_isZero (hvan i (.inl (lt_of_not_ge h)))).of_iso (eH i).symm)
    · by_contra h
      exact hi ((F.map_isZero (hvan i (.inr (lt_of_not_ge h)))).of_iso (eH i).symm)
  · intro i
    apply (Scheme.proEtaleModuleRestriction_constructible_iff Y B _).mpr
    have : Scheme.IsConstructibleSheaf ((H i).obj L) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL'.1 i)
    obtain ⟨eR⟩ := intrinsicRealization_restriction Y B
    exact isConstructible_of_iso
      ((eR.app ((ν Y).obj ((H i).obj L))).symm ≪≫
        (Scheme.proEtaleModuleRestriction Y B).mapIso (eH i))
      (isConstructible_comparisonUpperStar_obj ((H i).obj L))

end AlgebraicGeometry.ProEtale
