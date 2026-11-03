/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CompositionPairing
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Point
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.Compactification.BoundaryPreparation
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportUniformTor

/-! # Finite Hom groups into finite compact-support terms

Source: the finite-coefficient finiteness argument in the integral realization step
of the constructible exceptional compositor; SGA 4½, Th. finitude, and scalar adjunction.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

private theorem etale_hom_finite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (K M : Etale.DerivedCategoryModule Λ X)
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (a b c d : ℤ)
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hMt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    Finite (K ⟶ M) := by
  letI : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom aX
  let R := ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M
  have hR := Etale.boundedConstructible_derivedHom Λ aX a b c d hK hKt hM hMt
  let P := (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} Λ) aX).obj R
  have hP := Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType
    Λ aX aX (𝟙 _) (by simp) R hR
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let H0 := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0
  letI hC : IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ 0).obj P) := hP.2 0
  letI hFG : Module.Finite Λ ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj ((DerivedCategory.homologyFunctor _ 0).obj P)) :=
    Etale.finite_Γ_of_isConstructibleSheaf _
  let e := (Etale.homologyRightDerivedGlobalSectionsIsoOfIsSepClosed 0).app P
  letI : Module.Finite Λ ((DerivedCategory.homologyFunctor _ 0 ⋙
      Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P) := by
    change Module.Finite Λ ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj ((DerivedCategory.homologyFunctor _ 0).obj P))
    exact hFG
  letI hF0 : Module.Finite Λ (H0.obj (Γ.obj P)) := Module.Finite.equiv e.toLinearEquiv.symm
  letI hfin0 : Finite (H0.obj (Γ.obj P)) := Module.finite_of_finite Λ
  letI hfin1 : Finite ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ) ⟶ Γ.obj P) :=
    Finite.of_equiv _ (DerivedCategory.homSingleRingEquiv _).symm
  letI hfin2 : Finite (𝟙_ (Etale.DerivedCategoryModule Λ (Spec (.of k))) ⟶ P) :=
    Γ.finite_hom_of_fullyFaithful (Etale.rightDerivedGlobalSectionsUnitIso Λ k) (Iso.refl _)
  let adj := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) aX
  let eU := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) aX
  letI hfin3 : Finite (𝟙_ (Etale.DerivedCategoryModule Λ X) ⟶ R) :=
    @Finite.of_equiv _ _ hfin2 ((adj.homEquiv _ _).symm.trans
      (eU.homCongr (Iso.refl _)))
  exact @Finite.of_equiv _ _ hfin3
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := M)).symm

private theorem coefficient_has_invertible_exponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (K₀ : Type u) [Field K₀]
    (hl : IsUnit (l : K₀)) (n : ℕ) (_hn : 1 ≤ n) :
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

private theorem etale_bc
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (G : Etale.DerivedCategoryModule A T)
    (h : Etale.DerivedCategory.isBoundedConstructible A T G) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T G := by
  obtain ⟨hc, a, b, _, hab⟩ := h
  exact ⟨⟨⟨a, (DerivedCategory.isGE_iff G a).2 fun i hi ↦ hab i (Or.inl hi)⟩,
    ⟨b, (DerivedCategory.isLE_iff G b).2 fun i hi ↦ hab i (Or.inr hi)⟩⟩,
    fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩

private theorem intrinsic_hom_finite
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn X K)
    (hM : intrinsicFiniteTorsionConstructible l E n hn X M)
    (a b c d : ℤ)
    (hKt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) K a b)
    (hMt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) M c d) :
    Finite (K ⟶ M) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  letI : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  letI : HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of D.k)) :=
    coefficient_has_invertible_exponent l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) n hn
  let J := ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} A) X) ⋙ ProEtale.finiteCoefficientIntrinsicDerivedComparison X A
  have hJ := finiteRing_constructibleDerived_origin X A
  letI : J.Full := hJ.1
  letI : J.Faithful := hJ.2.1
  have origin (L : proEtaleDerivedCategory X A)
      (hL : intrinsicFiniteTorsionConstructible l E n hn X L) : J.essImage L := by
    obtain ⟨lo, hlo⟩ := hL.1.bddBelow
    obtain ⟨hi, hhi⟩ := hL.1.bddAbove
    apply (hJ.2.2.1 L).mpr
    refine ⟨hL.2, min lo hi, max lo hi, min_le_max, fun i hi' ↦ ?_⟩
    by_contra hz
    rcases hi' with hi' | hi'
    · exact (not_lt_of_ge (hlo hz)) (hi'.trans_le (min_le_left _ _))
    · exact (not_lt_of_ge (hhi hz)) ((le_max_right _ _).trans_lt hi')
  obtain ⟨K', ⟨eK⟩⟩ := origin K hK
  obtain ⟨M', ⟨eM⟩⟩ := origin M hM
  have hKb := etale_bc _ X K'.obj K'.property
  have hMb := etale_bc _ X M'.obj M'.property
  have hKt' := finiteCoefficient_comparison_reflects_torAmplitude
    D l hl E n hn X a b K'.obj hKb.1.1 K hK hKt eK.symm
  have hMt' := finiteCoefficient_comparison_reflects_torAmplitude
    D l hl E n hn X c d M'.obj hMb.1.1 M hM hMt eM.symm
  letI hfin : Finite (K'.obj ⟶ M'.obj) := etale_hom_finite (ULift.{u + 1, u} A) D.k X
    (X ↘ Spec (.of D.k)) K'.obj M'.obj hKb hMb a b c d
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hKt')
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hMt')
  letI : Finite (K' ⟶ M') := @Finite.of_equiv _ _ hfin
    ((ObjectProperty.fullyFaithfulι
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X)).homEquiv
        (X := K') (Y := M')).symm
  exact Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful J).homEquiv.trans
    (eK.homCongr eM))

/-- Finite-level compact-support terms have finite shifted Hom groups from integral
constructible objects. Source: SGA 4½, Th. finitude; blueprint Verdier-exchange Step 1,
integral realization (blueprint: lem-sf-compact-support-term-hom-finite).

Proof:
1. Transpose through the derived reduction--restriction adjunction at level n+1.
The source is the reduction of the shifted integral object M[1]. The integral
predicate supplies bounded constructibility of both reductions. Integral residue Tor
upgrades the common residue intervals to Tor intervals at every positive level.
2. Apply the uniform compact-support Tor estimate, which uses a dense refinement,
and transport the result back to the original compactification. This yields bounded
constructibility and finite Tor amplitude of the finite compact-support target.
3. Use finite-ring etale origin and its fully faithful comparison to compute Hom on
the small etale site. Reflect both Tor intervals along this comparison. Bounded
constructible internal Hom is bounded constructible by the existing finite-Tor
internal-Hom theorem. Its direct image to the algebraically closed point is bounded
constructible by the finite-type direct-image finiteness theorem, which allows
nonseparated source schemes. The degree-zero sections of that direct image form a
finite module over the finite ring. Global sections at the point are exact and fully
faithful, and inverse image preserves the unit; the direct-image adjunction and the
closed monoidal Hom adjunction identify these sections with the original Hom set.
4. Transport finiteness back through the comparison and scalar-adjunction Hom
bijections. Zero objects, empty schemes and the first positive quotient are included. -/
theorem compactSupportTerm_hom_finite
    (D : FiniteFieldDatum.{u}) (B : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic B.l) E]
    [FiniteDimensional (Padic B.l) E]
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (M : sfIntegralConstructibleCategory B.l E Y.obj.left)
    (K : sfIntegralConstructibleCategory B.l E X.obj.left) (n : ℕ) :
    Finite (M.obj⟦(1 : ℤ)⟧ ⟶ sfCompactSupportTerm B.l E c K.obj n) := by
  classical
  letI : ∀ x : X.obj.left, Invertible (B.l : X.obj.left.residueField x) := fun x ↦ by
    let φ : D.k →+* X.obj.left.residueField x :=
      (X.obj.left.evaluation ⊤ x (by trivial)).hom.comp
        ((X.obj.left ↘ Spec (.of D.k)).appTop.hom.comp
          (Scheme.ΓSpecIso (.of D.k)).inv.hom)
    exact (show IsUnit (B.l : X.obj.left.residueField x) from by
      simpa only [map_natCast] using
        (PurCompactSupport.coefficientPrimeUnit B.l D B.different).map φ).invertible
  letI : ∀ y : Y.obj.left, Invertible (B.l : Y.obj.left.residueField y) := fun y ↦ by
    let φ : D.k →+* Y.obj.left.residueField y :=
      (Y.obj.left.evaluation ⊤ y (by trivial)).hom.comp
        ((Y.obj.left ↘ Spec (.of D.k)).appTop.hom.comp
          (Scheme.ΓSpecIso (.of D.k)).inv.hom)
    exact (show IsUnit (B.l : Y.obj.left.residueField y) from by
      simpa only [map_natCast] using
        (PurCompactSupport.coefficientPrimeUnit B.l D B.different).map φ).invertible
  let M' : sfIntegralConstructibleCategory B.l E Y.obj.left :=
    ⟨M.obj⟦(1 : ℤ)⟧, (sfIntegralConstructible B.l E Y.obj.left).le_shift (1 : ℤ) _
      M.property⟩
  obtain ⟨a, b, hab, hK⟩ := K.property.2
  obtain ⟨c', d, hcd, hM⟩ := M'.property.2
  have htK := (integral_residue_tor D B.l B.different E X.obj.left).1
    K.obj K.property a b hab (hK 0).2 n
  have htM := (integral_residue_tor D B.l B.different E Y.obj.left).1
    M'.obj M'.property c' d hcd (hM 0).2 n
  obtain ⟨dim, hdim⟩ := exists_topologicalKrullDim_le (X.obj.left ↘ Spec (.of D.k))
  have hs := (ProEtale.finiteCompactSupport_uniformTor_after_denseRefinement
    D B.l B.different E f.hom.left c dim hdim).2.2.2.2.2
    (n + 1) (by omega) a b hab
    ((scalarReductionDerivedExtension B.l E X.obj.left n).obj K.obj) (hK n).1 htK
  let L := (sfAmbientCompactSupportCandidate
    (Padic.coefficientExtensionRing B.l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension B.l E X.obj.left n).obj K.obj)
  letI : Finite
      ((scalarReductionDerivedExtension B.l E Y.obj.left n).obj M'.obj ⟶ L) :=
    intrinsic_hom_finite D B.l B.different E (n + 1) (by omega) Y.obj.left
      _ L (hM n).1 hs.2.2.1 c' d a (b + 2 * (dim : ℤ)) htM hs.2.2.2.1
  exact Finite.of_equiv _
    ((derivedScalarExtensionRestrictionAdjunction B.l E Y.obj.left n).choose.homEquiv
      M'.obj L)

end WeilConjectures
