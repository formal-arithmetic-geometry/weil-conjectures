/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleUnit
import WeilConjectures.AlgebraicGeometry.FiniteIntrinsicDirectTensorComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The section invariant in intrinsic finite-coefficient coordinates

Source: blueprint master, sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: def-pur-section-invariant).

This equivalent interface uses the canonical constant-ring realization and the
published finite exceptional functor. It avoids mixing the retired pro-etale
pullback API with the finite-coefficient API. The data remain Ls* Rg! A_B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory

namespace WeilConjectures.PurityFiniteSetting

/-- The original site fits its object universe, with no extra scalar universe to infer.
Source: small pro-etale site convention (blueprint: def-pur-section-invariant). -/
instance (priority := 2000) intrinsicSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

/-- Finiteness of the actual positive coefficient quotient, by the published theorem.
Source: finite coefficient convention (blueprint: def-pur-section-invariant). -/
instance intrinsicCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The constant coefficient object in degree zero in the recorded intrinsic category.
Source: section-invariant definition, Lambda_B (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    proEtaleDerivedCategory T P.Ring :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- The existing K-flat derived tensor, with independent site and coefficient universes.
Source: section-invariant tensor invertibility (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  let R := (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} P.Ring))
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology T)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} P.Ring)))

/-- Actual exceptional image of the coefficient unit, using the specified etale adjoint
and the two canonical site comparisons. Source: omega_g in the section-invariant definition
(blueprint: def-pur-section-invariant). -/
def intrinsicDualizing (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] : proEtaleDerivedCategory V P.Ring :=
  (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification g)).obj
    (P.intrinsicCoefficientUnit B)

/-- The actual derived pullback Ls* Rg! A_B, with no choice of an orientation.
Source: section-invariant displayed definition (blueprint: def-pur-section-invariant). -/
def sectionInvariantIntrinsic (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :
    proEtaleDerivedCategory B P.Ring :=
  (Scheme.sfIntrinsicDerivedPullback P.Ring s).obj (P.intrinsicDualizing g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
private theorem intrinsicGoodIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (h : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T L := by
  have hc : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos T L :=
    (finiteTorsionConstructible P.field P.coefficients.l P.coefficients.different
      P.extension P.level P.level_pos T).prop_of_iso e h.1
  obtain ⟨a, b, hab⟩ := h.2
  refine ⟨hc, a, b, hab.1, ?_⟩
  intro C D hC f hf hD M i hi
  obtain ⟨eC⟩ := hC
  exact hab.2 C D ⟨eC ≪≫ e.symm⟩ f hf hD M i hi

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private noncomputable def comparison_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison T
      (Padic.coefficientExtensionRing l E (n + 1))).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E T n)) := by
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let ν := ProEtale.comparisonUpperStar A T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T B
  let F := ProEtale.finiteCoefficientIntrinsicComparison T B
  let e : F.obj (𝟙_ _) ≅ SheafOfModules.unit (integralCoefficientSheaf l E T n) := by
    change R.obj (ν.obj (𝟙_ _)) ≅ _
    exact R.mapIso ((Functor.Monoidal.εIso ν).symm ≪≫
      (Functor.Monoidal.εIso (constantSheaf (ProEt.topology T) A)).symm) ≪≫
      proEtaleConstantModuleUnit T B
  change F.mapDerivedCategory.obj (𝟙_ _) ≅ _
  exact F.mapDerivedCategory.mapIso (Etale.singleFunctorObjUnitIso A T).symm ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private theorem etale_unit_ctf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T (𝟙_ _) := by
  refine ⟨(Etale.DerivedCategory.boundedConstructible _ T).prop_of_iso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T)
    (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0, ?_⟩
  exact (Etale.DerivedCategory.torAmplitudeIn _ T 0 0).prop_of_iso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T)
    (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.flat_of_isDualizable isDualizable_unit))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private theorem etale_inverse_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [IsAlgClosed k] (T : Scheme.{u})
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent A T] (K : Etale.DerivedCategoryModule A T)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K)
    (hI : IsInvertible K) :
    ∃ L, Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T L ∧
      Nonempty (K ⊗ L ≅ 𝟙_ _) ∧ Nonempty (L ⊗ K ≅ 𝟙_ _) := by
  obtain ⟨L, ⟨e⟩, ⟨e'⟩⟩ := hI
  let : ExactPairing L K := exactPairingOfTensorIso e' e
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hUbc, c, d, hUt⟩ := etale_unit_ctf A T
  obtain ⟨m, hm⟩ := exists_topologicalKrullDim_le aT
  have hDbc := Etale.boundedConstructible_derivedHom A aT a b c d hKbc hKt hUbc hUt
  have hDt := Etale.torAmplitudeIn_derivedHom A aT m hm a b c d hKbc hKt hUbc hUt
  refine ⟨L, ?_, ⟨e⟩, ⟨e'⟩⟩
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso
    (MonoidalClosed.ihomObjUnitIso L K) ⟨hDbc, _, _, hDt⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private theorem comparison_ctf (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    [∀ x : T, Invertible (P.coefficients.l : T.residueField x)]
    [Finite P.Ring] (K : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj K) := by
  obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, c, d, ht⟩ := hK
  have hbc : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K := by
    refine ⟨fun i ↦
      (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).mp ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).mp hb i hi
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    (ht.mono (min_le_left c d) le_rfl)
  have h := finiteCoefficient_comparison_preserves_torAmplitude P.field P.coefficients.l
    P.coefficients.different P.extension P.level P.level_pos T (min c d) d
    (min_le_right _ _) K hbc ht'
  exact ⟨h.1, min c d, d, h.2⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private noncomputable def exceptional_origin_iso (P : PurityFiniteSetting.{u})
    [Finite P.Ring] (X Y : Scheme.{u})
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (G : Etale.DerivedCategoryModule P.Coefficient Y)
    (hG : _root_.DerivedCategory.TStructure.t.plus G)
    (K : proEtaleDerivedCategory Y P.Ring)
    (e : K ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).obj G) :
    (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification f)).obj K ≅
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
        ((Etale.rightDerivedUpperShriek P.Coefficient f).obj G) := by
  let E := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : E.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact
    Y P.Ring).1
  have hE : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let eComp := @Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ ν E
    inferInstance hE inferInstance inferInstance
    (ProEtale.finiteCoefficientIntrinsicRealization_exact Y P.Ring).2.2.1
    (ProEtale.finiteCoefficientIntrinsicRealization_exact Y P.Ring).2.2.2
  have : E.asEquivalence.functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let Rν := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let F := Etale.rightDerivedUpperShriek P.Coefficient f
  let e₁ : E.asEquivalence.inverse.mapDerivedCategory.obj K ≅
      ν.mapDerivedCategory.obj G :=
    E.asEquivalence.inverse.mapDerivedCategory.mapIso e ≪≫
    E.asEquivalence.inverse.mapDerivedCategory.mapIso
      (eComp.app G) ≪≫
    E.asEquivalence.mapDerivedCategory.unitIso.symm.app _
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y G hG
  let e₂ : Rν.obj (ν.mapDerivedCategory.obj G) ≅ G :=
    (asIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app G)).symm
  let νX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
  let EX := (sfIntrinsicModuleEquivalence X P.Ring).functor
  have hEX : EX.Additive := sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let c := @Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ νX EX
    inferInstance hEX inferInstance inferInstance
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X P.Ring).2.2.1
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X P.Ring).2.2.2
  exact EX.mapDerivedCategory.mapIso
      (νX.mapDerivedCategory.mapIso (F.mapIso (Rν.mapIso e₁ ≪≫ e₂))) ≪≫
    c.symm.app _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private def comparison_pullback (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A ⋙
        sfIntrinsicDerivedPullback A f ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X A := by
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y
  let E := sfIntrinsicModuleEquivalence Y A
  let G := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let R := (sfIntrinsicModuleEquivalence X A).functor
  let e : ProEtale.finiteCoefficientIntrinsicComparison Y A ⋙ sfIntrinsicPullback A f ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
    Functor.isoWhiskerLeft ν (E.funInvIdAssoc (G ⋙ R)) ≪≫
      Functor.isoWhiskerRight
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) R
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
/-- The invariant is tensor-invertible in the exact recorded finite-Tor category.
Smooth relative dimension may vary; no Tate orientation is supplied.
Source: section-invariant invertibility paragraph (blueprint: def-pur-section-invariant).
Proof: split the finite-type smooth source into its finitely many clopen relative-dimension
loci and use thm-pur-cohomological-smoothness on each. Reassemble the relative dualizing
object and its inverse along this finite partition. Derived inverse image preserves the
coefficient unit and tensor product. Pulling the two inverse isomorphisms along the section
gives the asserted two-sided inverse. Bounded constructibility and a uniform finite Tor
interval descend from the finite partition and are preserved by inverse image. The
canonical coefficient realization identifies precisely finiteTorConstructible, including
empty schemes and the dimension-zero identity section. -/
theorem sectionInvariantIntrinsic_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g] [Smooth g]
    [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantIntrinsic g s) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantIntrinsic g s, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantIntrinsic g s) ≅ P.intrinsicCoefficientUnit B) := by
  classical
  let _ := hs
  rcases P with ⟨field, coefficients, extension, level, level_pos⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt level_pos)
  let P : PurityFiniteSetting.{u} :=
    ⟨field, coefficients, extension, n + 1, level_pos⟩
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : V.Over (Spec (.of P.field.k)) := ⟨g ≫ aB⟩
  have : LocallyOfFiniteType g := inferInstance
  have : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aB))
  have : QuasiCompact (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aB))
  have : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  have : QuasiCompact (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aB)
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g ≫ aB)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (g ≫ aB)
  have : IsNoetherian V := ⟨⟩
  let : HasInvertibleExponent P.Coefficient B := P.finiteComparedInvertibleExponent aB
  let : HasInvertibleExponent P.Coefficient V := .of_hom g
  let : ∀ x : B, Invertible (P.coefficients.l : B.residueField x) := fun x ↦
    IsUnit.invertible (by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk B aB x).map (B.residue x).hom)
  let W := Etale.dualizingComplex P.Coefficient g
  let S := Etale.sectionInvariant P.Coefficient g s
  have hS := Etale.isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant_of_smooth
    P.Coefficient g s
  have hI : IsInvertible S :=
    (Etale.isInvertible_iff_exists_derivedTensor S).mpr hS.1
  let : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  obtain ⟨Q₀, hQ₀, ⟨a₁⟩, ⟨a₂⟩⟩ :=
    etale_inverse_ctf P.Coefficient B aB S hS.2 hI
  let Cν := ProEtale.finiteCoefficientIntrinsicDerivedComparison B P.Ring
  let Q := Cν.obj Q₀
  let ω := P.intrinsicDualizing g
  let U : Etale.DerivedCategoryModule P.Coefficient B := 𝟙_ _
  have hU := etale_unit_ctf P.Coefficient B
  let eW : ω ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison V P.Ring).obj W :=
    exceptional_origin_iso P V B g U hU.1.1.1 _
      (comparison_unit P.coefficients.l P.extension B n).symm
  let F := sfIntrinsicDerivedPullback P.Ring s
  let epull : P.sectionInvariantIntrinsic g s ≅ Cν.obj S :=
    F.mapIso eW ≪≫ (comparison_pullback P.Ring s).app W ≪≫
      Cν.mapIso ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) s).app W).symm
  have hC := comparison_ctf P B S hS.2
  have hQ := comparison_ctf P B Q₀ hQ₀
  obtain ⟨t₁⟩ := ProEtale.finiteCoefficientIntrinsicDerivedTensorComparison P.Ring B S Q₀
  obtain ⟨t₂⟩ := ProEtale.finiteCoefficientIntrinsicDerivedTensorComparison P.Ring B Q₀ S
  refine ⟨intrinsicGoodIso P B epull.symm hC, Q, hQ, ⟨?_⟩, ⟨?_⟩⟩
  · exact (P.intrinsicCoefficientTensor B).mapIso (Iso.prod epull (Iso.refl Q)) ≪≫
      t₁ ≪≫ Cν.mapIso a₁ ≪≫
      comparison_unit P.coefficients.l P.extension B n
  · exact (P.intrinsicCoefficientTensor B).mapIso (Iso.prod (Iso.refl Q) epull) ≪≫
      t₂ ≪≫ Cν.mapIso a₂ ≪≫
      comparison_unit P.coefficients.l P.extension B n

/-- Nagata supplies the compactification from the source hypotheses, with no added
exceptional-adjoint condition. Source: section-invariant finite-type setting
(blueprint: def-pur-section-invariant).
Proof: B is Noetherian since it is finite type over a field. The separated finite-type
map g therefore admits a compactification by Nagata. Smoothness in particular supplies
local finite type; quasi-compactness supplies finite type. -/
theorem sectionCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    HasCompactification g := by
  exact (P.finiteComparedCompactification g aB).hasCompactification

/-- The section invariant on precisely the finite-type domain of the source.
Compactifiability is a consequence, rather than an additional assumption.
Source: displayed definition C(g,s) (blueprint: def-pur-section-invariant). -/
def sectionInvariantFinite (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    proEtaleDerivedCategory B P.Ring :=
  let _ := hs
  letI := P.sectionCompactifiable g aB
  P.sectionInvariantIntrinsic g s

/-- Tensor invertibility with all auxiliary admissibility hypotheses discharged.
Source: section-invariant Picard assertion (blueprint: def-pur-section-invariant).
Proof: use sectionCompactifiable and sectionInvariantIntrinsic_invertible. Their
coefficient objects and pullback are exactly the definition sectionInvariantFinite,
so the same finite-Tor inverse and its two tensor isomorphisms give the result. -/
theorem sectionInvariantFinite_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantFinite g aB s hs) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantFinite g aB s hs, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantFinite g aB s hs) ≅ P.intrinsicCoefficientUnit B) := by
  let := P.sectionCompactifiable g aB
  exact P.sectionInvariantIntrinsic_invertible g aB s hs

end WeilConjectures.PurityFiniteSetting
