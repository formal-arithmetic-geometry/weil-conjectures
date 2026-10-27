/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.Paper.ClopenStrictSystemComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.FiniteCoefficientSiteHomArrow
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.PurityFiniteSettingComparisonHypotheses
import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! # A finite-coefficient inverse on a pure-dimensional smooth source

Source: blueprint smooth purity, thm-pur-cohomological-smoothness, first paragraph;
finite-clopen dualizing inverse assembly, Step 4.
(blueprint: lem-pur-smooth-finite-dualizing-inverse).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local irreducible] WeilConjectures.finiteIntrinsicClosed
  WeilConjectures.finiteHomEtaleData WeilConjectures.finiteHomEtaleClosedGeneral
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
namespace WeilConjectures.PurityFiniteSetting

private theorem etale_monoidal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (finiteHomEtaleClosed l E T n).monoidal =
      (inferInstance : MonoidalCategory (Etale.DerivedCategoryModule
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) T)) := by
  have h := (finiteHomEtaleData_existsUnique l E T).choose_spec.1.closed n
  have h' : finiteHomEtaleClosed l E T n = finiteHomEtaleClosedWitness l E T n :=
    eq_of_heq (by
      unfold finiteHomEtaleClosed finiteHomEtaleData
      exact h)
  rw [h']
  change (finiteHomEtaleClosedGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) T).monoidal = _
  unfold finiteHomEtaleClosedGeneral
  exact (finiteHomEtaleClosed_existsUnique (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) T).choose_spec.1.1

private theorem tensor_obj_eq {C : Type*} [Category C]
    (H : Cᵒᵖ × C ⥤ C) (S : CoefficientClosedStructure H) (M : MonoidalCategory C)
    (h : S.monoidal = M) (K L : C) :
    S.tensor.obj (K, L) = @tensorObj C _ M.toMonoidalCategoryStruct K L := by
  cases h
  rfl

private noncomputable def comparison_tensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ)
    (K L : Etale.DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) T) :
    (finiteIntrinsicDerivedTensor l E T n).obj
        ((finiteHomNu l E T n).obj K, (finiteHomNu l E T n).obj L) ≅
      (finiteHomNu l E T n).obj (K ⊗ L) :=
  ((finiteHomNuTensor l E T n).app (K, L)).symm ≪≫
    (finiteHomNu l E T n).mapIso
      (eqToIso (tensor_obj_eq _ _ _ (etale_monoidal l E T n) K L))

private noncomputable def comparison_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (finiteHomNu l E T n).obj (𝟙_ _) ≅ finiteConstantCoefficientObject l E T n := by
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
  have hD := Etale.constructibleFiniteTor_coefficientDual A aT hK
  refine ⟨L, ?_, ⟨e⟩, ⟨e'⟩⟩
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso
    (MonoidalClosed.ihomObjUnitIso L K) hD

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

private theorem intrinsic_ctf_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)}
    (e : K ≅ L) (hL : finiteTorConstructible l E n hn T L) :
    finiteTorConstructible l E n hn T K := by
  let B := Padic.coefficientExtensionRing l E n
  let : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply hL.1.1.subset
    intro i hi hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e))
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T B _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T B).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)).symm
      ((proEtaleModuleRestriction_constructible_iff T B _).mp (hL.1.2 i))
  · obtain ⟨a, b, ht⟩ := hL.2
    refine ⟨a, b, ht.1, ?_⟩
    intro Q R he g hg hR M i hi
    exact ht.2 Q R (he.map (fun z ↦ z ≪≫ e)) g hg hR M i hi

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
    (finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
      P.field.k X Y f).obj K ≅
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj G) := by
  let E := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : E.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact
    Y P.Ring).1
  have : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let Rν := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let F := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f
  let C := ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring
  let e₁ : E.asEquivalence.inverse.mapDerivedCategory.obj K ≅
      ν.mapDerivedCategory.obj G :=
    E.asEquivalence.inverse.mapDerivedCategory.mapIso e ≪≫
    E.asEquivalence.inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν E).app G) ≪≫
    E.asEquivalence.mapDerivedCategory.unitIso.symm.app _
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y G hG
  let e₂ : Rν.obj (ν.mapDerivedCategory.obj G) ≅ G :=
    (asIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app G)).symm
  exact C.mapIso (F.mapIso (Rν.mapIso e₁ ≪≫ e₂))

/-- A smooth exceptional image of the coefficient unit of pure relative dimension
has a two-sided finite-Tor constructible inverse in the actual intrinsic coefficient
category. There is no choice of a trivialization or Tate orientation.

Source: blueprint thm-pur-cohomological-smoothness, first paragraph, and Step 4 of
lem-pur-varying-dimension-dualizing-inverse.
(blueprint: lem-pur-smooth-finite-dualizing-inverse).

Proof: apply finite_setting_comparison_hypotheses with the setting whose level is
n+1. It supplies Noetherianity of the target, compactifiability, finiteness of the
coefficient ring, and an invertible positive annihilator. Smooth tensor duality
identifies the etale exceptional image of the unit with L[2d], where L is etale
locally a free rank-one coefficient module. Apply shifted_line_site_inverse to L
with shift 2d. Its dual shifted by -2d gives both inverse evaluations and is
bounded constructible of finite Tor amplitude, as is L[2d]. The finite exceptional
functor is the specified etale exceptional functor transported through the two
site comparisons. The comparison adjunction unit on the etale coefficient unit
identifies its input with that unit, so its value is the comparison pullback of
L[2d]. Transport the inverse and both evaluations through the intrinsic module
realization equivalence. Its tensor comparison, and uniqueness of derived tensor
on K-flat representatives, identify this tensor with finiteIntrinsicDerivedTensor;
the same realization identifies the unit with finiteConstantCoefficientObject.
Constructibility and the Tor tests are invariant under these equivalences, giving
the recorded finiteTorConstructible predicates. This also covers the empty source:
the module category there is zero, and the coefficient unit is its own inverse. -/
theorem smooth_finite_dualizing_inverse (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d n : ℕ) [SmoothOfRelativeDimension d g] :
    let omega := (clopenFiniteExceptional P P.extension X Y g n).obj
      (finiteConstantCoefficientObject P.coefficients.l P.extension Y.left n)
    finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n)
        X.left omega ∧
      ∃ Q, finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n)
          X.left Q ∧
        Nonempty ((finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).obj
          (omega, Q) ≅ finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ∧
        Nonempty ((finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).obj
          (Q, omega) ≅ finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) := by
  let P' : PurityFiniteSetting.{u} := { P with level := n + 1, level_pos := Nat.succ_pos n }
  obtain ⟨_hX, _hXc, _hXs, _hY, _hYc, _hYs, _hc, _hall,
      hfin, hN, hkill, hunit, _hbase⟩ :=
    finite_setting_comparison_hypotheses P'
      (X.left ↘ Spec (.of P.field.k)) (Y.left ↘ Spec (.of P.field.k)) g
      ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp inferInstance)
  let : Finite P'.Ring := hfin
  let : Finite P'.Coefficient := Finite.of_equiv P'.Ring Equiv.ulift.symm
  let : HasCompactification g :=
    hasCompactification_of_finiteType_over_field P.field.k X.left Y.left g
  have hA : ((P'.coefficients.l ^ P'.level : ℕ) : P'.Coefficient) = 0 := by
    apply ULift.ext
    change ((P'.coefficients.l ^ P'.level : ℕ) : P'.Ring) = 0
    simpa only [nsmul_eq_mul, mul_one] using hkill 1
  let : HasInvertibleExponent P'.Coefficient Y.left :=
    ⟨P'.coefficients.l ^ P'.level, lt_of_lt_of_le Nat.zero_lt_one hN, hA,
      hunit Y.left Y.hom⟩
  let : HasInvertibleExponent P'.Coefficient X.left := .of_hom g
  let : ∀ x : X.left, Invertible (P'.coefficients.l : X.left.residueField x) :=
    fun x ↦ (P.clopenResidue_isUnit X x).invertible
  let W := Etale.dualizingComplex (ModuleCat.{u + 1} P'.Coefficient) g
  have hW : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P'.Coefficient) X.left W :=
    Etale.constructibleFiniteTor_dualizingComplex P'.Coefficient (Y.left ↘ Spec (.of P.field.k)) g
      (Etale.constructibleFiniteTor_unit P'.Coefficient)
  have hI : IsInvertible W :=
    (Etale.isInvertible_iff_exists_derivedTensor W).mpr
      (Etale.isInvertible_dualizingComplex P'.Coefficient (d := d) g)
  let : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  obtain ⟨Q, hQ, ⟨e⟩, ⟨e'⟩⟩ :=
    etale_inverse_ctf P'.Coefficient X.left (X.left ↘ Spec (.of P.field.k)) W hW hI
  let C := finiteHomNu P.coefficients.l P.extension X.left n
  let U : Etale.DerivedCategoryModule P'.Coefficient Y.left := 𝟙_ _
  have hU := Etale.constructibleFiniteTor_unit P'.Coefficient (X := Y.left)
  let eW : (clopenFiniteExceptional P P.extension X Y g n).obj
      (finiteConstantCoefficientObject P.coefficients.l P.extension Y.left n) ≅ C.obj W :=
    exceptional_origin_iso P' X.left Y.left g U hU.1.1.1 _
      (comparison_unit P.coefficients.l P.extension Y.left n).symm
  have hcW := comparison_ctf P' X.left W hW
  have hcQ := comparison_ctf P' X.left Q hQ
  refine ⟨intrinsic_ctf_iso _ _ _ _ _ eW hcW, C.obj Q, hcQ, ?_, ?_⟩
  · exact ⟨(finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).mapIso
        (Iso.prod eW (Iso.refl _)) ≪≫
      comparison_tensor P.coefficients.l P.extension X.left n W Q ≪≫ C.mapIso e ≪≫
      comparison_unit P.coefficients.l P.extension X.left n⟩
  · exact ⟨(finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).mapIso
        (Iso.prod (Iso.refl _) eW) ≪≫
      comparison_tensor P.coefficients.l P.extension X.left n Q W ≪≫ C.mapIso e' ≪≫
      comparison_unit P.coefficients.l P.extension X.left n⟩

end WeilConjectures.PurityFiniteSetting
