/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! Pullback composition and completed reduction on the strict diagram category.
Source: Stacks Project, Tags 0D6D and 0E48.
(blueprint: lem-weil-pbc-completed-reduction-pullback-square) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The integral ringed square retains the specified completed coefficient maps.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-completed-reduction-pullback-square). -/
def AdicCoefficientDatum.integralTowerRingedSquare
    (sq : ChosenCartesianSquare g' f' f g) : StrictTowerRingedSquare sq where
  RY := d.completedRing Y
  RX := d.completedRing X
  RY' := d.completedRing Y'
  RX' := d.completedRing X'
  cf := d.integralRingIso f
  cg := d.integralRingIso g
  cg' := d.integralRingIso g'
  cf' := d.integralRingIso f'
  coherent := d.integral_coherent sq

private theorem kFlat_acyclicTensor {T : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (P : CochainComplex (proEtaleRingModules T R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) : P.IsAcyclicTensorKFlat := by
  unfold CochainComplex.IsAcyclicTensorKFlat
  exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP

/-- Ordinary inverse image preserves flat terms of K-flat complexes. -/
private theorem pullback_flatTerms {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{t + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{t + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{t + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{t + 1}).obj RW ≅ RZ)
    (K : CochainComplex (proEtaleRingModules V RV) ℤ) (hK : K.IsKFlatIndependentCoefficients)
    (hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := RV) (K.X n)) (n : ℤ) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := RW)
      ((((proEtaleRingModulePullback k RV RW ck).mapHomologicalComplex (.up ℤ)).obj K).X n) := by
  obtain ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩, _⟩ :=
    proEtaleCanonicalPullbackComposition_existsUnique h k RV RW RZ ck ch _ rfl
  exact (hc K (kFlat_acyclicTensor K hK) hflat).2.1 n

private theorem reductionIso_level {U V : Scheme.{t}} (q : U ⟶ V)
    (N : reductionModules V (d.completedRing V)) (n : ℕᵒᵖ) :
    (stratumModulePull d q).map (((completedReductionModuleUnit d V).app N).app n) ≫
      ((stratumModuleReductionIso d q).hom.app N).app n =
    ((completedReductionModuleUnit d U).app ((stratumModulePull d q).obj N)).app n := by
  have h := NatTrans.congr_app ((stratumModuleReductionIso_exists d q).exists.choose_spec N) n
  simp only [NatTrans.comp_app, AdicCoefficientDatum.constantPullbackIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp] at h
  exact h


end AlgebraicGeometry.Scheme
