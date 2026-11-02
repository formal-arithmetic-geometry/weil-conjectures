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

@[reassoc]
private theorem reductionIso_level {U V : Scheme.{t}} (q : U ⟶ V)
    (N : reductionModules V (d.completedRing V)) (n : ℕᵒᵖ) :
    (stratumModulePull d q).map (((completedReductionModuleUnit d V).app N).app n) ≫
      ((stratumModuleReductionIso d q).hom.app N).app n =
    ((completedReductionModuleUnit d U).app ((stratumModulePull d q).obj N)).app n := by
  have h := NatTrans.congr_app ((stratumModuleReductionIso_exists d q).exists.choose_spec N) n
  simp only [NatTrans.comp_app, AdicCoefficientDatum.constantPullbackIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp] at h
  exact h

/-- The ordinary reduction comparisons paste along any isomorphism of composite
module pullbacks: each is determined by its quotient augmentation. -/
private theorem ordinaryReduction_square
    (σ : stratumModulePull d g ⋙ stratumModulePull d f' ≅
      stratumModulePull d f ⋙ stratumModulePull d g')
    (M : reductionModules Y (d.completedRing Y)) (n : ℕᵒᵖ) :
    (stratumModulePull d f').map (((stratumModuleReductionIso d g).hom.app M).app n) ≫
      ((stratumModuleReductionIso d f').hom.app ((stratumModulePull d g).obj M)).app n ≫
      ((completedReductionModuleTowerFunctor X' d).map (σ.hom.app M)).app n =
    σ.hom.app (((completedReductionModuleTowerFunctor Y d).obj M).obj n) ≫
      (stratumModulePull d g').map (((stratumModuleReductionIso d f).hom.app M).app n) ≫
      ((stratumModuleReductionIso d g').hom.app ((stratumModulePull d f).obj M)).app n := by
  have := stratumModuleUnit_epi d Y M n.unop
  apply (cancel_epi ((stratumModulePull d f').map ((stratumModulePull d g).map
    (((completedReductionModuleUnit d Y).app M).app n)))).1
  rw [← Functor.map_comp_assoc, reductionIso_level d g M n,
    reductionIso_level_assoc d f' ((stratumModulePull d g).obj M) n]
  have hu : ((completedReductionModuleUnit d X').app
        ((stratumModulePull d f').obj ((stratumModulePull d g).obj M))).app n ≫
      ((completedReductionModuleTowerFunctor X' d).map (σ.hom.app M)).app n =
    σ.hom.app M ≫ ((completedReductionModuleUnit d X').app
        ((stratumModulePull d g').obj ((stratumModulePull d f).obj M))).app n :=
    (NatTrans.congr_app ((completedReductionModuleUnit d X').naturality (σ.hom.app M)) n).symm
  have hσ : (stratumModulePull d f').map ((stratumModulePull d g).map
        (((completedReductionModuleUnit d Y).app M).app n)) ≫
      σ.hom.app (((completedReductionModuleTowerFunctor Y d).obj M).obj n) =
    σ.hom.app M ≫ (stratumModulePull d g').map ((stratumModulePull d f).map
        (((completedReductionModuleUnit d Y).app M).app n)) :=
    σ.hom.naturality _
  rw [hu, reassoc_of% hσ, ← Functor.map_comp_assoc, reductionIso_level d f M n,
    reductionIso_level d g' ((stratumModulePull d f).obj M) n]

private theorem whiskeringRight_mapIso_hom_app_app {C D E : Type*} [Category C] [Category D]
    [Category E] {F G : D ⥤ E} (σ : F ≅ G) (T : C ⥤ D) (n : C) :
    (((Functor.whiskeringRight C D E).mapIso σ).hom.app T).app n = σ.hom.app (T.obj n) := rfl

private theorem ordinaryReduction_square_tower
    (σ : stratumModulePull d g ⋙ stratumModulePull d f' ≅
      stratumModulePull d f ⋙ stratumModulePull d g')
    (τ : d.towerModulePull g ⋙ d.towerModulePull f' ≅
      d.towerModulePull f ⋙ d.towerModulePull g')
    (hτ : ∀ T n, (τ.hom.app T).app n = σ.hom.app (T.obj n))
    (M : reductionModules Y (d.completedRing Y)) :
    (d.towerModulePull f').map ((stratumModuleReductionIso d g).hom.app M) ≫
        (stratumModuleReductionIso d f').hom.app ((stratumModulePull d g).obj M) ≫
        (completedReductionModuleTowerFunctor X' d).map (σ.hom.app M) =
      τ.hom.app ((completedReductionModuleTowerFunctor Y d).obj M) ≫
        (d.towerModulePull g').map ((stratumModuleReductionIso d f).hom.app M) ≫
        (stratumModuleReductionIso d g').hom.app ((stratumModulePull d f).obj M) := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, hτ]
  exact ordinaryReduction_square d σ M n

/-- The normalized completed reduction comparisons respect the inverse-image square.
This is an equation before taking mates and in the full derived diagram category.
Source: blueprint completed-exchange-coherence, tensor/pullback coherence in its
first two proof sentences; Stacks Tags 0D6D and 0E48
(blueprint: lem-weil-pbc-completed-reduction-pullback-square).

Proof: take a flat-term K-flat representative P on Y. Its two successive inverse
images remain flat-term K-flat. The canonical geometric composition comparison is
localization of the ordinary compositor whose right-adjoint conjugate is restriction
along Over.pullbackComp. At each coefficient level the ordinary reduction comparison
is tensor balancing; its two composites around the square send a pure tensor to its
inverse image with the same quotient scalar. Naturality of the ring projections and
the quotient transition maps makes this an equality of strict tower-complex maps.
Use the defining normalization equations for completedReductionPullbackIso on all
four edges. The ordinary equality and the factorization equations for derived
pullback give the displayed equation after cancellation of the invertible K-flat
counits. Finally resolve an arbitrary M by P and use naturality across the resulting
quasi-isomorphism. This proves equality of strict derived maps, without assuming
that derived evaluation is faithful. Zero complexes, zero coefficient rings and
empty schemes satisfy the same tensor formulas. -/
theorem completedReductionPullback_square
    (sq : ChosenCartesianSquare g' f' f g) :
    Functor.whiskerRight (d.reductionTowerPullbackIso g).hom (d.towerPull f') ≫
      Functor.whiskerLeft (d.pull g) (d.reductionTowerPullbackIso f').hom ≫
      Functor.whiskerRight
        (proEtaleAmbientRingedPullbackComparison sq
          (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
          (d.integralRingIso f) (d.integralRingIso g) (d.integralRingIso g')
          (d.integralRingIso f') (d.integral_coherent sq)).hom
        (completedReductionTower X' d) =
    Functor.whiskerLeft (completedReductionTower Y d)
        (d.integralTowerRingedSquare sq).exchangeTowerSquare.hom ≫
      Functor.whiskerRight (d.reductionTowerPullbackIso f).hom (d.towerPull g') ≫
      Functor.whiskerLeft (d.pull f) (d.reductionTowerPullbackIso g').hom := by
  have hamb : proEtaleAmbientRingedPullbackComparison sq
      (d.completedRing X) (d.completedRing Y) (d.completedRing X') (d.completedRing Y')
      (d.integralRingIso f) (d.integralRingIso g) (d.integralRingIso g')
      (d.integralRingIso f') (d.integral_coherent sq) =
      Functor.mapDerivedCategorySquareIso (d.integralTowerRingedSquare sq).exchangeModuleSquare :=
    (d.integralTowerRingedSquare sq).ambientSquare_localization
  rw [hamb]
  let σ : stratumModulePull d g ⋙ stratumModulePull d f' ≅
      stratumModulePull d f ⋙ stratumModulePull d g' :=
    (d.integralTowerRingedSquare sq).exchangeModuleSquare
  let good : ObjectProperty (CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y) (R := d.completedRing Y) (P.X n)
  have res (L : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
      ∃ P, ∃ p : P ⟶ L, good P ∧ QuasiIso p := by
    obtain ⟨P, p, hP, hflat, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := d.completedRing Y) L
    exact ⟨P, p, ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (d.completedRing Y) (P.X n)).symm
        (hflat n)⟩, hp⟩
  have hcounit (T : Scheme.{t}) : (fun P ↦ (stratumComplexCounit d T).app P) =
      completedReductionTowerComplexCounit T d := funext (stratumComplexCounit_app d T)
  have spec {U V : Scheme.{t}} (q : U ⟶ V) :
      StratumReductionFormula d q (d.reductionTowerPullbackIso q) :=
    (completedReductionPullbackIso_existsUnique d q).choose_spec.1
  have hf_flat (P) (hP : good P) (n : ℤ) := pullback_flatTerms g' f
    (d.completedRing Y) (d.completedRing X) (d.completedRing X')
    (d.integralRingIso f) (d.integralRingIso g') P hP.1 hP.2 n
  refine derivedReductionSquare_paste
    (stratumModulePull d g) (stratumModulePull d f') (stratumModulePull d f)
    (stratumModulePull d g')
    (d.towerModulePull g) (d.towerModulePull f') (d.towerModulePull f) (d.towerModulePull g')
    (completedReductionModuleTowerFunctor Y d) (completedReductionModuleTowerFunctor Y' d)
    (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor X' d)
    (completedReductionTower Y d) (completedReductionTower Y' d)
    (completedReductionTower X d) (completedReductionTower X' d)
    (stratumComplexCounit d Y) (stratumComplexCounit d Y')
    (stratumComplexCounit d X) (stratumComplexCounit d X')
    (stratumModuleReductionIso d g) (stratumModuleReductionIso d f')
    (stratumModuleReductionIso d f) (stratumModuleReductionIso d g')
    (d.reductionTowerPullbackIso g) (d.reductionTowerPullbackIso f')
    (d.reductionTowerPullbackIso f) (d.reductionTowerPullbackIso g')
    σ ((Functor.whiskeringRight ℕᵒᵖ (reductionModules Y (d.completedRing Y))
      (reductionModules X' (d.completedRing X'))).mapIso σ)
    good res ?_ ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [hcounit, hcounit]
    exact spec g P hP.1
  · intro P hP
    rw [hcounit, hcounit]
    exact spec f' _ (stratumPull_flatKFlat d g P hP.1 hP.2)
  · intro P hP
    rw [hcounit, hcounit]
    exact spec f P hP.1
  · intro P hP
    rw [hcounit, hcounit]
    exact spec g' _ (stratumPull_flatKFlat d f P hP.1 hP.2)
  · intro P hP
    rw [stratumComplexCounit_app]
    exact towerCounit_isIso X' d _ (stratumPull_flatKFlat d g' _
      (stratumPull_flatKFlat d f P hP.1 hP.2) (hf_flat P hP))
  · intro M
    apply NatTrans.ext
    funext n
    exact ordinaryReduction_square d σ M n

end AlgebraicGeometry.Scheme
