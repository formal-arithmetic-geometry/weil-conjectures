/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalStratumIntegralModelBasic
public import WeilConjectures.AlgebraicGeometry.IntegralModelOpenClosedPieces
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralConstructibleComparison
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientComparison
import WeilConjectures.AlgebraicGeometry.LisseEConstructibleIntegralLattice
import WeilConjectures.AlgebraicGeometry.ContinuousFiltrationAdmissibleStrata
import WeilConjectures.AlgebraicGeometry.IntegralPieceCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.RationalContinuousFiniteFreeCriterion
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement

/-! # Filtration quotients with completed integral models

Source: Bhatt--Scholze, Definitions 6.8.6 and 6.8.10, Proposition 6.8.11(3),
Lemma 6.8.13 and Proposition 6.8.14(2), pp. 60--62
(blueprint: lem-per-rational-stratum-integral-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.RationalStratum

/-- Constructible rational sheaves have finite filtrations with genuine completed
integral models for the open/closed stratum quotients. IsCompletedModel retains
completeness, uniform constructible reductions and compatible etale-origin witnesses.
The integral sheaves are constructible; they need not be lisse or torsion-free.
Source: Bhatt--Scholze, Definitions 6.8.6 and 6.8.10, Proposition 6.8.11(3),
Lemma 6.8.13 and Proposition 6.8.14(2), pp. 60--62
(blueprint: lem-per-rational-stratum-integral-models).

Proof following the seven node steps:
1. Identify completed and continuous coefficients by
lem-weil-pbc-continuous-coefficients-immersion-restriction. The continuous realization
isomorphism (lem-weil-pbc-continuous-coefficient-realizations) and the internal/sectionwise
module equivalence identify finite free models with finite constant models solely to
apply the filtration lemma.
2. Noetherian closed subsets satisfy the descending-chain condition by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Apply
lem-sfb-finite-model-stratum-filtration. Over E its finitely presented stratum models
are finite free, hence lisse. Its monic maps give the filtration below.
3. Immersions are locally of finite type (lem-weil-pbc-immersion-base-change-lft).
pqf-lem-locnoeth-lft makes their sources locally noetherian; compactness of every subset
(lem-sfb-noetherian-space-compact-subsets) makes them noetherian. Closures in X embed
strict irreducible chains, bounding dimensions. Units restrict along local-ring maps.
4. Apply lem-weil-pbc-lisse-e-constructible-integral-lattice on every stratum to get N
and its specified rationalization isomorphism, with finitely presented scalar models.
5. Apply lem-weil-pbc-integral-model-open-closed-pieces to the closed part and zero on
its complement, then to the resulting open part and zero on its complement. This
makes the actual piece v_! t_* N constructible and gives both scalar comparisons.
6. Its degree-zero complex has bounded constructible cohomology. Condition (iii)
implies (i) of lem-weil-pbc-integral-stratified-perfect-characterization puts it in
the completed category with the full witnesses. Normalize the coefficient comparison
by its finite residue maps, as in IsCompletedModel.
7. lem-weil-pbc-scalar-localization-module-colimit identifies scalar extension with
the repeated-uniformizer colimit with nth leg h mapped to varpi^(-n) tensor h. The
actual closed functor preserves this filtered colimit on qcqs schemes by
lem-weil-pbc-proetale-ringed-open-closed; the open functor preserves it by adjunction.
Their linearity preserves its transition maps. On every open-extension generator
the induced comparison is the formula IsNormalizedComparison. The colimit universal
property makes it equal to the separate open/closed comparisons. Compose with the
lattice isomorphism for the claimed comparison with v_! t_* L.
Empty schemes, the empty filtration, zero sheaves, torsion lattices and nonreduced X
are all included. -/
theorem exists_filtration_integral_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (F : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (_hF : IsContinuousConstructible X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) F) :
    ∃ (m : ℕ)
      (H : Fin (m + 1) → SheafOfModules.{u + 1}
        (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
      (a : ∀ k, H k ⟶ F) (d : ∀ k : Fin m, H k.castSucc ⟶ H k.succ),
      (∀ k, Mono (a k)) ∧ IsZero (H 0) ∧ IsIso (a (Fin.last m)) ∧
      (∀ k : Fin m, d k ≫ a k.succ = a k.castSucc) ∧
      (∀ k : Fin m, Mono (d k)) ∧
      ∃ (U : Fin m → X.ProEt) (S : Fin m → Scheme.{u})
        (t : ∀ k : Fin m, S k ⟶ (U k).left)
        (hS : ∀ k : Fin m, IsNoetherian (S k))
        (L : ∀ k : Fin m, SheafOfModules.{u + 1}
          (latticeModuleRing (S k) (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
        (N : ∀ k : Fin m, SheafOfModules.{u + 1}
          (latticeModuleRing (S k) (latticeCoefficientIntegers l E))),
        (∀ k, IsOpenImmersion (U k).hom ∧ QuasiCompact (U k).hom ∧
          QuasiSeparated (U k).hom ∧ IsClosedImmersion (t k) ∧ IsReduced (S k)) ∧
        (∀ k, (∃ n : ℕ, topologicalKrullDim (S k) ≤ n) ∧
          ∀ x : S k, IsUnit (l : (S k).presheaf.stalk x)) ∧
        (∀ k, (L k).IsFiniteLocallyFree) ∧
        (∀ k, @IsContinuousConstructible (S k)
          (@IsNoetherian.noetherianSpace (S k) (hS k)) (latticeCoefficientIntegers l E)
          inferInstance inferInstance inferInstance (N k)) ∧
        (∀ k, IsContinuousConstructible X (latticeCoefficientIntegers l E)
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k))) ∧
        (∀ k, IsCompletedModel l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k))) ∧
        ∃ (α : ∀ k, integralModelRationalize l E (S k) (N k) ≅ L k)
          (_q : ∀ k, cokernel (d k) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj (L k))
          (e : ∀ k, integralModelRationalize l E X
              ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
                (integralModelRationalize l E (S k) (N k))),
          (∀ k, IsNormalizedComparison l E (U k) (t k) (N k) (e k)) ∧
          ∃ β : ∀ k, integralModelRationalize l E X
              ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
            (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj (L k),
            ∀ k, β k = e k ≪≫ (piece (U k) (t k)
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).mapIso (α k) := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let hnorm : NormedAlgebra ℚ_[l] K := ⟨fun a x ↦ by
    change spectralNorm ℚ_[l] E (a • x.ofAbs) ≤
      ‖a‖ * spectralNorm ℚ_[l] E x.ofAbs
    exact (spectralNorm_smul a (Algebra.IsAlgebraic.isAlgebraic x.ofAbs)).le⟩
  have hfinite : FiniteDimensional ℚ_[l] K := Module.Finite.equiv
    (WithAbs.linearEquiv ℚ_[l] (Padic.coefficientExtensionAbsoluteValue l E)).symm
  have hfree : ∃ s : X.FiniteLocallyClosedStratification, ∀ j : Fin s.n,
      ((ContinuousFiltration.pull l K (s.immersion j)).obj F).IsFiniteLocallyFree := by
    obtain ⟨s, hs⟩ := _hF
    refine ⟨s.toFiniteLocallyClosed, fun j ↦ ?_⟩
    change (continuousModulePullback (s.immersion j) K F).IsFiniteLocallyFree
    apply (finiteLocalModels_iff (s.domain j) K _).mp
    have hm (P : ModuleCat.{u + 1} (ULift.{u + 1} K)) :
        continuousCoefficientModule (s.domain j) K P =
          (model (s.domain j) K).obj P :=
      (Scheme.reductionChange_obj_eq (s.domain j)
        (continuousCoefficientConstantMap (s.domain j) K) _).symm
    dsimp only [K] at hm ⊢
    simpa only [hm] using hs j
  obtain ⟨_, _, _, _, m, V, hV, hV0, hVlast, S, t, ht, hgeomV, hgeomS,
      hmono, hzero, hiso, d, hd, hmd, hq⟩ :=
    @exists_continuousFiltration_admissibleStrata l inferInstance K inferInstance hnorm
      hfinite X inferInstance _hdim _hl F hfree
  let U (k : Fin m) : X.ProEt := Scheme.ProEt.mk (V k.succ).ι
  let L (k : Fin m) :=
    (ContinuousFiltration.pull l K (t k)).obj
      ((ContinuousFiltration.pull l K (V k.succ).ι).obj F)
  have (k : Fin m) : IsNoetherian (S k) := (hgeomS k).1
  have hdimS (k : Fin m) : ∃ n : ℕ, topologicalKrullDim (S k) ≤ n := by
    obtain ⟨n, hn⟩ := _hdim
    exact ⟨n, (hgeomS k).2.1.trans hn⟩
  have (k : Fin m) : (L k).IsFiniteLocallyFree := (hgeomS k).2.2.2.2.2
  have hlattice (k : Fin m) := exists_constructible_integral_lattice l E (S k)
    (hdimS k) (hgeomS k).2.2.1 (L k)
  choose N hN α using hlattice
  have hp (k : Fin m) :
      IsContinuousConstructible X (latticeCoefficientIntegers l E)
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ∧
      IsCompletedModel l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ∧
      ∃ e : integralModelRationalize l E X
          ((piece (U k) (t k) (latticeCoefficientIntegers l E)).obj (N k)) ≅
          (piece (U k) (t k) K).obj (integralModelRationalize l E (S k) (N k)),
        IsNormalizedComparison l E (U k) (t k) (N k) e := by
    have : IsNoetherian (U k).left := (hgeomV k.succ).1
    have : IsOpenImmersion (U k).hom := inferInstanceAs (IsOpenImmersion (V k.succ).ι)
    have : QuasiCompact (U k).hom := (hgeomV k.succ).2.2.2.1
    have : QuasiSeparated (U k).hom := (hgeomV k.succ).2.2.2.2
    have : IsClosedImmersion (t k) := (ht k).1
    have hdimV : ∃ n : ℕ, topologicalKrullDim (U k).left ≤ n := by
      obtain ⟨n, hn⟩ := _hdim
      exact ⟨n, (hgeomV k.succ).2.1.trans hn⟩
    obtain ⟨_, hc, ⟨dc, ec, c, hnorm, hnat⟩, _⟩ :=
      integralPieceCompletionNormalization l E X _hdim _hl (U k) hdimV
        (hgeomV k.succ).2.2.1 (hdimS k) (hgeomS k).2.2.1 (t k)
        (TopologicalSpace.NoetherianSpace.isCompact _)
    exact ⟨(hc (N k) (hN k)).2.1, (hc (N k) (hN k)).2.2.2.2,
      c (N k) (hN k), (hnorm (N k) (hN k)).2.2.2.1⟩
  choose hconstruct hcomplete e he using hp
  refine ⟨m, fun k ↦ (ContinuousFiltration.piece K (V k)).obj F,
    fun k ↦ ContinuousFiltration.counit K (V k) F, d,
    hmono, hzero, hiso, hd, hmd, U, S, t, inferInstance, L, N, ?_, ?_,
    inferInstance, hN, hconstruct, hcomplete, fun k ↦ (α k).some, ?_, e, he,
    fun k ↦ e k ≪≫ (piece (U k) (t k) K).mapIso (α k).some, fun _ ↦ rfl⟩
  · intro k
    exact ⟨inferInstanceAs (IsOpenImmersion (V k.succ).ι),
      (hgeomV k.succ).2.2.2.1, (hgeomV k.succ).2.2.2.2,
      (ht k).1, (ht k).2.1⟩
  · intro k
    exact ⟨hdimS k, (hgeomS k).2.2.1⟩
  · intro k
    exact (hq k).some

/-- Continuous constructible integral modules give completed degree-zero models with
all residue projections normalized. Compare the two finite coefficient towers, identify
finite constant sheaves through their sheafification units, and transport the local
finitely presented models by the scalar-compatible coefficient isomorphism. The
stratified-perfect characterization then supplies the full completed predicate.
Source: Bhatt--Scholze, Lemma 6.8.2(1), Definition 6.8.10 and Proposition 6.8.11(3)
(blueprint: lem-per-rational-stratum-integral-models). -/
private theorem completedModel_of_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hlStalk : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    (hN : IsContinuousConstructible X (latticeCoefficientIntegers l E) N) :
    IsCompletedModel l E X N := by
  classical
  have hl : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hlStalk x
  obtain ⟨i, hi⟩ := Scheme.continuousCoefficientCompletion l E X
  let b := completedIso X l E
  let k := integerSheafIso X l E
  let c := b ≪≫ i.symm ≪≫ k.symm
  have hsc : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (liftedIntegerEquiv l E).toCommRingCatIso.hom ≫
      Scheme.pbcCompletedScalar X (Scheme.pbcIntegralDatum l E) =
      continuousCoefficientConstantMap X (latticeCoefficientIntegers l E) ≫ c.inv := by
    apply (cancel_mono b.hom).mp
    change _ ≫ b.hom = _ ≫ (k.hom ≫ i.hom ≫ b.inv) ≫ b.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply limit.hom_ext
    intro n
    dsimp only [b]
    simp only [Category.assoc]
    rw [completedIso_scalar X l E n.unop]
    obtain ⟨q, hq, hiq⟩ := hi n.unop
    apply (cancel_mono q.hom).mp
    apply ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (latticeCoefficientIntegers l E)))) _).injective
    simp only [← Functor.map_comp, constantSheaf, Functor.comp_map, Category.assoc]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [continuousCoefficientConstantMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    let : TopologicalSpace (Scheme.finiteCoefficientRing l E n.unop) := ⊥
    let : DiscreteTopology (Scheme.finiteCoefficientRing l E n.unop) := ⟨rfl⟩
    apply ContinuousMap.ext
    intro x
    change Scheme.finiteContinuousCoefficientValue l E X n.unop V
      (q.hom.hom.app V ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (Scheme.finiteCoefficientRing l E n.unop))).app V _))
          x = _
    rw [hq]
    change Scheme.integralCoefficientULift l E n.unop
      (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a)) = _
    have hu : Scheme.integralCoefficientULift l E n.unop
        (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a)) =
        ULift.up (Ideal.Quotient.mk _ ((liftedIntegerEquiv l E) a).down) :=
      (Scheme.integralCoefficientULift_exists l E n.unop).exists.choose_spec _
    rw [hu]
    apply ULift.ext
    exact (hiq V (k.hom.hom.app V
      ((continuousCoefficientConstants X (latticeCoefficientIntegers l E)).app V a)) x).symm
  refine ⟨c, ?_, ?_⟩
  · intro n W s x
    have hb : b.inv ≫ Scheme.pbcAdicProjection X (Scheme.pbcIntegralDatum l E) n ≫
        (finiteComparison l E X n).hom =
        limit.π (Scheme.finiteCoefficientTower l X E) (op n) ≫
          ((Scheme.discreteContinuousCoefficientIso X).app
            (Scheme.finiteCoefficientRing l E n)).hom := by
      simp only [b, completedIso, Iso.trans_inv, Iso.symm_inv, finiteComparison,
        Iso.trans_hom, Iso.symm_hom, Scheme.pbcAdicProjection,
        Scheme.pbcCompletedComparison, Category.assoc,
        HasLimit.isoOfNatIso_hom_π_assoc, HasLimit.isoOfNatIso_inv_π_assoc]
      simp only [asIso_inv, NatIso.isIso_inv_app]
      change limit.π (Scheme.finiteCoefficientTower l X E) (op n) ≫
        inv ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (Scheme.integralCoefficientULift l E n).toCommRingCatIso.hom) ≫
        (Scheme.pbcLevelConstantComparison X (Scheme.pbcIntegralDatum l E) n).hom ≫
        (Scheme.pbcLevelConstantComparison X (Scheme.pbcIntegralDatum l E) n).inv ≫
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (Scheme.integralCoefficientULift l E n).toCommRingCatIso.hom ≫ _ = _
      simp only [Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
    obtain ⟨q, hq, hiq⟩ := hi n
    have hq' : q = (Scheme.discreteContinuousCoefficientIso X).app
        (Scheme.finiteCoefficientRing l E n) := by
      apply Iso.ext
      apply Sheaf.hom_ext
      apply sheafify_hom_ext _ _ _
        (Scheme.finiteContinuousCoefficientSheaf l X E n).property
      apply NatTrans.ext
      funext V
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      let : TopologicalSpace (Scheme.finiteCoefficientRing l E n) := ⊥
      let : DiscreteTopology (Scheme.finiteCoefficientRing l E n) := ⟨rfl⟩
      apply ContinuousMap.ext
      intro y
      exact (hq V a y).trans (by
        symm
        exact congrArg (fun f : C(V.unop.left, Scheme.finiteCoefficientRing l E n) ↦ f y)
          (congrArg (fun f ↦ f.app V a)
          (Scheme.continuousCoefficientConstantComparison_unit X
            (Scheme.finiteCoefficientRing l E n))))
    rw [hq'] at hiq
    have hc : c.inv ≫ Scheme.pbcAdicProjection X (Scheme.pbcIntegralDatum l E) n ≫
        (finiteComparison l E X n).hom =
        k.hom ≫ i.hom ≫ limit.π (Scheme.finiteCoefficientTower l X E) (op n) ≫
          ((Scheme.discreteContinuousCoefficientIso X).app
            (Scheme.finiteCoefficientRing l E n)).hom := by
      dsimp only [c, Iso.trans_inv, Iso.symm_inv]
      simp only [Category.assoc, hb]
    rw [hc]
    exact hiq (op W) (k.hom.hom.app (op W) s) x
  · let e := CondensedRing.ringModuleEquivalenceOfIso X
      ((Scheme.adicLisseForget X).mapIso c)
    have hfp : Scheme.IsIntegralStratifiedFinitelyPresented X (Scheme.pbcIntegralDatum l E)
        (e.functor.obj N) := by
      obtain ⟨s, hs⟩ := hN
      refine ⟨s, fun j ↦ ?_⟩
      obtain ⟨V, hV, hv⟩ := (localModels_cover_iff_sieve
        (Scheme.ProEt.topology (s.domain j))
        (latticeModuleRing (s.domain j) (latticeCoefficientIntegers l E))
        (fun P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)) ↦
          Module.FinitePresentation _ P)
        (continuousCoefficientModule (s.domain j) (latticeCoefficientIntegers l E))
        (continuousModulePullback (s.immersion j) (latticeCoefficientIntegers l E) N)).mp
          (hs j)
      exact ⟨V, hV, fun U f hf ↦
        (continuousIntegralSliceModelComparison X l E (liftedIntegerEquiv l E) c hsc
          (s.immersion j) N U).mp (hv U f hf)⟩
    have hc := (Scheme.single_complete_iff X l E hdim hl (e.functor.obj N)).mpr hfp
    exact hc

/-- The additional assertion for every lisse sheaf, including its completed degree-zero
integral model. Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.11(3)
(blueprint: lem-per-rational-stratum-integral-models).
Proof: apply lem-weil-pbc-lisse-e-constructible-integral-lattice directly on X. Its model
has finitely presented scalar models on finitely many strata. Apply condition (iii)
implies (i) of lem-weil-pbc-integral-stratified-perfect-characterization to its degree-zero
complex. The finite residue maps normalize the completed/continuous coefficient
identification. This is node proof steps 4 and 6 on X itself. -/
theorem exists_lisse_completed_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)),
      IsContinuousConstructible X (latticeCoefficientIntegers l E) N ∧
      IsCompletedModel l E X N ∧ Nonempty (integralModelRationalize l E X N ≅ L) := by
  obtain ⟨N, hN, eN⟩ := exists_constructible_integral_lattice l E X _hdim _hl L
  exact ⟨N, hN, completedModel_of_constructible l E X _hdim _hl N hN, eN⟩

end AlgebraicGeometry.ProEtale.RationalStratum
