/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.IntegralModelOpenClosedPieces
public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.Paper.FiniteModelStratumFiltration
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.ScalarLocalizationModuleColimit
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Topology.NoetherianSpace

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

/-- The actual closed direct image followed by open extension by zero.
Source: Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-per-rational-stratum-integral-models). -/
def piece {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :=
  continuousModuleDirectImage t A ⋙ continuousModuleExtensionByZero U A

open Classical in
/-- The generator indexed by a factorization through the open, followed by the actual
module-sheafification unit. Closed direct image evaluates on the base change.
Source: Stacks Tag 03DI; Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-per-rational-stratum-integral-models). -/
def generator {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing S A))
    (W : X.ProEt) (φ : W ⟶ U)
    (s : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj
      ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))) :
    ((piece U t A).obj N).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (latticeModuleRing X A).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf (latticeModuleRing X A) U).obj
        ((openSliceModules U A).obj ((continuousModuleDirectImage t A).obj N)))).app
          (op W) (DirectSum.of _ φ s)

/-- A pure tensor in ordinary integral-to-field change of rings, followed by
sheafification. Source: Stacks Tag 03EK; Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-per-rational-stratum-integral-models). -/
def tensorSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    (W : X.ProEt) (a : WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
    (s : N.val.obj (op W)) : (integralModelRationalize l E X N).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj)
      ).unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap X l E) N)).app (op W)
          ((ULift.up (ContinuousMap.const W.left a)) ⊗ₜ[
            (latticeCoefficientSheaf X (latticeCoefficientIntegers l E)).obj.obj (op W),
              ((integralLatticeCoefficientMap X l E).hom.app (op W)).hom] s)

/-- The actual finite-level coefficient comparison, normalized on residue representatives.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-per-rational-stratum-integral-models). -/
def finiteComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :=
  (Scheme.pbcLevelConstantComparison X (Scheme.pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).mapIso
      (Scheme.integralCoefficientULift l E n).toCommRingCatIso ≪≫
    (Scheme.discreteContinuousCoefficientIso X).app (Scheme.finiteCoefficientRing l E n)

/-- Completed membership in degree zero, with the coefficient identification fixed by
all finite residue maps. The predicate used is the published three-clause predicate,
including compatible etale origins. No completion or model is substituted for N.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-per-rational-stratum-integral-models). -/
def IsCompletedModel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :
    Prop :=
  ∃ b : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (latticeCoefficientIntegers l E),
    (∀ (n : ℕ) (W : X.ProEt) (s : (latticeCoefficientSheaf X
        (latticeCoefficientIntegers l E)).obj.obj (op W)) (x : W.left),
      (Scheme.finiteContinuousCoefficientValue l E X n (op W)
        ((b.inv ≫ Scheme.pbcAdicProjection X (Scheme.pbcIntegralDatum l E) n ≫
          (finiteComparison l E X n).hom).hom.app (op W) s) x).down =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          ⟨WithAbs.ofAbs (s.down x).val, (s.down x).property⟩) ∧
    Scheme.PbcIsBoundedConstructibleComplete X (Scheme.pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.pbcRestrict b.hom).obj N))

/-- The chosen uniformizer viewed in the continuous field coefficient type.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-per-rational-stratum-integral-models). -/
def uniformizer (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    WithAbs (Padic.coefficientExtensionAbsoluteValue l E) :=
  (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).symm
    (Padic.coefficientExtensionUniformizer l E).val

/-- The ordinary scalar comparison is fixed on all sequential-localization fractions
of all extension-by-zero generators. The underlying closed direct-image section is
on the actual base change. The formula is precisely h/varpi^n mapped to its image
under the two exact module functors, and determines the comparison by sheafification
and the localization colimit universal property.
Source: Bhatt--Scholze, Lemmas 6.8.2(2) and 6.8.13; Stacks Tags 03DI and 03DJ
(blueprint: lem-per-rational-stratum-integral-models). -/
def IsNormalizedComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (N : SheafOfModules.{u + 1} (latticeModuleRing S (latticeCoefficientIntegers l E)))
    (e : integralModelRationalize l E X
        ((piece U t (latticeCoefficientIntegers l E)).obj N) ≅
      (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
        (integralModelRationalize l E S N)) : Prop :=
  ∀ (n : ℕ) (W : X.ProEt) (φ : W ⟶ U)
    (s : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj
      ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))),
    e.hom.val.app (op W)
      (tensorSection l E X ((piece U t (latticeCoefficientIntegers l E)).obj N) W
        ((uniformizer l E)⁻¹ ^ n) (generator U t (latticeCoefficientIntegers l E) N W φ s)) =
      generator U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
        (integralModelRationalize l E S N) W φ
        (tensorSection l E S N ((Scheme.proEtaleBaseChange t).obj
          ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))) ((uniformizer l E)⁻¹ ^ n) s)

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
  sorry

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
  sorry

end AlgebraicGeometry.ProEtale.RationalStratum
