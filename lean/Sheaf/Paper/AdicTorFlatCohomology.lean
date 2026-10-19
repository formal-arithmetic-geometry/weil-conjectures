/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.LevelwiseAdicTruncations
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.AdicLisseModule
import Sheaf.Paper.RefinementCoefficientRealization
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Paper.TorsionLimitSheafCompleteness
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Higher Tor and flat cohomology for complete integral coefficients

Source: Weil blueprint, sec-smooth-base-change/sk-rem-rest,
`thm-weil-pbc-integral-truncations`, hypothesis paragraph
(blueprint: lem-weil-pbc-adic-tor-flat-cohomology).

The completed and finite coefficient actions are retained. Index n denotes exponent n+1.
The common-model condition quantifies over whole supplied systems of models on finite
stratifications and covering sieves, rather than over terms of a chosen representative.
The reduction map is constructed from the tensor-unit normalized adjunctions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The canonical map H^q(K) tensor S to H^q(K tensor^L S): apply cohomology to the
unit K → Res(K tensor^L S), commute cohomology with exact scalar restriction, and take
its ordinary scalar-extension adjunct. Thus it is the actual cocycle reduction map,
not an arbitrarily chosen isomorphism. Source: blueprint hypothesis paragraph, and
Stacks Tags 03EK and 06YY (blueprint: lem-weil-pbc-adic-tor-flat-cohomology). -/
def pbcCohomologyScalarExtension
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (q : ℤ) :
    (pbcExtend φ).obj ((DerivedCategory.homologyFunctor _ q).obj K) ⟶
      (DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K) :=
  ((pbcScalarAdjunction φ).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ q).map
        ((pbcDerivedScalarAdjunction φ).unit.app K) ≫
      ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
        ((pbcDerivedExtend φ).obj K))

/-- Flatness of cohomology on every supplied system of common local models of the
canonical reduction tower. The bounds, stratification, covering sieves and all their
models are supplied together, exactly as in the uniform-constructibility definition.
Each flatness test uses the actual inverse-image completed ring. Source: blueprint
hypothesis paragraph (blueprint: lem-weil-pbc-adic-tor-flat-cohomology). -/
def PbcSuppliedModelCohomologyFlat (K : PbcCompletedDerived T d) : Prop :=
  ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : LocallyClosedStratification T)
    (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
    (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
    ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt),
        V α f → AdicTowerLocalModel d (U.hom ≫ S.immersion α)
          (pbcReductionAdicTower T d K) d₀ d₁,
      ∀ (α : Fin S.n) (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt)
        (hf : V α f) (q : ℤ),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
          (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj (pbcAdicCompletion T d))
          ((DerivedCategory.homologyFunctor _ q).obj
            (DerivedCategory.Q.obj (L α U f hf).complex))

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- All-cutoff higher Tor, ambient flat cohomology and flat cohomology of every supplied
common local model are equivalent. Source: blueprint integral truncations, hypothesis
paragraph (blueprint: lem-weil-pbc-adic-tor-flat-cohomology).

Proof:
1. The DVR structure and completed coefficient reduction give the two-term free
resolution [B --varpi^n--> B] of R_n. Immersion and slice restrictions preserve these
coefficients, cohomology and the ordinary and derived tensor products.
2. Flatness descends along the finite stratum covers: restrict a tensor kernel and use
noetherian stratum detection; tensor preserves cokernels by the tensor/Hom adjunction.
3. If ambient cohomology is flat, the quotient triangle and its long exact sequence
kill the varpi-power kernel in the next cohomology, giving the canonical reduction map.
4. Scalar extension of a flat sheaf is flat. Degree-zero flat sheaves are K-flat,
so all the negative cohomology defining positive Tor vanishes.
5. Conversely, the integral stratified perfect characterization supplies bounded finite
projective A-models on a finite stratum cover, and the Tor condition restricts to them.
6. Downward Smith-normal-form induction splits such a model into one-term free modules
and two-term [A --varpi^e--> A] blocks; the blocks with e=0 are contractible.
7. A positive-exponent block, at n≥e, has a cohomology summand A/varpi^e whose Tor_1 for
R_(n+1)→R_n is (A/varpi)_U, by the alternating varpi^n,varpi free resolution. It is
nonzero on nonempty U, contradicting the assumed Tor vanishing.
8. The remaining blocks have finite free cohomology. Descend their flatness using step 2;
the empty-scheme case has only zero module sheaves.
9. Every supplied bounded adic-lisse model is complete by torsion-limit completeness
and the constant/completed equivalence. Exact product-preserving restriction preserves
ambient completeness via the Roos triangle.
10. Normalization-compatible model identifications lift to an isomorphism of derived
strict towers by sequential evaluation fullness. Derived limits and Koszul
reconstruction identify each model with the restriction of K.
11. These cohomology identifications transport ambient flatness to every supplied model;
conversely choose a supplied system and descend flatness by step 2. No uniqueness of the
strict-tower lift, nonempty stratum, or nonzero complex is required. -/
theorem pbc_adic_tor_flat_cohomology
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    ((∀ m : ℤ, PbcLevelwiseTorVanishing T (pbcPadicCoefficientDatum l E)
        (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) m) ↔
      ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ∧
    ((∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ↔
      PbcSuppliedModelCohomologyFlat T (pbcPadicCoefficientDatum l E) K.obj) := by
  sorry

/-- Under the equivalent conditions, the canonical cohomology reduction map is an
isomorphism and the reduced cohomology is flat over its own quotient coefficient sheaf.
Source: blueprint integral truncations, hypothesis paragraph
(blueprint: lem-weil-pbc-adic-tor-flat-cohomology).
Proof: steps 3 and 4 of this node's proof. Resolve the quotient sheaf by multiplication
by the uniformizer power. The cohomology long exact sequence identifies the cokernel
with reduced cohomology because flatness kills the next cohomology's power-torsion.
The first arrow sends a cocycle z to z tensor 1, so it is precisely the adjunct of the
derived tensor unit used in pbcCohomologyScalarExtension. Its scalar-extension source
is the ordinary tensor. Balancing shows scalar extension preserves flatness; transfer
this flatness across the canonical isomorphism. -/
theorem pbc_adic_flat_cohomology_reduction
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E))
    (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
      ((DerivedCategory.homologyFunctor _ q).obj K.obj)) :
    ∀ (n : ℕ) (q : ℤ),
      IsIso (pbcCohomologyScalarExtension T
        (pbcAdicProjection T (pbcPadicCoefficientDatum l E) n) K.obj q) ∧
      SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := (pbcAdicRings T (pbcPadicCoefficientDatum l E)).obj (op n))
        ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T (pbcPadicCoefficientDatum l E) n).obj K.obj)) := by
  sorry

end AlgebraicGeometry.Scheme
