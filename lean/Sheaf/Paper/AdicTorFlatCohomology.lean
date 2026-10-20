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
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.AdicReductionCohomologySequence
import Sheaf.Paper.AdicTorFlatCriterion
import Sheaf.Paper.AdicSuppliedModelFlatCriterion
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses

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

private theorem pbcExtend_flat
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := S)
      ((pbcExtend φ).obj M) := by
  let R' := (adicLisseForget T).obj R
  let S' := (adicLisseForget T).obj S
  let N := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (J := ProEt.topology T) φ M
  obtain ⟨e⟩ := SheafOfModules.nonempty_scalarTensorComparisonOfUniverses.{u + 1, u, u + 1, u + 1}
    (J := ProEt.topology T) φ M
  have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M) := hM.1
  have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M) := hM.2
  have : PreservesFiniteLimits
      (pbcRestrict φ ⋙ SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M ⋙
        SheafOfModules.toSheaf R') := inferInstance
  have : PreservesFiniteColimits
      (pbcRestrict φ ⋙ SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M ⋙
        SheafOfModules.toSheaf R') := inferInstance
  have : PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := S) N ⋙ SheafOfModules.toSheaf S') :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := S) N ⋙ SheafOfModules.toSheaf S') :=
    preservesFiniteColimits_of_natIso e
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} S') := inferInstance
  have hN : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := S) N :=
    ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf S'),
      preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf S')⟩
  have hobj := (pbcExtensionExistence φ).choose_spec.choose M
  exact hobj.symm ▸ hN

private theorem pbcFlat_of_iso
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {M N : pbcModules T R} (e : M ≅ N)
    (h : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) N := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let tensor : MonoidalCategory (pbcModules T R) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let e₁ := SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R M
  let e₂ := SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R N
  let e₃ := (@MonoidalCategory.curriedTensor (pbcModules T R) _ tensor).flip.mapIso e
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso (e₁ ≪≫ e₃ ≪≫ e₂.symm) h

private theorem pbcFlat_zero (T : Scheme.{u}) {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : pbcModules T R) (hM : IsZero M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.tensorPreadditive R
  apply (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm
  have hz : IsZero (MonoidalCategory.tensorRight M) := by
    rw [Functor.isZero_iff]
    intro N
    exact (MonoidalCategory.tensorLeft N).map_isZero hM
  exact ⟨⟨fun _ _ _ ↦ (MonoidalCategory.tensorRight M).preservesLimitsOfShape_of_isZero hz _⟩,
    ⟨fun _ _ _ ↦ (MonoidalCategory.tensorRight M).preservesColimitsOfShape_of_isZero hz _⟩⟩
private theorem pbcFlat_single_kflat (T : Scheme.{u})
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : pbcModules T R)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M) :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology T) (R := R)
      ((CochainComplex.singleFunctor _ 0).obj M) := by
  classical
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R ((CochainComplex.singleFunctor _ 0).obj M) 0
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_obj_X_self] using hM
  · exact pbcFlat_zero T _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
private theorem pbcFlat_scalar_single (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R)
    (hM : SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M)
    (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let P := (CochainComplex.singleFunctor _ 0).obj M
  have hk := pbcFlat_single_kflat T M hM
  have : IsIso ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P)) :=
    pbcExtensionCounit_isIso φ P hk
  let e₁ := (pbcDerivedExtend φ).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M)
  let e₂ := asIso ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P))
  let e₃ := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (pbcExtend φ) (.up ℤ) 0).app M)
  let e := e₁ ≪≫ e₂ ≪≫ e₃
  have hz := DerivedCategory.isZero_of_isGE
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((pbcExtend φ).obj M))) 0 i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)

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
  intro n q
  let d := pbcPadicCoefficientDatum l E
  let B := pbcAdicCompletion T d
  let S := (pbcAdicRings T d).obj (op n)
  let φ := pbcAdicProjection T d n
  let c := pbcCohomologyScalarExtension T φ K.obj q
  obtain ⟨f, hf, hseq⟩ := pbc_adic_reduction_cohomology_sequence T l E n
  obtain ⟨δ, hδ, hs⟩ := hseq K.obj q
  let H := (DerivedCategory.homologyFunctor _ (q + 1)).obj K.obj
  have : Mono f := hf
  have : PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight (J := ProEt.topology T) (A := B) H) :=
    (_hflat (q + 1)).1
  have : Mono ((SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := B) H).map f) := inferInstance
  have hc : IsIso ((pbcRestrict φ).map c) :=
    hs.isIso_f_iff.mpr (isZero_kernel_of_mono _)
  have : IsIso ((SheafOfModules.toSheaf ((adicLisseForget T).obj B)).map
      ((pbcRestrict φ).map c)) := inferInstance
  have hc' : IsIso c := by
    have : IsIso ((SheafOfModules.toSheaf ((adicLisseForget T).obj S)).map c) :=
      inferInstanceAs (IsIso ((SheafOfModules.toSheaf ((adicLisseForget T).obj B)).map
        ((pbcRestrict φ).map c)))
    exact isIso_of_reflects_iso c (SheafOfModules.toSheaf ((adicLisseForget T).obj S))
  refine ⟨hc', ?_⟩
  have hflatS := pbcFlat_of_iso T (asIso c) (pbcExtend_flat T φ
    ((DerivedCategory.homologyFunctor _ q).obj K.obj) (_hflat q))
  exact hflatS

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
  constructor
  · constructor
    · exact pbc_adic_tor_implies_flat_cohomology T _hdim l E _hl K
    · intro hflat m n q _hq p hp
      have hred := pbc_adic_flat_cohomology_reduction T l E _hdim _hl K hflat
        (n + 1) q
      exact pbcFlat_scalar_single T
        (pbcAdicQuotient T (pbcPadicCoefficientDatum l E) (n + 1) n (Nat.le_succ n))
        _ hred.2 (-(p : ℤ)) (by omega)
  · exact pbc_adic_flat_iff_supplied_model_flat T _hdim l E _hl K

end AlgebraicGeometry.Scheme
