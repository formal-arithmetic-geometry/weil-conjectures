/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Sheaf.Paper.LisseLatticeReducedOpen
import all Sheaf.Paper.ContinuousConstructibleIntegralTransport
import Sheaf.Paper.ContinuousLisseStratifiedLattices
import Sheaf.Paper.ContinuousConstructibleIntegralGluing
import Sheaf.Paper.IntegralContinuousEncodingConstructible

/-!
# A lisse finite-extension sheaf has a constructible integral lattice

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
Definitions 6.8.1, 6.8.3 and 6.8.10; Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-lisse-e-constructible-integral-lattice).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction
  CondensedRing.pullIso CondensedRing.upperStarComp
  CondensedRing.integralScalarMap
  CondensedRing.continuousFieldModuleEquivalence
  CondensedRing.continuousIntegerModuleEquivalence

private theorem internal_lisse_model
    (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj K) T))
    (hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj K) T) P) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff l K) T),
      IsConstructibleModuleObject (condensedRingObj (CondensedRing.integralCoeff l K) T) N ∧
      Nonempty ((Mod.extendScalars
        (coefficientMap (CondensedRing.integralScalarMap l K) T)).obj N ≅ P) := by
  obtain ⟨S, hS⟩ := CondensedRing.continuousLisse_stratified_lattices l K T P hP
  have hmodels (a : Fin S.n) :
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (CondensedRing.integralCoeff l K) T)),
        IsConstructibleModuleObject
          ((upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (CondensedRing.integralCoeff l K) T)) M ∧
        Nonempty ((Mod.extendScalars
          ((upperStar Ab.{u + 1} (S.immersion a)).map
            (coefficientMap (CondensedRing.integralScalarMap l K) T))).obj M ≅
          ((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj P) := by
    obtain ⟨M, hM, ⟨eM⟩⟩ := hS a
    exact CondensedRing.pullbackCoefficient_model (CondensedRing.integralCoeff l K)
      (Profinite.continuousMapRingObj K) (CondensedRing.integralScalarMap l K)
      (X := T) (Y := S.domain a) (S.immersion a) P M hM eM
  exact CondensedRing.continuousConstructible_integral_gluing l K T P S hmodels

/-- A lisse rational sheaf has a constructible integral model, with no global freeness
requirement on that model. `WithAbs` equips the field with its canonical absolute-value
topology and transports its valuation ring; `ULift` changes only the coefficient size.
Source: Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-weil-pbc-lisse-e-constructible-integral-lattice).

Proof:
1. Replace E by an algebra-isomorphic small finite extension K. The spectral
absolute value is invariant under this equivalence, giving isomorphisms of the
integral and rational continuous coefficient sheaves and their scalar map.
2. The section-action equivalence transports L to a locally finite free internal
continuous K-module. The stratified lattice theorem gives integral models on a
finite stratification, using etale-local lattice existence and finite-etale descent.
3. Transport those models to the actual inverse-image coefficient rings. The finite
stratification gluing theorem constructs an internal constructible integral model
whose actual scalar extension is the internal rational module.
4. Encode the integral model sectionwise and transport its coefficients back to E.
Integral constructibility is invariant under this encoding. The scalar-extension
comparison and the rational equivalence's counit give the required isomorphism.
The construction includes empty schemes and rank zero. -/
theorem exists_constructible_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing T (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ N : SheafOfModules.{u + 1} (latticeModuleRing T (latticeCoefficientIntegers l E)),
      IsContinuousConstructible T (latticeCoefficientIntegers l E) N ∧
      Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap T l E) N ≅ L) := by
  classical
  obtain ⟨K, hK, hAK, hFK, ⟨e⟩⟩ := exists_small_coefficient l E
  let := hK
  let := hAK
  let := hFK
  let := spectralNorm.normedField ℚ_[l] K
  let := spectralNorm.normedAlgebra ℚ_[l] K
  let FE := CondensedRing.continuousFieldModuleEquivalence l K T
  let FI := CondensedRing.continuousIntegerModuleEquivalence l K T
  let er := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e T)
  let ea := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e T)
  let GE := CondensedRing.ringModuleEquivalenceOfIso T er
  let GI := CondensedRing.ringModuleEquivalenceOfIso T ea
  let L' := GE.inverse.obj L
  have : L'.IsFiniteLocallyFree := by
    dsimp only [L', GE, CondensedRing.ringModuleEquivalenceOfIso]
    exact finiteLocallyFree_restrict (Scheme.ProEt.topology T) _ _ er.symm L
  let P := FE.inverse.obj L'
  have hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj K) T) P :=
    field_inverse_locallyFree l K T L'
  obtain ⟨N, hN, ⟨eN⟩⟩ := internal_lisse_model l K T P hP
  let M := FI.functor.obj N
  have hM : IsContinuousConstructible T (latticeCoefficientIntegers l E)
      (GI.functor.obj M) :=
    integralContinuousEncoding_constructible l E K T (nativeIntegerIso l E K e T) N hN
  obtain ⟨eS⟩ := CondensedRing.continuousModuleEncoding_scalar_extension l K T M
  let eS' := FE.functor.mapIso
    ((Mod.extendScalars (coefficientMap (CondensedRing.integralScalarMap l K) T)).mapIso
      (FI.unitIso.app N)) ≪≫ eS
  obtain ⟨es⟩ := native_scalar_iso l E K e T M
  refine ⟨GI.functor.obj M, hM, ⟨?_⟩⟩
  exact es ≪≫ GE.functor.mapIso
    (eS'.symm ≪≫ FE.functor.mapIso eN ≪≫ FE.counitIso.app L') ≪≫ GE.counitIso.app L

end AlgebraicGeometry.ProEtale
