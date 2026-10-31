/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.AlgebraicGeometry.OpenExtensionConstantModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-! # Open extension by zero with condensed coefficients

Source: current blueprint, sec-six-functors/sk-lem-sf-open-ctf/_section.md and
sk-lem-sf-open-ctf.proof.md (blueprint: sk-lem-sf-open-ctf).

The coefficient alternatives are isomorphisms of ring objects, including the
finite quotient with its discrete topology and the finite-subextension-valued
algebraic closure. The exact open extension is derived termwise, as prescribed
by def-sfb-right-derived-exact. Constructibility uses finite constant scalar models.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar CondensedRing.openImmersionLowerShriek
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction CondensedRing.upperStarComp

/-- Restrict open extension to a map through the open, preserving its finite model.
Source: blueprint sk-lem-sf-open-ctf, Constructibility paragraph. -/
private theorem constantModel_openExtension_restrict
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y W : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (f : W ⟶ U)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ f).obj M)) :
    HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ (f ≫ j)).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) := by
  have := CondensedRing.open_unit_isIso Λ j
  apply constant_model_of_iso Λ _ hM
  exact (CondensedRing.upperStarComp Λ f j).app _ ≪≫
    (CondensedRing.upperStar Λ f).mapIso
      (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        Λ j).unit.app M)).symm

/-- The complementary restriction has the zero finite model.
Source: blueprint sk-lem-sf-open-ctf, Constructibility paragraph. -/
private theorem constantModel_openExtension_complement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    HasFiniteConstantLocalModel Λ _ ((CondensedRing.upperStar Λ j.closedComplement).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) := by
  exact constant_model_of_isZero Λ _
    (module_pullback_lowerShriek_isZero Λ j j.closedComplement
      (by rw [j.range_closedComplement]; exact Set.inter_compl_self _) M)

/-- Adjoin the closed complement while preserving any property of the stratum maps.
Source: blueprint sk-lem-sf-open-ctf, explicit extended stratification. -/
private theorem existsOpenExtensionStratification
    {U Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (j : U ⟶ Y) [IsOpenImmersion j]
    (S : Scheme.FiniteLocallyClosedStratification U)
    (Q : (W : Scheme.{u}) → (W ⟶ Y) → Prop)
    (last : Q _ j.closedComplement)
    (old : ∀ c : Fin S.n, Q (S.domain c) (S.immersion c ≫ j)) :
    ∃ R : Scheme.Stratification Y, ∀ c : Fin R.n, Q (R.domain c) (R.immersion c) := by
  let T := extendedStratification j S
  have hT (c : Fin T.n) : Topology.IsConstructible (T.stratum c) :=
    (T.isLocallyClosed_stratum c).isConstructible_of_noetherianSpace
  exact stratified_of_property Q T hT
    (extendedStratification_property j S Q last old)

/-- Forget the constructibility proofs while retaining every stratum scheme and map.
Source: blueprint sk-lem-sf-open-ctf, finite-stratification witness. -/
private theorem locallyClosedStratification_of_property
    {U : Scheme.{u}} (Q : (W : Scheme.{u}) → (W ⟶ U) → Prop)
    (h : ∃ S : Scheme.Stratification U, ∀ c : Fin S.n, Q (S.domain c) (S.immersion c)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification U,
      ∀ c : Fin S.n, Q (S.domain c) (S.immersion c) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨{
    n := S.n
    stratum := S.stratum
    isLocallyClosed_stratum := S.isLocallyClosed_stratum
    iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
    pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
    domain := S.domain
    immersion := S.immersion
    isImmersion := S.isImmersion
    range_immersion := S.range_immersion }, hS⟩

/-- On a qcqs scheme, the defining constructibility condition is its finite witness.
Source: blueprint sk-def-sfb-constructible, qcqs clause. -/
private theorem finiteStratified_of_constantConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsConstantModelConstructible Λ U M) : IsFiniteConstantStratified Λ U M := by
  classical
  exact (show IsConstantModelConstructible Λ U M = IsFiniteConstantStratified Λ U M from
    if_pos ⟨inferInstance, inferInstance⟩).mp hM

/-- Combine the old finite models and the complementary zero model on the explicit
extended stratification. Source: blueprint sk-lem-sf-open-ctf, Constructibility paragraph. -/
private theorem finiteStratified_openExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y] (j : U ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsFiniteConstantStratified Λ U M) :
    IsFiniteConstantStratified Λ Y ((CondensedRing.openImmersionLowerShriek Λ j).obj M) := by
  obtain ⟨S, hS⟩ := locallyClosedStratification_of_property
    (fun W f ↦ HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ f).obj M)) hM
  exact existsOpenExtensionStratification j S
    (fun W f ↦ HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ f).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)))
    (constantModel_openExtension_complement Λ j M)
    (fun c ↦ constantModel_openExtension_restrict Λ j (S.immersion c) M (hS c))

/-- The general constructibility step uses the original finite scalar models and the
zero model on the complementary stratum.
Source: blueprint sk-lem-sf-open-ctf, proof paragraph Constructibility
(blueprint: sk-lem-sf-open-ctf). -/
private theorem constantModelConstructible_openExtension_of_noetherian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y : Scheme.{u}} [IsNoetherian Y]
    (j : U ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsConstantModelConstructible Λ U M) :
    IsConstantModelConstructible Λ Y ((CondensedRing.openImmersionLowerShriek Λ j).obj M) := by
  classical
  let J := CondensedRing.openImmersionLowerShriek Λ j
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  exact constant_constructible_of_models Λ (J.obj M)
    (finiteStratified_openExtension Λ j M (finiteStratified_of_constantConstructible Λ M hM))

/-- Open extension by zero preserves bounded constructibility and the given
cohomological and Tor amplitude interval for each of the four condensed coefficients.
Consequently it carries `ConstantModelConstructibleFiniteTor` into the corresponding
category on the target: choose a common enlargement of the two finite intervals.

Source: current blueprint, sec-six-functors/sk-lem-sf-open-ctf/_section.md and
sk-lem-sf-open-ctf.proof.md (blueprint: sk-lem-sf-open-ctf).

Proof:
1. Finite-type schemes over the fixed algebraic closure of the finite field are
Noetherian (lem-weil-pbc-finite-type-over-noetherian). The recorded open extension
by zero `J = j_!` is exact (sk-def-sfb-module-lower-shriek); def-sfb-right-derived-exact
identifies its right derived functor with `J.mapDerivedCategory`. The exact-functor
cohomology comparison (lem-weil-pbc-exact-functor-complex-cohomology,
def-sfb-exact-derived-cohomology-comparison) gives H^q(j_! K) = j_! H^q(K), so
boundedness and the cohomological interval [a,b] are preserved
(lem-weil-pbc-exact-functor-bounded-below).
2. The general explicit-stratification helpers in OpenExtensionConstantModelConstructible
append the reduced closed complement as a zero stratum on the Noetherian `Y`. Pullback
composition and the open adjunction unit retain each original finite constant local
model. Disjoint-support vanishing gives the zero model on the complement, using the
identity cover and the finitely presented zero module. Thus `J` preserves constant-model
constructibility for any commutative condensed ring. Isomorphism invariance
(det-def-sfb-constructible-tor-amplitude) transports this through step 1 to H^q(j_! K).
3. For a degree-zero module `N` on `Y`, exact pullback identifies Lj^*(N[0]) with
(j^*N)[0] (det-prop-sfb-module-pullback-exact-main, def-sfb-left-derived-exact).
The open projection formula (lem-sfb-condensed-support-projection-formula, in the
module-object form `openImmersionProjectionComparison'`) gives
j_!(K ⊗^L Lj^*(N[0])) ≅ (j_! K) ⊗^L N[0]. The Tor hypothesis applied to j^*N bounds
K ⊗^L (j^*N)[0] in [a,b], and exactness of `J` keeps that interval. No
constructibility condition is imposed on `N`; the two intervals are preserved
separately, and enlarging them to one interval gives Dctf preservation. -/
theorem constantModelBoundedConstructible_openExtension_torAmplitudeIn
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    (n : ℕ) (_hn : 1 ≤ n)
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (_hΛ :
      (∃ (_ : TopologicalSpace (Padic.coefficientExtensionRing l E n))
        (_ : IsTopologicalRing (Padic.coefficientExtensionRing l E n)),
        DiscreteTopology (Padic.coefficientExtensionRing l E n) ∧
          Nonempty (Λ.toMon ≅
            Mon.mk (Profinite.continuousMapRingObj (Padic.coefficientExtensionRing l E n)))) ∨
      Nonempty (Λ.toMon ≅ Mon.mk (Profinite.padicIntegersRingObj l E)) ∨
      Nonempty (Λ.toMon ≅ Mon.mk
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing l E))) ∨
      Nonempty (Λ.toMon ≅ Mon.mk (Profinite.padicAlgClRingObj l)))
    {U Y : Scheme.{u}}
    [U.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : U ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (.of D.k))]
    [HasCompactification j]
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)))
    (hK : constantModelBoundedConstructible Λ.X U K)
    (hcoh : DerivedCategory.homologyConcentratedIn a b K)
    (hTor : DerivedCategory.torAmplitudeIn _ a b K) :
    constantModelBoundedConstructible Λ.X Y
        ((CondensedRing.openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) ∧
      DerivedCategory.homologyConcentratedIn a b
        ((CondensedRing.openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b
        ((CondensedRing.openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of D.k))
  have : IsNoetherian Y := {}
  let J := CondensedRing.openImmersionLowerShriek Λ.X j
  let P := CondensedRing.upperStar Λ.X j
  have hJ : ∀ (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ.X U)), IsConstantModelConstructible Λ.X U M →
      IsConstantModelConstructible Λ.X Y (J.obj M) := by
    exact constantModelConstructible_openExtension_of_noetherian Λ.X j
  have hcoh' := J.homologyConcentratedIn_mapDerivedCategory_obj hcoh
  refine ⟨⟨J.bounded_mapDerivedCategory_obj hK.1, ?_⟩, hcoh', ?_⟩
  · intro q
    have := (constantModelConstructibleFiniteTor_wellDefined Λ.X Y).1
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ.X Y)
      ((J.mapDerivedCategoryHomologyFunctorIso q).app K)
      (hJ _ (hK.2 q))
  · intro N
    let e : P.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
        (DerivedCategory.singleFunctor _ 0).obj (P.obj N) :=
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
        Λ.X j).app _ ≪≫ (P.mapDerivedCategorySingleFunctor 0).app N
    have ht := J.homologyConcentratedIn_mapDerivedCategory_obj (hTor (P.obj N))
    let t := asIso ((CondensedRing.openImmersionProjectionComparison' Λ.X j).app K |>.app
      ((DerivedCategory.singleFunctor _ 0).obj N))
    exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (J.mapDerivedCategory.mapIso
        (CategoryTheory.MonoidalCategory.tensorIso (Iso.refl K) e.symm) ≪≫ t) ht

end AlgebraicGeometry.ProEtale
