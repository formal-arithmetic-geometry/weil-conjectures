/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedTowerRoos
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralTowerReductionRepresentatives
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedEquivalenceStatement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantLocalTor
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralQcqsReductionConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.CohomologyTorInterval
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.StratifiedTorIntervalDevissage
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteInputScalarCoordinates
import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare.BoundedFlatCoefficientSiteSquareCurrent
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSiteSquare
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.CategoryTheory.Derived.DerivedEquivalenceCancellation
/-! # Reduction, completion unit, and the normalized equivalence
Source: sk-lem-sp-tower, both paragraphs (blueprint: sk-lem-sp-tower).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Reduction restricted to the full constructible subcategory, once closure is proved.
Source: sk-lem-sp-tower, equivalence clause (blueprint: sk-lem-sp-tower). -/
def boundedReduction (D : Model l E T)
    (h : ∀ K : Dbc l E T, Normalized l E T D (D.red.obj K.obj)) :
    Dbc l E T ⥤ NormalizedTowers l E T D :=
  ObjectProperty.lift _ ((constantModelBoundedConstructible
    (DerivedNakayama.integerRing l E) T).ι ⋙ D.red) h

/-- Total inverse limit restricted to normalized constructible towers, once closure is proved.
Source: sk-lem-sp-tower, equivalence clause (blueprint: sk-lem-sp-tower). -/
def boundedLimit (D : Model l E T)
    (h : ∀ C : NormalizedTowers l E T D,
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T
        (D.rlim.obj C.obj)) : NormalizedTowers l E T D ⥤ Dbc l E T :=
  ObjectProperty.lift _ ((Normalized l E T D).ι ⋙ D.rlim) h

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- The same reduction/limit adjunction restricts to the equivalence; both maps are
literally the ambient unit and counit. Source: sk-lem-sp-tower, second paragraph
(blueprint: sk-lem-sp-tower). -/
structure BoundedEquivalence (D : Model l E T) (adj : D.red ⊣ D.rlim) where
  redClosed : ∀ K : Dbc l E T, Normalized l E T D (D.red.obj K.obj)
  limitClosed : ∀ C : NormalizedTowers l E T D,
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T (D.rlim.obj C.obj)
  adjunction : boundedReduction l E T D redClosed ⊣ boundedLimit l E T D limitClosed
  unit : ∀ K : Dbc l E T, (adjunction.unit.app K).hom = adj.unit.app K.obj
  counit : ∀ C : NormalizedTowers l E T D,
    (adjunction.counit.app C).hom = adj.counit.app C.obj
  unitIso : IsIso adjunction.unit
  counitIso : IsIso adjunction.counit

/-- The unit is the actual derived-completion map, in the Roos coordinates of every
K-flat representative. Using the cofinal ell-power tower gives the same canonical map.
Source: sk-lem-sp-tower, first paragraph (blueprint: sk-lem-sp-tower). -/
def CompletionUnit (D : Model l E T) (adj : D.red ⊣ D.rlim) : Prop :=
  ∀ (K : Integral l E T) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K),
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      ∃ c : D.rlim.obj (D.red.obj K) ≅
      DerivedCategory.Q.obj (AdicCompletion.roos l E T P),
      adj.unit.app K ≫ c.hom = AdicCompletion.completionMap l E T K P e

private theorem reduction_isIso_of_iso
    (D : Model l E T) (m n : ℕ) (h : m ≤ n) {K L : DerivedTowers l E T}
    (e : K ≅ L) [IsIso ((D.reduction h).app K)] :
    IsIso ((D.reduction h).app L) := by
  exact IsIso.of_isIso_fac_left ((D.reduction h).naturality e.hom)

private theorem reduction_normalized (D : Model l E T) (K : Integral l E T)
    (m n : ℕ) (h : m ≤ n) :
    IsIso ((D.reduction h).app (D.red.obj K)) := by
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  let := hf
  let C := (D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨hc, hs, hr⟩ := reduction_representatives l E T D
  have hi : IsIso
      ((NatTrans.mapHomologicalComplex (ordinaryTransitionAdjunct l E T D h)
        (.up ℤ)).app C) := by
    let t := (NatTrans.mapHomologicalComplex (ordinaryTransitionAdjunct l E T D h)
      (.up ℤ)).app C
    have : ∀ i : ℤ, IsIso (t.f i) := fun i ↦
      ordinaryTransitionAdjunct_isIso l E T D (P.X i) m n h
    exact HomologicalComplex.Hom.isIso_of_components t
  have := hs P hP m n h
  have : IsIso ((D.reduction h).app (DerivedCategory.Q.obj C)) := by
    rw [hr C m n h]
    infer_instance
  have := hc P hP
  let e : D.red.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C :=
    asIso (D.redCounit.app P)
  have := reduction_isIso_of_iso l E T D m n h e.symm
  exact reduction_isIso_of_iso l E T D m n h
    (D.red.mapIso (asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K))

private theorem bounded_equivalence_of_normalized [IsNoetherian T]
    (D : Model l E T) (N : NormalizedEquivalence l E T D)
    (hn : ∀ K : Integral l E T, ∀ (m n : ℕ) (h : m ≤ n),
      IsIso ((D.reduction h).app (D.red.obj K))) :
    Nonempty (BoundedEquivalence l E T D N.adjunction) := by
  let P := constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T
  let Q := Normalized l E T D
  let hr : ∀ K : Dbc l E T, Q (D.red.obj K.obj) :=
    fun K ↦ ⟨finite_reduction_constructible l E T D K, hn K.obj⟩
  let hl := normalized_limit_constructible l E T D N
  let a : boundedReduction l E T D hr ⊣ boundedLimit l E T D hl :=
    N.adjunction.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
      (Iso.refl _) (Iso.refl _)
  have hu (K : Dbc l E T) : (a.unit.app K).hom = N.adjunction.unit.app K.obj := by
    change P.ι.map (a.unit.app K) = _
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change N.adjunction.unit.app K.obj ≫ D.rlim.map (𝟙 _) ≫ 𝟙 _ = _
    rw [D.rlim.map_id]
    simp only [Category.comp_id]
    exact Category.comp_id (N.adjunction.unit.app K.obj)
  have hc (C : NormalizedTowers l E T D) :
      (a.counit.app C).hom = N.adjunction.counit.app C.obj := by
    change Q.ι.map (a.counit.app C) = _
    dsimp only [a]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change 𝟙 _ ≫ D.red.map (𝟙 _) ≫ N.adjunction.counit.app C.obj = _
    rw [D.red.map_id]
    simp only [Category.id_comp]
  have hui (K : Dbc l E T) : IsIso (a.unit.app K) := by
    have h := (N.unit_iff K.obj).mpr (N.constructibleComplete inferInstance K)
    have : IsIso (P.ι.map (a.unit.app K)) := by
      change IsIso (a.unit.app K).hom
      rw [hu]
      exact h
    exact isIso_of_reflects_iso (a.unit.app K) P.ι
  have hci (C : NormalizedTowers l E T D) : IsIso (a.counit.app C) := by
    have h := N.counit C.obj C.property.2
    have : IsIso (Q.ι.map (a.counit.app C)) := by
      change IsIso (a.counit.app C).hom
      rw [hc]
      exact h
    exact isIso_of_reflects_iso (a.counit.app C) Q.ι
  let : ∀ K, IsIso (a.unit.app K) := hui
  let : ∀ C, IsIso (a.counit.app C) := hci
  exact ⟨⟨hr, hl, a, hu, hc, NatIso.isIso_of_isIso_app _,
    NatIso.isIso_of_isIso_app _⟩⟩

/-- Canonical reduction is left adjoint to total derived inverse limit, with its unit
identified with derived completion, and over a Noetherian scheme this same adjunction
restricts to the normalized constructible equivalence.

Source: latest blueprint, sk-lem-sp-tower, both paragraphs (blueprint: sk-lem-sp-tower).
Proof: the change of rings h from towers to constant inverse systems and the topos
morphism p with p_* = inverse limit give Lh^* p^{-1} ⊣ Rp_* h_* (Stacks 06YV, 07A6).
In strict-system coordinates this is the specified ordinary tensor/limit adjunction,
derived using K-flat and K-injective representatives. Its unit is the augmented Roos
completion map; cofinal ell- and uniformizer-power ideals identify their completion maps.
By sk-prop-sp-integral-towers(1), red sends Dbc into normalized constructible towers.
The integral criterion gives derived completeness, so the restricted unit is invertible.
Conversely for a normalized tower C, reduction of Rlim C modulo ell^m differs from C_m
by Rlim of (C_m[1])_n with transition multiplication by ell. This limit vanishes since
ell^m kills C_m. Thus the limit is derived complete and its first reduction constructible.
Repleteness (sk-prop-pe-replete, Stacks 0940) supplies boundedness, and
sk-prop-sp-integral-towers(2) gives Dbc. The counit is at level m this same reduction
isomorphism; evaluations detect isomorphisms, so the whole counit is invertible.
The full inclusions retain these exact unit and counit maps. -/
theorem sp_tower_statement :
    ∃ D : Model l E T, ∃ adj : D.red ⊣ D.rlim,
      CompletionUnit l E T D adj ∧
      (IsNoetherian T → Nonempty (BoundedEquivalence l E T D adj))  := by
  obtain ⟨D, ⟨N⟩⟩ := normalized_equivalence_statement l E T
  refine ⟨D, N.adjunction, N.completionUnit, ?_⟩
  intro hT
  let := hT
  exact bounded_equivalence_of_normalized l E T D N (reduction_normalized l E T D)

/-- Canonical reduction/total-limit coordinates, determined up to the canonical derived
isomorphisms by the ordinary tensor/limit construction and universal derived functors.
Source: sk-lem-sp-tower (blueprint: sk-lem-sp-tower). -/
def model : Model l E T := (sp_tower_statement l E T).choose

/-- The adjunction supplied by sk-lem-sp-tower in the chosen canonical coordinates.
Source: sk-lem-sp-tower (blueprint: sk-lem-sp-tower). -/
def adjunction : (model l E T).red ⊣ (model l E T).rlim :=
  (sp_tower_statement l E T).choose_spec.choose

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
