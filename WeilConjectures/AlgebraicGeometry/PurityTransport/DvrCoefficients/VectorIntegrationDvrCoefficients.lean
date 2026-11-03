/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.IntegersModPow
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierScalarCoordinates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity

/-! # Valuation-ring quotient coefficients and their scalar comparisons

Source: thm-pur-vector-bundle-thom, Step 3, as refined by Wei Yang #1412 item 9:
the coefficient tower `A_n = R/ϖ^n` of `R = O_F`, its quotient maps, the
localization `R → F`, the closure map `F → Qbar_ℓ`, and the canonical
compact-support scalar, coefficient-unit and root-normalized Tate comparisons
(blueprint: def-pur-vector-integration-dvr-coefficients).

The positive level `n+1` is indexed by `n : ℕ`. Every ring is the existing
`PurityTransport.Coefficient` presentation (a finite discrete ring, `O_E`, `E` or the
algebraic closure). Every coefficient map is postcomposition with a continuous ring map.
Every comparison is assembled from the published scalar-six maps
(`scalarSupportMap`, `sourceScalar`, `scalarLineZero`, `scalarDirectMate`,
`scalarLineMap`); no comparison is chosen from an existence statement except the
normalized scalar line coordinates, which are unique.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport.DvrCoefficients

variable (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
  (ϖ : PadicAlgCl.integers ell E.1)

/-- `ℓ^(n+1)` lies in `(ϖ^(n+1))`, so `A_(n+1)` is a quotient of `O_E/ℓ^(n+1)`.
Source: blueprint Step 3, `A_n = R/ϖ^n`
(blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: `O_E` is a discrete valuation ring and `ϖ` is a uniformizer. Since
`|ℓ| < 1`, the element `ℓ` lies in the maximal ideal `(ϖ)`, so `ϖ ∣ ℓ` and
`ϖ^(n+1) ∣ ℓ^(n+1)`. -/
theorem ellPow_mem (hϖ : Irreducible ϖ) (n : ℕ) :
    (ell : PadicAlgCl.integers ell E.1) ^ (n + 1) ∈ Ideal.span {ϖ ^ (n + 1)} := by
  sorry

/-- The finite coefficient ring `A_(n+1) = O_E/ϖ^(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
abbrev level (n : ℕ) : CommRingCat.{0} :=
  CommRingCat.of (PadicAlgCl.integers ell E.1 ⧸ Ideal.span {ϖ ^ (n + 1)})

/-- The quotient of `O_E/ℓ^(n+1)` onto `A_(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
def levelFactor (hϖ : Irreducible ϖ) (n : ℕ) :
    PadicAlgCl.integersModPow ell E.1 (n + 1) →+* level ell E ϖ n :=
  Ideal.Quotient.factor (Ideal.span_le.2 (by
    rintro x rfl
    exact ellPow_mem ell E ϖ hϖ n))

/-- Each level is finite, being a quotient of the finite ring `O_E/ℓ^(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: `levelFactor` is surjective (`Ideal.Quotient.factor_surjective`) from the finite ring
`O_E/ℓ^(n+1)`; apply `Finite.of_surjective`. -/
theorem level_finite (hϖ : Irreducible ϖ) (n : ℕ) : Finite (level ell E ϖ n) := by
  sorry

/-- `ℓ^(n+1)` annihilates `A_(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: `ℓ^(n+1) ∈ (ϖ^(n+1))` by `ellPow_mem`; map to the quotient (`map_pow`, `map_natCast`). -/
theorem level_annihilated (hϖ : Irreducible ϖ) (n : ℕ) :
    (ell ^ (n + 1) : level ell E ϖ n) = 0 := by
  sorry

/-- The finite coefficient presentation of `A_(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
abbrev coefficient (hϖ : Irreducible ϖ) (n : ℕ) : Coefficient ell :=
  .finite (level ell E ϖ n) (level_finite ell E ϖ hϖ n) n (level_annihilated ell E ϖ hϖ n)


/-- The quotient map `R → A_(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
abbrev reductionRingHom (n : ℕ) : PadicAlgCl.integers ell E.1 →+* level ell E ϖ n :=
  Ideal.Quotient.mk _

/-- The quotient map `R → A_(n+1)` is continuous for the valuation topology on `R`
and the discrete topology on `A_(n+1)`: it factors through `O_E/ℓ^(n+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: the map equals `levelFactor ∘ integersModPowMk` (by `rfl` pointwise); the latter is
continuous (`continuous_integersModPowMk`) and any map out of a discrete space is continuous. -/
theorem continuous_reductionRingHom (hϖ : Irreducible ϖ) (n : ℕ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
    letI : TopologicalSpace (level ell E ϖ n) := ⊥
    Continuous (reductionRingHom ell E ϖ n) := by
  sorry

/-- The quotient map `A_(n+1) → A_(m+1)` for `m ≤ n`.
Source: blueprint Step 3, quotient maps `A_n → A_m`
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def transitionRingHom {m n : ℕ} (h : m ≤ n) : level ell E ϖ n →+* level ell E ϖ m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2
    (pow_dvd_pow ϖ (Nat.succ_le_succ h)))

/-- The condensed coefficient reduction `R_B → A_(n+1),B`, postcomposition with the
continuous quotient map. Source: blueprint Step 3
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def reduction (hϖ : Irreducible ϖ) (n : ℕ) :
    (Coefficient.integral E).bundled.{u} ell ⟶ (coefficient ell E ϖ hϖ n).bundled ell :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  letI : TopologicalSpace (level ell E ϖ n) := ⊥
  haveI : DiscreteTopology (level ell E ϖ n) := discreteTopology_bot _
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap (reductionRingHom ell E ϖ n)
      (continuous_reductionRingHom ell E ϖ hϖ n))⟩⟩

/-- The condensed coefficient transition `A_(n+1) → A_(m+1)`, `m ≤ n`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
def transition (hϖ : Irreducible ϖ) {m n : ℕ} (h : m ≤ n) :
    (coefficient ell E ϖ hϖ n).bundled.{u} ell ⟶ (coefficient ell E ϖ hϖ m).bundled ell :=
  letI : TopologicalSpace (level ell E ϖ n) := ⊥
  haveI : DiscreteTopology (level ell E ϖ n) := discreteTopology_bot _
  letI : TopologicalSpace (level ell E ϖ m) := ⊥
  haveI : DiscreteTopology (level ell E ϖ m) := discreteTopology_bot _
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap (transitionRingHom ell E ϖ h)
      continuous_of_discreteTopology)⟩⟩

/-- The localization `O_E → E` of condensed coefficients.
Source: blueprint Step 3, scalar extension along `R → F`
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def localization :
    (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.rational E).bundled ell :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)⟩⟩

/-- The inclusion `E → Qbar_ℓ` of condensed coefficients (finite-subextension valued).
Source: blueprint Step 3, scalar extension along `F → Qbar_ℓ`
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def closure :
    (Coefficient.rational E).bundled.{u} ell ⟶ (Coefficient.closure).bundled ell :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicSubfieldCondensedRingToPadicAlgCl ell E)⟩⟩

/-- The integral extension `O_E → O_E'` for `E ≤ E'`.
Source: blueprint Step 3, finite extension of `F`
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def integralExtension {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
    (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.integral E').bundled ell :=
  latticeIntegralMap ell h

/-- The rational extension `E → E'` for `E ≤ E'`.
Source: blueprint Step 3, finite extension of `F`
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def rationalExtension {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
    (Coefficient.rational E).bundled.{u} ell ⟶ (Coefficient.rational E').bundled ell :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.padicSubfieldCondensedRingMap ell h)⟩⟩

/-- Each listed map is compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: all maps are postcomposition with continuous ring homomorphisms. Two continuous
ring homomorphisms out of `ℤ_ℓ` agree on the dense subring `ℤ`, hence agree; so the
two composites agree on every section `C(S, ℤ_ℓ)`. -/
theorem reduction_integral (hϖ : Irreducible ϖ) (n : ℕ) :
    (Coefficient.integral E).integralMap.{u} ell ≫ (reduction ell E ϖ hϖ n).hom.hom =
      (coefficient ell E ϖ hϖ n).integralMap ell := by
  sorry

/-- Transition maps are compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: as for `reduction_integral`, by density of `ℤ` in `ℤ_ℓ`. -/
theorem transition_integral (hϖ : Irreducible ϖ) {m n : ℕ} (h : m ≤ n) :
    (coefficient ell E ϖ hϖ n).integralMap.{u} ell ≫ (transition ell E ϖ hϖ h).hom.hom =
      (coefficient ell E ϖ hϖ m).integralMap ell := by
  sorry

/-- Localization is compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: both composites are postcomposition with the inclusion `ℤ_ℓ ⊆ E`. -/
theorem localization_integral :
    (Coefficient.integral E).integralMap.{u} ell ≫ (localization ell E).hom.hom =
      (Coefficient.rational E).integralMap ell := by
  sorry

/-- The closure map is compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: both composites are postcomposition with `ℤ_ℓ ⊆ ℚ_ℓ ⊆ E ⊆ Qbar_ℓ`. -/
theorem closure_integral :
    (Coefficient.rational E).integralMap.{u} ell ≫ (closure ell E).hom.hom =
      (Coefficient.closure).integralMap ell := by
  sorry

/-- Integral extension is compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: both composites are postcomposition with `ℤ_ℓ ⊆ O_E'`. -/
theorem integralExtension_integral {E E' : PadicAlgCl.FiniteIntermediateField ell}
    (h : E ≤ E') :
    (Coefficient.integral E).integralMap.{u} ell ≫ (integralExtension ell h).hom.hom =
      (Coefficient.integral E').integralMap ell := by
  sorry

/-- Rational extension is compatible with the canonical maps from `ℤ_ℓ`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: both composites are postcomposition with `ℤ_ℓ ⊆ E'`. -/
theorem rationalExtension_integral {E E' : PadicAlgCl.FiniteIntermediateField ell}
    (h : E ≤ E') :
    (Coefficient.rational E).integralMap.{u} ell ≫ (rationalExtension ell h).hom.hom =
      (Coefficient.rational E').integralMap ell := by
  sorry

/-- The quotient maps compose: `R → A_(n+1) → A_(m+1)` is `R → A_(m+1)`.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: the underlying ring maps agree pointwise (a factor map after a quotient map is the
smaller quotient map), and postcomposition is functorial. -/
theorem reduction_transition (hϖ : Irreducible ϖ) {m n : ℕ} (h : m ≤ n) :
    reduction.{u} ell E ϖ hϖ n ≫ transition ell E ϖ hϖ h = reduction ell E ϖ hϖ m := by
  sorry

/-- The normalized scalar line coordinates of a coefficient map, unique by
`lineCoordinates_unique`. Source: def-pur-transport-scalar-line-coordinates
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def lineCoordinates {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    ScalarLineCoordinates ell a ha X :=
  (trace_scalar_coordinates_nonempty ell a ha X).some

/-- Normalized scalar line coordinates are unique.
Source: def-pur-transport-scalar-line-coordinates
(blueprint: def-pur-vector-integration-dvr-coefficients).
Proof: the first-line field is heterogeneously equal to `scalarFirst`, so the two first
fields agree. The normalized monoidal structure on extension of scalars exists and is
unique (internalScalarMonoidalNormalized_existsUnique); applying both power normalizations
to it identifies each power field with the same `powerPull`. Structure extensionality. -/
theorem lineCoordinates_unique {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u})
    (p q : ScalarLineCoordinates ell a ha X) : p = q := by
  sorry

/-- The coefficient-unit comparison `T(Λ_X) → Λ'_X`: the adjunct of the normalized
degree-zero line map. Source: lem-sfb-ringed-derived-monoidal-comparisons
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def unitComparison {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    (scalarSixChange a X).obj (unit ell c X) ⟶ unit ell c' X :=
  scalarLineZero ell a X 0 ((lineCoordinates ell a ha X).power 0)

section Vector

variable (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
  (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]

/-- The actual twisted compact-support source `M_Λ = Rπ_! Λ_V(d)[2d]` at the canonical
vector-bundle compactification. Source: blueprint Step 3
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
abbrev source (c : Coefficient ell) : c.derived ell S :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell)
    (Etale.vectorBundlePurityCompactification S d F)).obj
      ((c.smoothSource ell (VectorBundleZeroSection.π S d F) d).obj (unit ell c S))

/-- The compact-support scalar comparison of the source: the compact-support scalar map,
then the normalized scalar/pullback/Tate source comparison and the unit comparison.
Source: det-prop-scalar-six-compact-support, lem-pur-proetale-kummer-limit-boundary
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def sourceComparison {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) :
    (scalarSixChange a S).obj (source ell S d F c) ⟶ source ell S d F c' :=
  (scalarSupportMap a (Etale.vectorBundlePurityCompactification S d F)).app _ ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c'.obj ell)
      (Etale.vectorBundlePurityCompactification S d F)).map
      (sourceScalar ell a (VectorBundleZeroSection.π S d F) d ha
          (lineCoordinates ell a ha (VectorBundleZeroSection.scheme S d F)) (unit ell c S) ≫
        (c'.smoothSource ell (VectorBundleZeroSection.π S d F) d).map
          (unitComparison ell a ha S))

end Vector

section Proper

/-- The proper twisted source `Q_Λ = Rq_* Λ_P(1)[2]`.
Source: blueprint Step 3, projective-line normalization
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
abbrev properSource (c : Coefficient ell) {P U : Scheme.{u}} (q : P ⟶ U) :
    c.derived ell U :=
  (CondensedRing.lowerStar (c.obj ell) q).rightDerivedFunctor.obj (c.derivedLine ell P 1)

/-- The proper scalar comparison of `Q_Λ`: the direct-image scalar mate, then the
normalized scalar Tate-line map. Source: det-prop-scalar-six-direct-image,
lem-pur-proetale-kummer-limit-boundary
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
def properSourceComparison {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) {P U : Scheme.{u}}
    (q : P ⟶ U) :
    (scalarSixChange a U).obj (properSource ell c q) ⟶ properSource ell c' q :=
  (scalarDirectMate a q).app _ ≫
    (CondensedRing.lowerStar (c'.obj ell) q).rightDerivedFunctor.map
      (scalarLineMap ell a P 1 ((lineCoordinates ell a ha P).power 1))

end Proper

/-- A coefficient `c` with a tower of finite reductions: level rings, the reduction maps
from `c` and the consecutive transitions, with the composition identity. The positive level
`n+1` is indexed by `n`. Source: blueprint Step 3, the quotient tower
(blueprint: def-pur-vector-integration-dvr-coefficients). -/
structure ReductionSystem (c : Coefficient ell) where
  /-- The finite coefficient at positive level `n+1`. -/
  level : ℕ → Coefficient ell
  /-- The reduction from `c`. -/
  reduction : ∀ n, c.bundled.{u} ell ⟶ (level n).bundled ell
  /-- The consecutive quotient map. -/
  transition : ∀ n, (level (n + 1)).bundled.{u} ell ⟶ (level n).bundled ell
  /-- Reduction followed by the transition is the smaller reduction. -/
  comp : ∀ n, reduction (n + 1) ≫ transition n = reduction n

/-- The valuation-ring tower `R → A_(n+1)` with its quotient transitions.
Source: blueprint Step 3 (blueprint: def-pur-vector-integration-dvr-coefficients). -/
def dvrSystem (hϖ : Irreducible ϖ) : ReductionSystem.{u} ell (Coefficient.integral E) where
  level n := coefficient ell E ϖ hϖ n
  reduction n := reduction ell E ϖ hϖ n
  transition n := transition ell E ϖ hϖ (Nat.le_succ n)
  comp n := reduction_transition ell E ϖ hϖ (Nat.le_succ n)

end AlgebraicGeometry.ProEtale.PurityTransport.DvrCoefficients
