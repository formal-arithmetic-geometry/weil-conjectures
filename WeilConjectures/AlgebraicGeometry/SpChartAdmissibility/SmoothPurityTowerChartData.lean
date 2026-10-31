/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Strict Tate tower data and chart-domain predicates

The definitions are the existing chart-admissibility data, with their original names
and defining terms. They are separated from the admissibility theorem so that its
finite-level and operation lemmas can use them without an import cycle.
Source: blueprint latest, Local pairs and Uniformity
(blueprint: def-sp-chart-tate-tower-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified strict finite Tate towers, including their ordinary quotient transitions.
The comparison fields identify the actual sheaves and maps, before localization; they
are not choices of unrelated derived levels. Source: Local pairs, coefficient twists
(blueprint: lem-sp-tower-chart-admissibility). -/
structure Twists (T : Scheme.{u}) where
  comparison : ∀ n : ℕ, SpEllTwistComparisons l E T n
  normalized : ∀ n : ℕ, SpEllTwistComparisonsNormalized l E T n (comparison n)
  tower : ℕ → SpTowerShriek.S l E T
  level : ∀ n r : ℕ, (SpTowerShriek.ev l E T n).obj (tower r) ≅
    spEllTwistLine l E T n (r : ℤ)
  transition : ∀ n r : ℕ,
    HEq
      (((SemilinearSections.transition (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (Nat.le_succ n)).app (tower r)) ≫
        (SemilinearSections.res
          (SemilinearSections.coefficientMap (ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (Nat.le_succ n))).map
              (level n r).hom)
      ((level (n + 1) r).hom ≫ spEllTwistTransition l E T n (comparison n) (r : ℤ))

/-- Tensor in the ordinary tower derived category with the specified degree-zero line.
Source: Local pairs, H_U before the shift
(blueprint: lem-sp-tower-chart-admissibility). -/
def twist (base : SpTowerShriek.Base l E) {T : Scheme.{u}} (w : Twists l E T)
    (K : SpTowerShriek.D l E T) (r : ℕ) : SpTowerShriek.D l E T :=
  (SpTowerShriek.tensor l E base T).obj
    (K, (DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).obj (w.tower r))

/-- The separate, specified cohomological and Tor bounds on every actual tower level.
Constructibility is the recorded intrinsic predicate, with no normalization condition.
Source: Uniformity (blueprint: lem-sp-tower-chart-admissibility). -/
def bounds (T : Scheme.{u}) (K : SpTowerShriek.D l E T) (a b s t : ℤ) : Prop :=
  ∀ n : ℕ,
    spFiniteConstructibleTor T (SpTowerShriek.R l E n) ((SpTowerShriek.Ev l E T n).obj K) ∧
    proEtaleCohomologicalSupport ((SpTowerShriek.Ev l E T n).obj K) ⊆ Set.Icc a b ∧
    HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
      ((SpTowerShriek.Ev l E T n).obj K) s t

/-- Membership in the recorded unnormalized full subcategory, together with the precise
bounded-below and separate level-origin domains used by compact support. The sectionwise
normalized equivalence is the recorded spTowerShriekRealization.
Source: Local pairs domain checks (blueprint: lem-sp-tower-chart-admissibility). -/
def domain (base : SpTowerShriek.Base l E) (T : Scheme.{u})
    (K : SpTowerShriek.D l E T) : Prop :=
  (∀ D : SpCoefficientTowersAbelian l E T,
    spConstructibleTorTowers l E T D
      ((spTowerShriekRealization l E base T D).inverse.obj K)) ∧
  (∃ a : ℤ, K.IsGE a) ∧
  ∀ n : ℕ, Nonempty (SpTowerShriek.Origin l E base T n K)

/-- A finite-level origin retaining both specified intervals. The witness is an ordinary
etale complex and the isomorphism uses the specified comparison inverse image.
Source: clause (1), Local pairs (blueprint: lem-sp-tower-chart-admissibility). -/
def origins (T : Scheme.{u}) : Prop :=
  ∀ (n : ℕ) (M : proEtaleDerivedCategory T (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor T (SpTowerShriek.R l E n) M →
    ∀ a b s t : ℤ, a ≤ b → s ≤ t →
    proEtaleCohomologicalSupport M ⊆ Set.Icc a b →
    HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) M s t →
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} (SpTowerShriek.R l E n)) T,
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} (SpTowerShriek.R l E n)) T L ∧
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (SpTowerShriek.R l E n)) T s t L ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))) i).obj L)) ∧
      Nonempty ((finiteCoefficientIntrinsicDerivedComparison T (SpTowerShriek.R l E n)).obj
        L ≅ M)

/-- The compact-support assertion with its precise common output interval. The two input
intervals are independent. The compactification is fixed before choosing a coefficient.
Source: clause (3), Uniformity (blueprint: lem-sp-tower-chart-admissibility). -/
def compact (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    {Z T : Scheme.{u}} {h : Z ⟶ T} (c : Compactification h) (d : ℕ) : Prop :=
  ∀ (C : SpTowerShriek.D l E Z) (a b s t : ℤ), a ≤ b → s ≤ t →
    bounds l E Z C a b s t →
    bounds l E T ((SpTowerShriek.F l E base ops c).obj C) s (t + 2 * (d : ℤ))
      s (t + 2 * (d : ℤ)) ∧
    domain l E base T ((SpTowerShriek.F l E base ops c).obj C)

/-- The actual chart object, in the ordinary derived category of strict towers.
Source: Local pairs, H_U K = e^* p_d^* K(d)[2d]
(blueprint: lem-sp-tower-chart-admissibility). -/
def chart (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    {U V Y : Scheme.{u}} (e : U ⟶ V) (p : V ⟶ Y) (w : Twists l E U)
    (K : SpTowerShriek.D l E Y) (d : ℕ) : SpTowerShriek.D l E U :=
  (twist l E base w
    ((SpTowerShriek.pull l E base (ops.geometry e)).obj
      ((SpTowerShriek.pull l E base (ops.geometry p)).obj K)) d)⟦2 * (d : ℤ)⟧

/-- Standard affine r-space, with the coordinate index in the scheme universe.
Source: Local pairs, ordered coordinate projections
(blueprint: lem-sp-tower-chart-admissibility). -/
abbrev space (Y : Scheme.{u}) (r : ℕ) : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin r)) Y

/-- The coordinate projection forgetting the first coordinate, in the fixed order.
Source: Local pairs, ordered affine-line projections
(blueprint: lem-sp-tower-chart-admissibility). -/
def projection (Y : Scheme.{u}) (r : ℕ) : space Y (r + 1) ⟶ space Y r :=
  AffineSpace.reindex
    (fun i : ULift.{u} (Fin r) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (r + 1)))) Y

/-- The actual ordered iteration: each successor pulls back along the next affine-line
projection, tensors by its finite Tate tower, and shifts by two. The zero-dimensional
projection identifies the initial standard affine zero-space with Y.
Source: Local pairs, iterating the affine-line operation
(blueprint: lem-sp-tower-chart-admissibility). -/
def stage (base : SpTowerShriek.Base l E)
    (ops : SpTowerShriek.Operations l E base) {k : Type u} [Field k]
    (Y : Over (Spec (.of k)))
    (w : ∀ T : Over (Spec (.of k)), Twists l E T.left)
    (K : SpTowerShriek.D l E Y.left) : (r : ℕ) → SpTowerShriek.D l E (space Y.left r)
  | 0 => (SpTowerShriek.pull l E base (ops.geometry (space Y.left 0 ↘ Y.left))).obj K
  | r + 1 =>
    (twist l E base (w (Over.mk ((space Y.left (r + 1) ↘ Y.left) ≫ Y.hom)))
      ((SpTowerShriek.pull l E base (ops.geometry (projection Y.left r))).obj
        (stage base ops Y w K r)) 1)⟦(2 : ℤ)⟧

/-- The intermediate inverse image before the next twist and shift.
Source: Local pairs, ordered affine projections
(blueprint: lem-sp-tower-chart-admissibility). -/
def stagePull (base : SpTowerShriek.Base l E)
    (ops : SpTowerShriek.Operations l E base) {k : Type u} [Field k]
    (Y : Over (Spec (.of k)))
    (w : ∀ T : Over (Spec (.of k)), Twists l E T.left)
    (K : SpTowerShriek.D l E Y.left) (r : ℕ) : SpTowerShriek.D l E (space Y.left (r + 1)) :=
  (SpTowerShriek.pull l E base (ops.geometry (projection Y.left r))).obj
    (stage l E base ops Y w K r)

/-- The intermediate twist before the next shift.
Source: Local pairs, ordered affine projections
(blueprint: lem-sp-tower-chart-admissibility). -/
def stageTwist (base : SpTowerShriek.Base l E)
    (ops : SpTowerShriek.Operations l E base) {k : Type u} [Field k]
    (Y : Over (Spec (.of k)))
    (w : ∀ T : Over (Spec (.of k)), Twists l E T.left)
    (K : SpTowerShriek.D l E Y.left) (r : ℕ) : SpTowerShriek.D l E (space Y.left (r + 1)) :=
  twist l E base (w (Over.mk ((space Y.left (r + 1) ↘ Y.left) ≫ Y.hom)))
    (stagePull l E base ops Y w K r) 1

/-- The domains and intervals at every partial affine stage, before its twist,
after its twist, and after its shift. The source fixes the order of coordinates;
these are the canonical cumulative pullbacks along that order.
Source: clause (2), Local pairs and Uniformity
(blueprint: lem-sp-tower-chart-admissibility). -/
def intermediate (base : SpTowerShriek.Base l E)
    (ops : SpTowerShriek.Operations l E base) {k : Type u} [Field k]
    (Y : Over (Spec (.of k)))
    (w : ∀ T : Over (Spec (.of k)), Twists l E T.left)
    (K : SpTowerShriek.D l E Y.left) (d : ℕ) (a b s t : ℤ) : Prop :=
  ∀ r : ℕ, r ≤ d →
    bounds l E (space Y.left r)
      ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K)
      a b s t ∧
    domain l E base (space Y.left r)
      ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K) ∧
    bounds l E (space Y.left r)
      (twist l E base (w (Over.mk ((space Y.left r ↘ Y.left) ≫ Y.hom)))
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K) r)
      a b s t ∧
    domain l E base (space Y.left r)
      (twist l E base (w (Over.mk ((space Y.left r ↘ Y.left) ≫ Y.hom)))
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K) r) ∧
    bounds l E (space Y.left r)
      ((twist l E base (w (Over.mk ((space Y.left r ↘ Y.left) ≫ Y.hom)))
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K) r)
          ⟦2 * (r : ℤ)⟧)
      (a - 2 * (r : ℤ)) (b - 2 * (r : ℤ))
      (s - 2 * (r : ℤ)) (t - 2 * (r : ℤ)) ∧
    domain l E base (space Y.left r)
      ((twist l E base (w (Over.mk ((space Y.left r ↘ Y.left) ≫ Y.hom)))
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left r ↘ Y.left))).obj K) r)
          ⟦2 * (r : ℤ)⟧) ∧
    bounds l E (space Y.left r) (stage l E base ops Y w K r)
      (a - 2 * (r : ℤ)) (b - 2 * (r : ℤ))
      (s - 2 * (r : ℤ)) (t - 2 * (r : ℤ)) ∧
    domain l E base (space Y.left r) (stage l E base ops Y w K r) ∧
    (∀ V : (space Y.left r).Opens,
      ∀ c : Compactification V.ι, compact l E base ops c 0) ∧
    (r < d →
      bounds l E (space Y.left (r + 1)) (stagePull l E base ops Y w K r)
        (a - 2 * (r : ℤ)) (b - 2 * (r : ℤ))
        (s - 2 * (r : ℤ)) (t - 2 * (r : ℤ)) ∧
      domain l E base (space Y.left (r + 1)) (stagePull l E base ops Y w K r) ∧
      bounds l E (space Y.left (r + 1)) (stageTwist l E base ops Y w K r)
        (a - 2 * (r : ℤ)) (b - 2 * (r : ℤ))
        (s - 2 * (r : ℤ)) (t - 2 * (r : ℤ)) ∧
      domain l E base (space Y.left (r + 1)) (stageTwist l E base ops Y w K r) ∧
      ∀ c : Compactification (projection Y.left r), compact l E base ops c 1)

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
