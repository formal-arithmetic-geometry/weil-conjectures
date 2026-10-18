/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.Paper.FiniteLevelAmplification

/-!
# Preservation of uniformly bounded constructible adic towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1353
(blueprint: def-weil-pbc-tower-preservation).

The four ambient functors act on strict completed-coefficient towers before inverse
limit. Output quotient structures and common local models are required as data.
Amplitude compatibility is tested on the actual finite-coefficient operations; it
requires common output models in each interval supplied by AMP from a common input
interval, and tests the corresponding finite-level images. It asserts no evaluation
formula for arbitrary pullback towers. The finite-level AMP condition supplies the
indicated intervals [a,b+c] for
direct image and [a,b] for pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The finite derived pullback, using the canonical constant-coefficient comparison.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
abbrev towerFinitePullback {S T : Scheme.{u}} (h : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n))) ⥤
      DerivedCategory (pbcModules S ((pbcAdicRings S d).obj (op n))) :=
  proEtaleRingDerivedPullback h ((pbcAdicRings T d).obj (op n))
    ((pbcAdicRings S d).obj (op n))
    (asIso (completedFiniteCoefficientMap h d n))

/-- The finite derived direct image, with the same canonical coefficient comparison.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
abbrev towerFiniteDirectImage {S T : Scheme.{u}} (h : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    DerivedCategory (pbcModules S ((pbcAdicRings S d).obj (op n))) ⥤
      DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n))) :=
  completedFiniteDerivedDirectImage h d n

/-- A common window of quotient-coefficient cohomology, in the finite-level AMP sense.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
def HasAdicLevelAmplitude {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n))))
    (a b : ℤ) : Prop :=
  ∀ q : ℤ, (q < a ∨ b < q) → IsZero ((DerivedCategory.homologyFunctor _ q).obj K)

/-- The local models from bounded constructibility with a specified common window.
All the finite-lisse cohomology and compatibility fields are those of the existing
AdicTowerLocalModel; the complex is independent of n.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
def HasConstructibleAdicTowerModels {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (N : AdicTower T d) (a b : ℤ) : Prop :=
  ∃ S : LocallyClosedStratification T,
    ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
      V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
      ∀ (U : (S.domain α).ProEt) (h : U ⟶ ⊤_ (S.domain α).ProEt), V h →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) N a b)

/-- Amplitude compatibility uses the specified finite-level functors on the supplied
quotient-linear levels. Whenever AMP holds and the input levels have interval [a,b],
their finite images have the specified interval and the output admits common local
models in that interval. The width growth is c for direct image and zero for pullback.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
def HasTowerAmplitudeCompatibleModels {S T : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] {d : AdicCoefficientDatum A}
    (Amp : ℕ → Prop) (growth : ℕ → ℤ)
    (F : ∀ n : ℕ, DerivedCategory (pbcModules S ((pbcAdicRings S d).obj (op n))) ⥤
      DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n))))
    (M : AdicTower S d) (N : AdicTower T d) : Prop :=
  ∀ c : ℕ, Amp c → ∀ a b : ℤ, a ≤ b →
    (∀ n : ℕ, HasAdicLevelAmplitude d n (M.level n) a b) →
      (∀ n : ℕ, HasAdicLevelAmplitude d n ((F n).obj (M.level n)) a (b + growth c)) ∧
      HasConstructibleAdicTowerModels N a (b + growth c)

/-- Preservation means an output adic tower over the actual functor value, with its
full quotient-coefficient structures, evaluations, normalizations and cocycle, and
uniform local constructibility. The same output data admit the AMP-compatible models.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
def PreservesBoundedConstructibleAdicTowers {S T : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (Amp : ℕ → Prop) (growth : ℕ → ℤ)
    (F : DerivedCategory (pbcTowers S (pbcAdicCompletion S d)) ⥤
      DerivedCategory (pbcTowers T (pbcAdicCompletion T d)))
    (Ffin : ∀ n : ℕ, DerivedCategory (pbcModules S ((pbcAdicRings S d).obj (op n))) ⥤
      DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n)))) : Prop :=
  ∀ M : AdicTower S d, IsUniformlyBoundedConstructibleAdicTower d M →
    ∃ N : AdicTower T d, Nonempty (N.tower ≅ F.obj M.tower) ∧
      IsUniformlyBoundedConstructibleAdicTower d N ∧
      HasTowerAmplitudeCompatibleModels Amp growth Ffin M N

/-- TOW(square): each of the four specified completed-coefficient strict-tower functors
preserves every uniformly bounded constructible adic tower, with its full output data
and common local models compatible with finite-level AMP amplitude containments.
Source: blueprint order 1353 (blueprint: def-weil-pbc-tower-preservation). -/
def HasTowerPreservation {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) : Prop :=
  PreservesBoundedConstructibleAdicTowers d (HasFiniteLevelAmplification sq d)
      (fun c ↦ (c : ℤ)) (completedTowerDirectImage f d)
      (towerFiniteDirectImage f d) ∧
  PreservesBoundedConstructibleAdicTowers d (HasFiniteLevelAmplification sq d)
      (fun c ↦ (c : ℤ)) (completedTowerDirectImage f' d)
      (towerFiniteDirectImage f' d) ∧
  PreservesBoundedConstructibleAdicTowers d (HasFiniteLevelAmplification sq d)
      (fun _ ↦ 0) (completedTowerPullback g d)
      (towerFinitePullback g d) ∧
  PreservesBoundedConstructibleAdicTowers d (HasFiniteLevelAmplification sq d)
      (fun _ ↦ 0) (completedTowerPullback g' d)
      (towerFinitePullback g' d)

end AlgebraicGeometry.Scheme
