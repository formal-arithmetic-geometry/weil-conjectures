module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.ResolutionStrata
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober

/-! # Finite prefixes of codimension resolution rules

The input objects are the existing `QERationalResolutionInput` (reduced Noetherian
quasi-excellent rational schemes, def-per-qe-ordinary-resolution-rule), and the unresolved
set, generic image points and schematic density over them are the existing notions of
def-per-resolution-strata.

Source: Temkin, Non-embedded Desingularization, §§4.1.1–4.1.5 and 4.3,
printed pp.26–31 (blueprint: def-per-codimension-resolution-prefix).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The actual center scheme maps to the original input, retaining its scheme structure.
Source: Temkin §4.1.3 (blueprint: def-per-codimension-resolution-prefix). -/
noncomputable def OrdinaryBlowupTower.centerToBase {X : Scheme.{u}} (A : OrdinaryBlowupTower X)
    (i : Fin A.length) : (A.center i).subscheme ⟶ X :=
  (A.center i).subschemeι ≫ A.toBase i.castSucc

/-- Pure image codimension `e` (every generic point of an irreducible component of the image,
with its subspace topology, has local dimension `e` in `X`) and schematic density of the
center over those generic image points, both in the sense of def-per-resolution-strata.
Source: Temkin §4.1.3 (blueprint: def-per-codimension-resolution-prefix). -/
def OrdinaryBlowupTower.CenterEquicodimensional {X : Scheme.{u}}
    (A : OrdinaryBlowupTower X) (i : Fin A.length) (e : ℕ) : Prop :=
  (∀ x ∈ X.genericPointsIn (Set.range (A.centerToBase i)),
    ringKrullDim (X.presheaf.stalk x) = ((e : ℕ∞) : WithBot ℕ∞)) ∧
  (A.centerToBase i).SchematicallyDenseOverGenericImage

/-- Resolution through codimension d requires closedness and excludes every local ring
of dimension at most d from the unresolved set.
Source: Temkin §4.1.2 (blueprint: def-per-codimension-resolution-prefix). -/
def OrdinaryBlowupTower.ResolvedThrough {X : Scheme.{u}} (A : OrdinaryBlowupTower X)
    (d : ℕ) : Prop :=
  IsClosed A.unresolvedSet ∧
    ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ ((d : ℕ∞) : WithBot ℕ∞) →
      x ∉ A.unresolvedSet

/-- Two towers agree off T with exactly empty centers contracted, using one common
restricted tower and the existing ideal-preserving cartesian comparisons.
Source: Temkin §§4.1.4–4.1.5 (blueprint: def-per-codimension-resolution-prefix). -/
def OrdinaryBlowupTower.AgreeOff {X : Scheme.{u}} (A B : OrdinaryBlowupTower X)
    (T : Set X) : Prop :=
  ∃ U : X.Opens, (U : Set X) = Tᶜ ∧
    ∃ C : OrdinaryBlowupTower U.toScheme,
      Nonempty (OrdinaryResolutionComparison U.ι A C) ∧
        Nonempty (OrdinaryResolutionComparison U.ι B C)

/-- A prefix R_0,...,R_d of finite rules with the codimension and compatibility conditions.
The category includes the empty scheme and finite disjoint unions. Every regular map is
allowed; no finite-type condition is imposed. Every ambient level is reduced Noetherian
quasi-excellent, and its map to Q is induced from the input. Centers remain reduced
schemes, rather than replacements by their underlying sets.
Source: Temkin §§4.1.1–4.1.5 and 4.3
(blueprint: def-per-codimension-resolution-prefix). -/
structure CodimensionResolutionPrefix (d : ℕ) where
  tower : ∀ _k : Fin (d + 1), ∀ X : QERationalResolutionInput.{u},
    OrdinaryBlowupTower X.scheme
  zero_length : ∀ X, (tower 0 X).length = 0
  ambient : ∀ k X (j : Fin ((tower k X).length + 1)),
    IsReduced ((tower k X).level j) ∧ IsNoetherian ((tower k X).level j) ∧
      ∀ U : ((tower k X).level j).affineOpens,
        IsQuasiExcellent Γ((tower k X).level j, U.1)
  centers : ∀ k X (i : Fin (tower k X).length),
    RingedSpace.IsCoherent ((tower k X).level i.castSucc).toRingedSpace
        ((tower k X).center i).toModules ∧
      Set.Nonempty (((tower k X).center i).support : Set ((tower k X).level i.castSucc)) ∧
      IsReduced ((tower k X).center i).subscheme ∧
      IsNowhereDense (((tower k X).center i).support : Set ((tower k X).level i.castSucc)) ∧
      ∃ e : ℕ, e ≤ k.val ∧ (tower k X).CenterEquicodimensional i e
  resolves : ∀ k X, (tower k X).ResolvedThrough k.val
  regular_pullback : ∀ k (X Y : QERationalResolutionInput.{u}) (f : Y.scheme ⟶ X.scheme),
    IsRegularSchemeMorphism f →
      Nonempty (OrdinaryResolutionComparison f (tower k X) (tower k Y))
  unresolved_decreasing : ∀ (k l : Fin (d + 1)), k ≤ l →
    ∀ X, (tower l X).unresolvedSet ⊆ (tower k X).unresolvedSet
  agreement : ∀ (k l : Fin (d + 1)), k ≤ l →
    ∀ X, (tower l X).AgreeOff (tower k X) (tower k X).unresolvedSet
  later_centers : ∀ (k l : Fin (d + 1)), k ≤ l → ∀ X (i : Fin (tower l X).length)
    (e : ℕ), (tower l X).CenterEquicodimensional i e → k.val < e →
      Set.range ((tower l X).centerToBase i) ⊆ (tower k X).unresolvedSet

/-- A compatible construction has a prefix at every natural number and retains every
previous rule literally at each successor. This asserts extension for the constructed
prefixes, rather than for arbitrary prefixes satisfying the same invariants.
Source: Temkin §4.3 (blueprint: def-per-codimension-resolution-prefix). -/
structure CodimensionResolutionConstruction where
  approximation : ∀ d : ℕ, CodimensionResolutionPrefix.{u} d
  successor : ∀ (d : ℕ) (k : Fin (d + 1)) (X : QERationalResolutionInput.{u}),
    (approximation (d + 1)).tower k.castSucc X = (approximation d).tower k X

/-- The single sequence determined by compatible prefixes, obtained from their last rule.
Source: Temkin §4.1.5 (blueprint: def-per-codimension-resolution-prefix). -/
def CodimensionResolutionConstruction.rule (C : CodimensionResolutionConstruction.{u})
    (d : ℕ) (X : QERationalResolutionInput.{u}) : OrdinaryBlowupTower X.scheme :=
  (C.approximation d).tower (Fin.last d) X

end AlgebraicGeometry
