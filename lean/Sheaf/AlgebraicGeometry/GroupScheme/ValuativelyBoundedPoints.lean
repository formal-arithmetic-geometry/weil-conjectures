module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Valuation.Basic

/-! # Valuatively bounded generic points of a group scheme

Source: Prasad--Yu, On quasi-reductive group schemes, Lemma 3.7 and Proposition 4.3
(blueprint: def-sfb-valuatively-bounded-group-points).

Generic points are R-morphisms Spec L → D, canonically identified with L-points of
D ×_R Spec L. Functions are all global regular functions on that generic fibre.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ValuativelyBoundedPoints

/-- Generic points, expressed by the universal property of the generic fibre.
Source: Prasad--Yu, Lemma 3.7
(blueprint: def-sfb-valuatively-bounded-group-points). -/
abbrev genericPoints (R L : Type u) [CommRing R] [CommRing L] [Algebra R L]
    (D : Grp (Over (Spec (.of R)))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ D.X

/-- Integral points inside generic points: the range of canonical restriction.
Source: Prasad--Yu, Lemma 3.7
(blueprint: def-sfb-valuatively-bounded-group-points). -/
def integralPoints (R L : Type u) [CommRing R] [CommRing L] [Algebra R L]
    (D : Grp (Over (Spec (.of R)))) : Subgroup (genericPoints R L D) :=
  (pointsPrecomp D.X
    (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)))))).range

/-- Evaluation of a regular function on the generic fibre at an actual generic point.
Source: Prasad--Yu, Lemma 3.7 and the affine coordinate-ring argument
(blueprint: def-sfb-valuatively-bounded-group-points). -/
def evaluation (R L : Type u) [CommRing R] [CommRing L] [Algebra R L]
    (D : Grp (Over (Spec (.of R)))) (x : genericPoints R L D)
    (f : Γ(pullback D.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R L))), ⊤)) : L :=
  (Scheme.ΓSpecIso (.of L)).hom
    ((pullback.lift x.left (𝟙 (Spec (.of L)))
      (x.w.trans (Category.id_comp _).symm)).appTop f)

/-- Every regular function has a uniform integer lower bound on its valuations.
Zero values have valuation infinity, using the additive valuation's existing convention.
Source: Prasad--Yu, Lemma 3.7 and Proposition 4.3
(blueprint: def-sfb-valuatively-bounded-group-points). -/
def IsBounded (R L : Type u) [CommRing R] [Field L] [Algebra R L]
    (D : Grp (Over (Spec (.of R)))) (v : AddValuation L (WithTop ℤ))
    (M : Subgroup (genericPoints R L D)) : Prop :=
  ∀ f : Γ(pullback D.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R L))), ⊤),
    ∃ n : ℤ, ∀ x ∈ M, (n : WithTop ℤ) ≤ v (evaluation R L D x f)

end AlgebraicGeometry.ValuativelyBoundedPoints
