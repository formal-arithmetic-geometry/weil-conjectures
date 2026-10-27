module

public import Sheaf.AlgebraicGeometry.SpaceDivisorPullback
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Mathlib.Topology.LocallyFinite

/-! # Locally finite divisors with prescribed support on an algebraic space

Source: Stacks Project, Divisors, Tags 0BE0, 0BE2 and 0BE3;
Spaces Divisors, Tags 0DMM and 0EPQ (blueprint: def-sfb-locally-finite-space-divisors).

The coefficients use the existing codimension-one point classes. They may have infinite
support globally; the closures of the nonzero terms must be locally finite.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Closure support of a prime divisor, using its existing point class.
Source: Stacks, Tag 0BE2 (blueprint: def-sfb-locally-finite-space-divisors). -/
def spacePrimeSupport (X : AlgebraicSpace S) (z : SpacePrimeDivisor X) :
    Set (Point X.obj.obj) := closure {z.val}

/-- Integer coefficients with locally finite prime-closure support, vanishing on W.
Source: Stacks, Tags 0BE0 and 0BE2
(blueprint: def-sfb-locally-finite-space-divisors). -/
def IsSupportedLocallyFiniteDivisor (X : AlgebraicSpace S) (W : Set (Point X.obj.obj))
    (d : SpacePrimeDivisor X → ℤ) : Prop :=
  LocallyFinite (fun z ↦ if d z = 0 then ∅ else spacePrimeSupport X z) ∧
    ∀ z, d z ≠ 0 → Disjoint (spacePrimeSupport X z) W

/-- The zero coefficients satisfy the support and local finiteness conditions.
Source: Stacks, Tag 0BE0 (blueprint: def-sfb-locally-finite-space-divisors).
Proof: all indexed closed supports are empty, and no coefficient is nonzero. -/
theorem supportedLocallyFiniteDivisor_zero (X : AlgebraicSpace S)
    (W : Set (Point X.obj.obj)) : IsSupportedLocallyFiniteDivisor X W 0 := by
  sorry

/-- Adding two locally finite supported families preserves the condition.
Source: Stacks, Tag 0BE0 (blueprint: def-sfb-locally-finite-space-divisors).
Proof: intersect the two finite-support neighborhoods of each point. Every prime
with nonzero sum coefficient belongs to one of the two finite sets there. Its
support avoids W because a nonzero sum has at least one nonzero summand. -/
theorem supportedLocallyFiniteDivisor_add (X : AlgebraicSpace S)
    (W : Set (Point X.obj.obj)) (d e : SpacePrimeDivisor X → ℤ)
    (hd : IsSupportedLocallyFiniteDivisor X W d)
    (he : IsSupportedLocallyFiniteDivisor X W e) :
    IsSupportedLocallyFiniteDivisor X W (d + e) := by
  sorry

/-- Negation preserves the same nonzero terms and their supports.
Source: Stacks, Tag 0BE0 (blueprint: def-sfb-locally-finite-space-divisors).
Proof: a coefficient is zero exactly when its negative is zero. Thus both conditions
are literally those for the original coefficient family. -/
theorem supportedLocallyFiniteDivisor_neg (X : AlgebraicSpace S)
    (W : Set (Point X.obj.obj)) (d : SpacePrimeDivisor X → ℤ)
    (hd : IsSupportedLocallyFiniteDivisor X W d) :
    IsSupportedLocallyFiniteDivisor X W (-d) := by
  sorry

/-- The additive subgroup of locally finite divisors supported outside W.
Source: Stacks, Tag 0BE0 (blueprint: def-sfb-locally-finite-space-divisors). -/
def supportedLocallyFiniteDivisorSubgroup (X : AlgebraicSpace S)
    (W : Set (Point X.obj.obj)) : AddSubgroup (SpacePrimeDivisor X → ℤ) where
  carrier := IsSupportedLocallyFiniteDivisor X W
  zero_mem' := supportedLocallyFiniteDivisor_zero X W
  add_mem' := fun hd he ↦ supportedLocallyFiniteDivisor_add X W _ _ hd he
  neg_mem' := fun hd ↦ supportedLocallyFiniteDivisor_neg X W _ hd

/-- The supported locally finite divisor group, with coefficientwise addition.
Source: Stacks, Tag 0BE0 (blueprint: def-sfb-locally-finite-space-divisors). -/
abbrev SupportedLocallyFiniteDivisors (X : AlgebraicSpace S)
    (W : Set (Point X.obj.obj)) := supportedLocallyFiniteDivisorSubgroup X W

/-- The open subset of represented point classes corresponding to a scheme open.
Source: Stacks, Tag 03BU (blueprint: def-sfb-locally-finite-space-divisors). -/
def schemeOpenPointSet (T : Over S) (V : T.left.Opens) :
    Set (Point (schemeSpace T).obj.obj) :=
  schemePointMap (𝟙 (yoneda.obj T)) '' (V : Set T.left)

/-- Cartier equations have the prescribed locally finite coefficient family when every
local DVR order agrees, extending the existing finite-support order convention.
Source: Stacks, Tag 0BE3 (blueprint: def-sfb-locally-finite-space-divisors). -/
def HasLocallyFiniteWeilDivisor (X : AlgebraicSpace S) (C : SpaceCartierDivisor X)
    (d : SpacePrimeDivisor X → ℤ) : Prop :=
  ∀ (U : X.SmallEtaleModel) (g : (chartTotalFractionRing X U)ˣ),
    SpaceCartierDivisor.HasEquation X C U (divisorFractionUnit X U g) →
    ∀ (y : (divisorBasisChart X U).left)
      (hy : ringKrullDim ((divisorBasisChart X U).left.presheaf.stalk y) = 1),
      d ⟨schemePointMap (X.smallEtaleInclusion.obj U).obj.hom y,
        ⟨X.smallEtaleInclusion.obj U, y, rfl, hy⟩⟩ = divisorChartOrder X U y g.val

/-- Flat pullback on coefficient divisors is the existing Cartier pullback, with both
coefficient families fixed by normalized local orders. This relation allows an étale
pullback of a prime to split, without choosing an arbitrary map on primes.
Source: Stacks, Tags 0EN9 and 0EPQ
(blueprint: def-sfb-locally-finite-space-divisors). -/
def IsLocallyFiniteDivisorPullback {X Y : AlgebraicSpace S} (p : X ⟶ Y)
    (hp : MapIsFlat p) (d : SpacePrimeDivisor Y → ℤ)
    (e : SpacePrimeDivisor X → ℤ) : Prop :=
  ∃ (C : SpaceCartierDivisor Y) (E : SpaceCartierDivisor X),
    HasLocallyFiniteWeilDivisor Y C d ∧ HasLocallyFiniteWeilDivisor X E e ∧
      SpaceCartierDivisor.IsFlatPullback p hp C E

end AlgebraicGeometry.AlgebraicSpace
