/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Closed lowest-cohomology loci for an affine finite-free complex

Source: Stacks Project, Tag 0BDL, local matrix calculation, and Tag 0EWY.
(blueprint: lem-sc-affine-free-lowest-matrix-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A bounded-above finite-free complex starting in degree a on an affine scheme
has a closed rank-r lowest-cohomology locus when its first term has rank s <= r.
This assertion concerns a supplied complex, with no perfectness, Tor-amplitude,
Betti function, point, or choice of open neighbourhood in its statement.
Source: Stacks Project, Tag 0BDL, local matrix calculation, and Tag 0EWY.
(blueprint: lem-sc-affine-free-lowest-matrix-locus).

Proof: Every term is free, hence flat. Bounded-above flat complexes compute derived
pullback termwise (06YD). Since all terms below a vanish, after any pullback the
lowest cohomology is the kernel of the outgoing differential. Choose free frames
in degrees a and a+1 and express that differential by its finite matrix of global
sections on the affine X. If s=r, let Z be the closed subscheme cut out by these
entries. Its quotient ideal is finitely generated, so its closed immersion is
locally of finite presentation. A morphism into X factors through Z precisely
when all pulled-back entries vanish. This implies its kernel is free of rank r.
Conversely, trivialize a rank-r kernel on affine source neighbourhoods. Its
inclusion into the degree-a term is a square injective map. By 0EWY the dual of
its cokernel is zero. Each coordinate of the outgoing map factors through that
cokernel and is zero. The matrix therefore vanishes locally and globally; the
local factors through Z agree because a closed immersion is a monomorphism.
If s<r, take the empty closed subscheme. A rank-r free kernel on any nonempty
affine source chart injects into the rank-s first term. Pad the target with r-s
zero coordinates. The resulting square injection has injective transpose by
0EWY, but its transpose kills a nonzero padded basis vector, a contradiction.
Thus the source is empty. Conversely both predicates hold on the empty source.
The empty immersion is locally of finite presentation. For s=r=0 the first term
and matrix are zero and Z=X. Empty X and all zero rings obey the same argument. -/
theorem exists_affineFreeLowestMatrixLocus
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (X : Scheme.{u}) [IsAffine X]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : ℤ) (s r : ℕ) (hsr : s ≤ r)
    (hbounded : ∃ c : ℤ, ∀ j : ℤ, c < j → IsZero (K.X j))
    (hlower : ∀ j : ℤ, j < a → IsZero (K.X j))
    (hfree : ∀ j : ℤ, ∃ n : ℕ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n))))
    (ha : Nonempty (K.X a ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin s)))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ X),
        (∃ g : T ⟶ Z, g ≫ i = h) ↔
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
                ((derivedPullback h).obj (DerivedCategory.Q.obj K))) r) := by sorry

end AlgebraicGeometry.Scheme
