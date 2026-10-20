/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-!
# Boundary vanishing for the continuous algebraic-closure compatibility coefficient

This is the remaining coefficient case of the closed-support calculation in step 5.
It makes no assertion about the refinement comparison morphism or the localizing closure.

Source: blueprint main-20261015, det-sf-comp-coherence-refinement, proof step 5
(blueprint: lem-sf-refinement-boundary-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For the all-continuous-map algebraic-closure compatibility coefficient, proper
pushforward of extension by zero has zero restriction to the complementary closed subscheme,
on constructible sheaves placed in degree zero.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement, the algebraic-closure coefficient part of proof step 5
(blueprint: lem-sf-refinement-boundary-vanishing).

Proof: Write h for the proper ambient refinement and i for the complementary closed immersion.
Base change h along i. Boundary preservation identifies the inverse image of the distinguished
open with the source distinguished open. The base-changed closed subscheme therefore misses
that open, and exact inverse image of extension by zero there is zero. Extension by zero of
the single constructible sheaf remains bounded constructible: extend the finite
stratification of its support by the boundary stratum with zero constant model. The
coefficient-specific bounded proper base-change calculation identifies i* Rh* jprime!
with proper pushforward of that zero restriction. For this compatibility coefficient, this
calculation must be performed on the
finite constructible constant models after extension to the all-continuous-map ring; it is
not an identification of that ring with the finite-subextension-valued condensed algebraic
closure. The required coefficient comparisons carry the zero boundary restriction to zero.
The coefficient ring isomorphism in the hypothesis transports the same calculation to Λ.
Exactness identifies the termwise derived inverse image with the ordinary left-derived
inverse image, giving the displayed vanishing. The zero generator, identity refinement,
and empty boundary all reduce to the usual disjoint-support vanishing. Bounded
truncation dévissage is performed in the importing module, not left in this lemma. -/
theorem continuousAlgCl_refinementBoundaryVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (hΛ : Nonempty
      (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsZero ((upperStar Λ c.obj.obj.obj.i.closedComplement).mapDerivedCategory.obj
      ((lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
