/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Right adjoint to proper étale derived direct image

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale


/-- For finite coefficients, proper étale derived direct image has a right adjoint.
Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
(blueprint: lem-etale-proper-derived-direct-image-adjoint)

Proof in words: on each quasi-compact open of the base, a proper morphism is of
finite type and its geometric fibre dimensions have a common finite bound. The
proper base-change formula and the torsion cohomological dimension bound give
finite cohomological amplitude there. Higher direct images commute with filtered
colimits, hence with coproducts. The finite-amplitude argument then shows that
the unbounded derived direct image preserves coproducts on that open. Restriction
to such opens is exact, commutes with coproducts and detects isomorphisms, so the
coproduct comparison is an isomorphism globally. The source category of sheaves
of modules is Grothendieck abelian. Brown representability for its unbounded
derived category therefore gives a right adjoint to the exact,
coproduct-preserving derived direct image. -/
theorem isLeftAdjoint_proper_rightDerivedLowerStar
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] :
    (R((g)_*[ModuleCat.{u + 1} Λ])).IsLeftAdjoint := by sorry

end AlgebraicGeometry.Etale
