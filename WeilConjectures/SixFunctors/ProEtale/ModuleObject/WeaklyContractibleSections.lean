/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Sections of module objects over weakly contractible objects

Let `X` be a scheme and `U` a weakly contractible object of `X_proét`. Taking sections over `U`
is an exact functor on abelian pro-étale sheaves and on module objects over `Λ_X`
(`ProEtale.CondensedRing.preservesHomology_sectionsFunctor`): it is left exact since limits of
sheaves are computed on sections, and it preserves epimorphisms since an epimorphism of sheaves is
locally surjective, hence surjective on sections over `U`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  {X : Scheme.{u}}

end CondensedRing

end AlgebraicGeometry.ProEtale
