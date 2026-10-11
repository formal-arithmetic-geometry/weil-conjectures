/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finite étale covers and finite locally constant sheaves

Source: literature/blueprint/master/blueprint/sec-abelian-varieties/
  sk-prop-av-finite-etale-points/def-galois-categories.md, node def-galois-categories
  (blueprint: def-galois-categories).

The category of finite étale covers is `Scheme.FiniteEtale`, supplied by the
source library.  This file supplies the corresponding category of finite locally
constant sheaves of finite sets.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The category `FLC(Y)` of finite locally constant sheaves of finite sets on the
small étale site of `Y`, with morphisms of sheaves.

(blueprint: def-galois-categories)
Source: blueprint node `def-galois-categories`, category `FLC(Y)` clause.
The predicate expands the definition of finite locally constant sheaf from
`def-weil-pbc-etale-sheaves`; the full subcategory supplies exactly the sheaf
morphisms as its arrows. -/
abbrev FLC (Y : Scheme.{u}) : Type (u + 2) :=
  ObjectProperty.FullSubcategory
    (IsFiniteLocallyConstantEtaleSheafOfSets (T := Y))

end AlgebraicGeometry.Scheme
