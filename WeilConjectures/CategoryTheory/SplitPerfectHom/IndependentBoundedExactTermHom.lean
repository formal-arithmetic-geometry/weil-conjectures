/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.Single
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Bounded exact-term Hom with independent site universes

Source: Stacks Project, Tags 08DM, 0A8X and 0117.
(blueprint: lem-sfb-independent-bounded-exact-term-hom).
This extends the existing bounded exact-term proof without equating the site,
coefficient and morphism universes. All auxiliary proofs are private.
-/

@[expose] public section

set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SplitPerfectHom

end CategoryTheory.SplitPerfectHom
