/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!
# A representing trace is not unique without normalization

Source: the finite-orientation normalization in blueprint `def-route-smooth-trace`.
The two signs give distinct representing traces even for the identity of a geometric point.
(blueprint: lem-pur-geometric-point-trace-not-unique)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

attribute [local irreducible] AlgebraicGeometry.Spec

omit [Fact (ringChar k).Prime] in
omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_quasiCompact :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_isSeparated :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

attribute [local irreducible] CategoryTheory.Over.mk

attribute [local instance] pointObstruction_locallyOfFiniteType
  pointObstruction_quasiCompact pointObstruction_isSeparated

attribute [local semireducible] CategoryTheory.Over.mk

omit [Fact (ringChar k).Prime] in
end AlgebraicGeometry.ProEtale.CondensedRing
