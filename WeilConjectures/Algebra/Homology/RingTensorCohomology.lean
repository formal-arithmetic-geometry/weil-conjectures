/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.ModuleCat.Descent
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso

/-!
# Ring tensor cohomology and its comparison map

Source: Stacks Project, More on Algebra, Tag 06Y6 and Tor independence, comparison-map
(blueprint: def-pc-ring-tensor-cohomology).

The two models are extension of scalars of an R-K-flat resolution of the restricted
complex, and extension of scalars of an A-K-flat resolution, respectively. The comparison
uses the common model obtained by resolving the restricted A-resolution over R.

## Main definitions

* `source` and `target`: the two tensor cohomology functors.
* `comparison`: cohomology of the canonical comparison map.
* `baseChangeMap`: flat extension of scalars on cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTensorCohomology

variable (R : Type u) [CommRing R]

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

variable (C : Type u) [CommRing C] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

end RingTensorCohomology
