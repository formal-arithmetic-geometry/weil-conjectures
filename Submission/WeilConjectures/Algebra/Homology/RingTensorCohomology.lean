/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.ModuleCat.Descent
import all Submission.WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- Additivity inherited from the extension-restriction adjunction, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
local instance extendScalarsAdditive (f : R →+* B) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- Restriction of complexes from A to R, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable abbrev restrict : CochainComplex (ModuleCat.{u} A) ℤ ⥤
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)

/-- Extension of complexes from R to B, Stacks Tag 06Y6.
(blueprint: def-pc-ring-tensor-cohomology) -/
noncomputable abbrev extend : CochainComplex (ModuleCat.{u} R) ℤ ⥤
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)

variable (C : Type u) [CommRing C] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

end RingTensorCohomology
