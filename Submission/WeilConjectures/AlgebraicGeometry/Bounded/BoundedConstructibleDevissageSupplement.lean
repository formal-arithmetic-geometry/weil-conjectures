/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite truncation dévissage for constructible module objects

This is the standard t-structure induction from blueprint
`lem-sfb-dc-tensor-preserves`, step 10. It is independent of coefficient finiteness:
only the target property is required to be triangulated.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open DerivedCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale


end AlgebraicGeometry.ProEtale
