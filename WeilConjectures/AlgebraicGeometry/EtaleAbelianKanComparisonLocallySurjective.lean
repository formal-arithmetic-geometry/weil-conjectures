/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSmallUniverse
import Mathlib.Algebra.Category.Grp.Ulift

/-! # The underlying-set Kan comparison for an abelian inverse image

Source: Stacks Project, Tags 00YV, 09XN, and 00WK.
(blueprint: new-r2-etale-abelian-kan-comparison-locally-surjective). -/

@[expose] public section

universe u
open CategoryTheory Opposite AlgebraicGeometry

