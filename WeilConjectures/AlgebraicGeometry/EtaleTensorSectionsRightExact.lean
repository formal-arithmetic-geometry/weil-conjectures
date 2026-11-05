/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsCokernelExact

/-! # Right exactness of sheafified tensor sections

Source: blueprint `lem-sc-additive-ideal-image-tensor-comparison`, Proof, Step 2;
Stacks Project, Descent, Tag 070S, Lemma 35.8.5(2), and Tag 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-right-exact)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

end
end AlgebraicGeometry.Scheme.Modules
