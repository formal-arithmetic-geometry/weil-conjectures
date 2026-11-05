/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.Modules.AffineDescent
import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
/-! # Tensoring frames under monoidal pullback
Source: Stacks Project, Tags 0095 and 0096, tensor pullback coherence.
(blueprint: lem-pur-tensor-pullback-frames). -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' u'' v''
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

attribute [irreducible] tensorPullbackFrames

end AlgebraicGeometry.Scheme.Modules
