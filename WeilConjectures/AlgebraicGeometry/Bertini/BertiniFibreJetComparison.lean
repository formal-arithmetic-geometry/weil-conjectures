/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniSingularFibreCoordinates
public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniLocalFirstJets
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import Mathlib.LinearAlgebra.TensorProduct.Prod
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniLocalFirstJets
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Comparing the universal equation with its tensor of local first jets

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of lemma-bertini;
Morphisms, base change of differentials.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local irreducible] bertiniSingularIdeal bertiniUniversalIdeal
attribute [local irreducible] bertiniSingularFibreCoordinates bertiniSingularFibreCoefficient

attribute [local irreducible] Scheme.Modules.tensorPullbackSection
attribute [local irreducible] Scheme.Hom.relativeDifferentialsDerivation
attribute [local irreducible] Scheme.Hom.relativeDifferentials

set_option maxHeartbeats 800000 in
-- The fibre and sheaf restriction equalities require substantial dependent elaboration.
end AlgebraicGeometry
