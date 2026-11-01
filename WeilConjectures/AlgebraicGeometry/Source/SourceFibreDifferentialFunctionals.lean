/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniLocalFirstJets
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.Relative.RelativeDifferentialSheafBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Extending a cotangent functional over a fixed source point

Source: Stacks Project, Morphisms, Tag 01V0, base change of differentials;
Sheaves, Tag 0098, stalks of module pullback.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Hom.relativeDifferentials Scheme.Hom.relativeDifferentialsHomEquiv
  Scheme.Hom.relativeDifferentialsDerivation Scheme.Hom.pushforwardDerivation

end AlgebraicGeometry
