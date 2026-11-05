/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierPairPullbackSection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback

/-! # Arbitrary inverse image of a relative framed torsor extension

Source: Stacks 03AJ and 0A45; naturality of short-exact extension classes
(blueprint: lem-asd-relative-framed-extension-pullback-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

open Opposite

attribute [local irreducible] framePullbackMap

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Scheme.Modules.framePullbackMap

end AlgebraicGeometry.Etale
