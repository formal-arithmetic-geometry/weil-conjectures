/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerP1CtfData
import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerUniformEtaleDomains
import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerP1ProperCtf
import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerP1LevelCtfModel

/-! # Uniform constructible finite-Tor domains for the projective-line tower functors

Source: the standing-setting restriction and Levels of the projective-line tower proof.
The definitions are re-exported unchanged from TowerP1CtfData. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1Uniform

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
