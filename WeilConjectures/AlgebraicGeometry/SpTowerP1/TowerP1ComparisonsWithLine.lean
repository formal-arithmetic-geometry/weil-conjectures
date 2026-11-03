/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1EtaleOriginComparisons

/-! # The shifted Tate line in the projective-line comparison domain

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Construction and Levels (blueprint: lem-sp-tower-p1-etale-origin-comparisons).
-/

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
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- The same canonical comparisons, exposing their specialization to the shifted Tate line.
Source: Construction, the invertible-twist comparison; Levels, the root-site comparison
(blueprint: lem-sp-tower-p1-etale-origin-comparisons). -/
structure EtaleOriginComparisonsWithLine (p : Presentation l E S hS) (d : Maps l E p) :
    Prop extends EtaleOriginComparisons l E p d where
  line_domain : domain l E p.classes.base (ProjectiveLine S)
    ((SpTowerClasses.line l E p.classes.chernP)⟦(2 : ℤ)⟧)

end AlgebraicGeometry.ProEtale.SpTowerP1
