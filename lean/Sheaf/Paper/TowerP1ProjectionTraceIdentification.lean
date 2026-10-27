/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.Paper.TowerP1TriangleWords
public import Sheaf.Paper.TowerP1KernelScalarData

/-! # Identification of the two normalized projective-line traces

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md
(blueprint: lem-sp-tower-p1-projection-trace-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- The traces obtained by inverting exchange are the normalized splitting traces.
Source: Reduction of the triangle identities, base change of the trace
(blueprint: lem-sp-tower-p1-projection-trace-identification).

Proof: the ordinary coefficient-pullback maps of k and of p.classes.projective agree:
transpose them under the ordinary adjunction, evaluate at each level, and use their
scalar-unit normalization on every section. The line-pullback maps agree by the same
argument on the generators a tensor z of the finite root tensor. Thus their derived
maps and shifted maps agree. For the first projection use the canonical pullback square
and composition normalization to identify the comparison for the opposite line with
p.line2Iso; for the second it identifies it with p.line1Iso. Substitute these identities
in hk.trace_base_change. Its exchange is the exchange mate followed by the shifted-line
map. Precompose by the inverse shifted-line map and inverse exchange mate, both known
invertible on the shifted Tate object. Cancellation gives exactly projectionTrace1 and
projectionTrace2. Split the Boolean index into its two constructors. This uses equality
of ordinary sheaf maps only on generators, never faithfulness of derived evaluation.
The argument allows zero coefficients and empty schemes. -/
theorem towerP1_projectionTrace_eq (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) (k : KernelSplittingData l E p)
    (hk : KernelScalarNormalization l E p k) :
    ∀ a : Bool, projectionTrace l E h a = k.trace l E a := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
