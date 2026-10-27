/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescentData

/-! # Full faithfulness for the descended line module

Source: Stacks Project, Descent, Tag 023T; Spaces Descent, Tag 04W8
(blueprint: lem-trf-polarized-line-iso-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Over a fixed chart-compatible scheme isomorphism, the compatible global line
isomorphism exists uniquely. Scheme maps and their effectivity are not asserted here.

Source: Stacks Project, Descent, Tag 023T; Spaces Descent, Tag 04W8, full faithfulness
(blueprint: lem-trf-polarized-line-iso-descent).

Proof:
1. Base change the covering of S to the source Y and transport it along its chart
   isomorphisms to X_i. The result is an etale, hence fpqc, covering of Y.
2. Over X_i define the local isomorphism e^*M' to M by pulling the target chart
   trivialization along the equality of chart maps, then composing with the inverse
   source trivialization. Normalize all composite pullbacks by the canonical
   tensorPullbackCompositionIso. The two realization equations for lambda give the
   same local map on every double overlap; associativity cancels the common lambda.
3. Both e^*M' and M are invertible, hence quasi-coherent. Full faithfulness of fpqc
   module descent (Tag 023T) glues these maps uniquely. Their inverses also agree and
   glue; faithfulness proves the two inverse equations. Thus the global map is an
   isomorphism. Its restriction is exactly the displayed line equation, by the
   definition of the local maps. Faithfulness makes any other isomorphism satisfying
   those equations equal to it. This includes the empty scheme and repeated charts. -/
theorem existsUnique_polarizedLineIso
    {S : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ U i}
    {L : ∀ i, (X i).Modules} {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (d d' : PolarizedDescentPair U uMap X f L)
    (hd : IsPolarizedDescentRealization D d) (hd' : IsPolarizedDescentRealization D d')
    (e : d.Y ≅ d'.Y) (he : e.hom ≫ d'.g = d.g)
    (hc : ∀ i, polarizedChartMap d i ≫ e.hom = polarizedChartMap d' i) :
    ∃ μ : (Scheme.Modules.tensorPullback e.hom).obj d'.M ≅ d.M,
      (∀ i, polarizedPullLine (polarizedChartMap d i) e.hom d'.M d.M μ ≪≫
          polarizedChartLine d i =
        polarizedModuleCongr (hc i) d'.M ≪≫ polarizedChartLine d' i) ∧
      ∀ ν : (Scheme.Modules.tensorPullback e.hom).obj d'.M ≅ d.M,
        (∀ i, polarizedPullLine (polarizedChartMap d i) e.hom d'.M d.M ν ≪≫
            polarizedChartLine d i =
          polarizedModuleCongr (hc i) d'.M ≪≫ polarizedChartLine d' i) → ν = μ := by sorry

end AlgebraicGeometry
