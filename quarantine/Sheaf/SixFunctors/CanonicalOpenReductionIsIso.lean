/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData
import all Sheaf.SixFunctors.OpenReconstructionEffectivity

/-! # Invertibility of the canonical open coefficient mate

The comparison is the mate of the fixed, representative-normalized ordinary
pullback/reduction comparison, rather than an independently chosen open map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.GeneratorReduction

/-- Reduction commutes with exact open extension on the ambient derived category.
Source: Stacks 03DI and 07A7; the simultaneous quotient comparison in blueprint
`fix-prop-coherence.proof.md`, open-factor paragraph
(blueprint: lem-sf-canonical-open-reduction-is-iso).

Proof: this is the first half of the open reconstruction effectivity argument, which
holds for every input. Present the input on the good localization. The mate
localization lemma identifies the component of `realization.openReduction` at a
good representative, up to isomorphisms, with the localization of the ordinary
open reduction complex map. That map is invertible degreewise by the ordinary
open-mate invertibility, hence invertible. The library's `fixedOpenReduction_isIso`
(module `OpenReconstructionEffectivity`, blueprint
lem-sf-open-reconstruction-effectivity) carries out exactly this argument for
`o.system` and `o.realization`. -/
theorem canonicalOpenReduction_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (scalarReductionSource l E U)) :
    IsIso ((o.realization.openReduction l E j).app K) :=
  fixedOpenReduction_isIso l E o.system o.realization j K

end WeilConjectures.GeneratorReduction
