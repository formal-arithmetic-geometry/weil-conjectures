/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
public import WeilConjectures.SmoothPurity.IntegralCoherence.SitePullbackMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence

/-! # Monoidal strict comparisons for the sequence-site pullback

Source: Stacks 07A4 and 0D6D; integral coherence, strict-model step.

The sequence-site pullback is the left adjoint of the actual sectionwise direct image.
Its pure-tensor normalized ordinary comparison makes it monoidal; the termwise functor
on unbounded cochain complexes inherits the comparison, its Koszul symmetry and the
compatibility with the adjunction-normalized compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
open CategoryTheory.CochainPullback (moduleTmul)

namespace WeilConjectures.IntegralCoherence

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance] sequenceMonoidal sequencePreadditive sequenceColimits
  sequenceLeftColim sequenceRightColim sequenceTensor sequenceFour sequenceLeft sequenceRight
  complexMonoidal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] sequenceBaseChange_representablyFlat

end WeilConjectures.IntegralCoherence
