/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryPullbackSquare
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedTensorLifts
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareCoherence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # The component square on ordinary unbounded derived categories

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9, and the naturality
used in Corollary 4.4(2) (blueprint: lem-zl-component-derived-pullback-square).

The publicly imported data structures spell out the simultaneous witnesses and normalizations of
this one statement. All inverse images are the actual site inverse images. Module
transport uses the existing internal-module encoding and its equivalence with
`ringedSiteModules`; the derived categories and tensors are the ordinary ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- The component square gives the canonical natural isomorphism of exact symmetric
monoidal functors on ordinary unbounded derived categories, with all normalizations.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9, and naturality in
Corollary 4.4(2) (blueprint: lem-zl-component-derived-pullback-square).

Proof: `component_ordinary_pullback_square` supplies the normalized ordinary inverse
images, module square and its identity and composition equations.
`component_derived_tensor_lifts` supplies the normalized derived tensor structures
and the monoidality of the specified square. The proved
`component_derived_square_coherence` carries the two ordinary equations to the
canonical exact-derived comparisons. Assemble these data in `System`. For each
edge, `CategoryTheory.IsDualizable.map` applies its strong monoidal structure to
evaluation and coevaluation and verifies both triangle identities. This proves
all three preservation fields, including arbitrary unbounded complexes. -/
theorem component_derived_pullback_square
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] : Nonempty (System Λ) := by
  classical
  obtain ⟨s⟩ := component_ordinary_pullback_square Λ
  obtain ⟨t⟩ := component_derived_tensor_lifts Λ s
  obtain ⟨hi, hc⟩ := component_derived_square_coherence Λ s
  refine ⟨{
    corner := s.corner
    slice := s.slice
    square := s.square
    cornerTensor := t.corner
    sliceTensor := t.slice
    schemeTensor := t.scheme
    monoidal := t.monoidal
    sliceIdentity := s.sliceIdentity
    sliceComposition := s.sliceComposition
    identity := hi
    composition := hc
    cornerDuals := ?_
    sliceDuals := ?_
    schemeDuals := ?_ }⟩
  · intro X _ K hK
    let _ : ((s.corner X).derived Λ X).Monoidal := by
      unfold Corner.derived
      exact (t.corner X).monoidal
    exact hK.map ((s.corner X).derived Λ X)
  · intro X Y _ _ f K hK
    let _ : ((s.slice f).derived Λ).Monoidal := by
      unfold Slice.derived
      exact (t.slice f).monoidal
    exact hK.map ((s.slice f).derived Λ)
  · intro X Y _ _ f K hK
    let _ := (t.scheme f).monoidal
    exact hK.map (CondensedRing.upperStar Λ.X f).mapDerivedCategory

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
