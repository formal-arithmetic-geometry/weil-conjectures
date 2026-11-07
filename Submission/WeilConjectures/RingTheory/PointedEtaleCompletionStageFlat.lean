/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat

import Submission.WeilConjectures.RingTheory.StrictHenselizationCompletionFlatOverBase
import Mathlib.RingTheory.Unramified.Finite
import Submission.WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import Submission.WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Submission.WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import Submission.WeilConjectures.RingTheory.FlatColimitRings
import Mathlib.CategoryTheory.Limits.Preserves.Over

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Flatness from a pointed etale stage to the strict henselization completion

Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c).
(blueprint: lem-sc-pointed-etale-completion-stage-flat).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Every coprojection of the pointed etale algebra presentation becomes flat
when followed by completion at the extended maximal ideal.
Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c), paragraph
beginning “To finish the proof of (c)”.
(blueprint: lem-sc-pointed-etale-completion-stage-flat).

Proof: The given colimit cocone, with the identity isomorphism on its vertex,
is a strict henselization in the pointed-algebra definition. Apply
`strictHenselization_completion_flat_over_base` to make its completion flat over `R`.
The coprojection followed by completion is an `R`-algebra map from the etale stage `S`.
Use this map for the `S`-action on the completion; its algebra-map compatibility gives
an `R`-`S` scalar tower. An etale algebra is formally unramified and of finite type,
so Mathlib's `FormallyUnramified.flat_of_restrictScalars` makes the completion flat
as an `S`-module. By the definition of flat ring maps, this is the required flatness. -/
theorem pointedEtale_completion_stage_flat
    (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (c : Cocone ((ObjectProperty.ι
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) ⋙
        Over.forget (CommAlgCat.of R K)))
    (hc : IsColimit c)
    (t : ObjectProperty.FullSubcategory
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) :
    ((algebraMap c.pt
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R c.pt)) c.pt)).comp
        (c.ι.app t).hom.toRingHom).Flat := by
  let C := c.pt
  let S := t.obj.left
  let B := AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C
  have hC : IsStrictHenselization R K C := ⟨c, ⟨hc⟩, ⟨Iso.refl _⟩⟩
  have hflat := strictHenselization_completion_flat_over_base R K C hC
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp hflat
  have : Etale R S := t.property
  let f : S →ₐ[R] B := (IsScalarTower.toAlgHom R C B).comp (c.ι.app t).hom
  let : Algebra S B := f.toRingHom.toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  change f.toRingHom.Flat
  rw [RingHom.Flat]
  exact FormallyUnramified.flat_of_restrictScalars R S B


end Algebra
