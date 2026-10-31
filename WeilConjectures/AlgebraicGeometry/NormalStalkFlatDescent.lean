/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.FaithfullyFlatNormalRingDescent
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Normal local domains descend along flat surjective scheme maps

Source: Stacks Project, Algebra, Tag 033G, lemma-descent-normal, applied to stalks.
(blueprint: lem-wf-normal-stalk-flat-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Normal local domains descend along a flat surjective morphism of schemes.
Source: Stacks Project, Algebra, Tag 033G, lemma-descent-normal.
(blueprint: lem-wf-normal-stalk-flat-descent).
Proof: Choose a point x above y by surjectivity. The local map O(Y,y) -> O(X,x)
is flat, hence faithfully flat. It is injective, so its source is a domain.
Normality descends by Algebra.normal_ring_of_faithfullyFlat: for a fraction a/b
integral over the source, its image belongs to the integrally closed target.
Thus a belongs to b times the target, and faithful flat ideal contraction puts
a in b times the source. Apply this at prime localizations; integral closedness
of all maximal localizations gives integral closedness of the source itself.
No Noetherian or quasi-compact hypothesis is used. -/
theorem normal_stalks_of_flat_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Surjective f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨hd, hn⟩ := hX x
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat A B :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  have : IsDomain A :=
    (FaithfulSMul.algebraMap_injective A B).isDomain (algebraMap A B)
  refine ⟨inferInstance, IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ ?_⟩
  exact (Algebra.normal_ring_of_faithfullyFlat A B
    (fun q _ ↦ ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors⟩) p).2

end AlgebraicGeometry.Scheme
