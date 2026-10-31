/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData

/-! # Finite affine free presentation data

Helpers for constructible module Hom descent in Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Finite affine free presentation data for a constructible module sheaf.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), via Tag 095N;
(blueprint: lem-weil-pbc-constructible-module-colimit-presentation-data) -/
structure ConstructibleModuleFinitePresentationData
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) where
  n : ℕ
  m : ℕ
  U : Fin n → X.Etale
  V : Fin m → X.Etale
  hU : ∀ i, IsAffine (U i).left
  hV : ∀ j, IsAffine (V j).left
  P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  P_eq : P = fun W =>
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free A)
  f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun i : Fin n => P (U i))
  g : (∐ fun i : Fin n => P (U i)) ⟶ F
  w : f ≫ g = 0
  hc : Nonempty (IsColimit (CokernelCofork.ofπ g w))

end AlgebraicGeometry
