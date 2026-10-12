/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData
import Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep

/-! Finite trace and filtration reduction for generic second cohomology.

Source: blueprint `lem-sc-affine-generic-finite-second`, proof paragraphs 1--3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsConnectedCurve

private theorem subsingleton_H_of_iso {X : Scheme.{u}}
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : A ≅ B)
    (hB : Subsingleton (Sheaf.H B 2)) : Subsingleton (Sheaf.H A 2) := by
  let := hB
  apply Function.Injective.subsingleton (f := Sheaf.H.map e.hom 2)
  intro x y hxy
  have h := congrArg (Sheaf.H.map e.inv 2) hxy
  simpa only [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply] using h

/-- A map into a second-cohomology object with subsingleton codomain is enough to
deduce subsingletonness of the source. -/
theorem subsingleton_of_injective {A B : Type*} (j : A → B)
    (hj : Function.Injective j) (hB : Subsingleton B) : Subsingleton A := by
  constructor
  intro x y
  apply hj
  exact Subsingleton.elim _ _

/-- The finite primary decomposition, trace retraction, normalization, and filtration
argument produce an injective map from the desired cohomology into that of a finite
normalization model, whose second cohomology is subsingleton.  The construction uses
the finite Galois-module equivalence, Sylow filtration, finite etale trace degree,
exact finite pushforward, unrestricted strict henselization stalk comparison, exact
inverse image, torsion acyclicity, the derived long exact sequence, and the normal
generic constant-sheaf comparison.  These are exactly paragraphs 1--3 of the
blueprint proof; the remaining target theorem is the formal retraction consequence.
(blueprint: lem-sc-affine-generic-finite-second-retraction) -/
theorem finite_stalk_second_cohomology_retraction
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (hconstant : ∀ {D : Scheme.{u}} (g : D ⟶ Spec (.of k)) [IsConnectedCurve g]
      [Smooth g] [IsAffine D] (ℓ : ℕ) [Fact ℓ.Prime],
      Subsingleton (Sheaf.H (D.constantZMod ℓ) 2))
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (N : Type (u + 1))
      (j : Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2 → N),
      Function.Injective j ∧ Subsingleton N := by
  obtain ⟨r, D, g, hg, hsmooth, haffine, hintegral, n, F, hzero, hstep, j, hj⟩ :=
    exists_generic_finite_trace_filtration_data f hmodel M hM hfinite
  let : ∀ i, IsIntegral (D i) := hintegral
  have hvanish (i : Fin r) (a : ℕ) (ha : a ≤ n i) : Subsingleton
      (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField).obj
        (F i a)) 2) := by
    let := hg i
    let := hsmooth i
    let := haffine i
    let := hintegral i
    induction a with
    | zero =>
      exact Sheaf.subsingleton_H_of_isZero
        (Functor.map_isZero _ (hzero i)) 2
    | succ a ih =>
      obtain ⟨S, ℓ, hℓ, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hstep i a (by omega)
      let : Fact ℓ.Prime := ⟨hℓ⟩
      let T := Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField
      have hprev := ih (by omega)
      have hfirst : Subsingleton (Sheaf.H (T.obj S.X₁) 2) :=
        subsingleton_H_of_iso (T.mapIso e₁) hprev
      have hnext := subsingleton_generic_prime_filtration_step (g i) S hS ℓ hℓ e₃
        (hconstant (g i) ℓ) hfirst
      exact subsingleton_H_of_iso (T.mapIso e₂).symm hnext
  let : ∀ i, Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField).obj
        (F i (n i))) 2) := fun i ↦ hvanish i (n i) le_rfl
  exact ⟨_, j, hj, inferInstance⟩

end AlgebraicGeometry.IsConnectedCurve
