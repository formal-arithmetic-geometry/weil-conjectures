/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Finite free resolutions on affine neighbourhoods

Source: Stacks Project, Coherent Modules, Lemma 01XZ and Algebra, Lemma 00LP
(blueprint: lem-sc-coherent-affine-free-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A coherent module on a Noetherian scheme is locally represented by a finite module on an
affine open, and admits there a bounded-above resolution by finite-rank free modules.
Source: Stacks Project, Coherent Modules, Lemma 01XZ and Algebra, Lemma 00LP
(blueprint: lem-sc-coherent-affine-free-resolution).

The bounded-above condition is expressed by vanishing above an integer bound, each finite-free
term by an isomorphism with `SheafOfModules.free`, and the augmentation by `QuasiIso` to the
degree-zero complex.

Proof:
1. Choose an affine open containing `x` from a locally Noetherian affine cover; its ring
   is Noetherian (def-weil-pbc-quasi-compact-scheme, pqf-def-locnoeth).
2. Coherence gives quasi-coherence and finite type (pqf-lem-coherent-ft-locnoeth).
   The affine sections criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) makes
   the module of sections finite. The tilde-Gamma counit
   (lem-weil-pbc-affine-tilde-gamma-adjunction) identifies its tilde with the restriction.
3. Resolve that module by finite free modules
   (lem-weil-pbc-finite-free-resolution-noetherian), apply tilde termwise, and put the
   terms in degrees `-i`. The tilde-stalk localization identification
   (lem-weil-pbc-spec-tilde-stalk-localization) and exactness of localization make the
   augmented complex exact on stalks. Exactness is detected on stalks
   (lem-weil-pbc-module-stalk-exact), so the augmentation is a quasi-isomorphism. -/
theorem coherent_affine_free_resolution
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (x : X) :
    ∃ (U : X.Opens) (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (_ : x ∈ U) (_ : IsAffineOpen U)
      (M : Type u) (_ : AddCommGroup M) (_ : Module A M) (_ : Module.Finite A M)
      (e : U.toScheme ≅ Spec (CommRingCat.of A)),
      Nonempty (F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj
        (tilde (ModuleCat.of A M))) ∧
      ∃ (E : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ),
        (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
        ∃ q : E ⟶ (CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) 0).obj (F.over U),
          QuasiIso q := by
  sorry

end AlgebraicGeometry
