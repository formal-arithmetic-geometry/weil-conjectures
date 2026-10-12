/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Local module models on a finite principal-open cover

Source: Stacks Project, Tag 08E7, finite-cover and local-model steps
(blueprint: lem-pc-affine-pseudo-coherent-localization-cover).
-/

@[expose] public section

universe u wA wX wL

open CategoryTheory

namespace AlgebraicGeometry

/-- A pseudo-coherent associated-sheaf complex has pseudo-coherent module localizations
on a finite principal-open cover. This asserts only the local models, not their gluing.

Source: Stacks Project, Tag 08E7, finite-cover and local-model steps, using the local
finite-free characterization in Tags 08CB and 08E5
(blueprint: lem-pc-affine-pseudo-coherent-localization-cover).

Proof:
1. At each point choose a neighbourhood and a bounded-above finite-free complex from
   scheme pseudo-coherence. Refine these neighbourhoods by principal opens D(f).
   Quasi-compactness of Spec A gives finitely many such opens. Their union is Spec A,
   so their defining elements generate the unit ideal.
2. Over D(f), restriction of tilde N agrees with tilde of the localization N_f:
   the sections on the principal-open basis are the same localized modules, with the
   same restriction maps. Apply this identification termwise to the input complex.
3. The affine tilde equivalence over A_f identifies the free terms of the local model
   with finite free A_f-modules. Full faithfulness lifts its differentials; faithfulness
   proves their consecutive composites vanish. Its upper bound is unchanged.
4. The affine derived equivalence over A_f reflects the model's derived isomorphism.
   Hence the localized input complex has this bounded-above finite-free representative.
   Empty Spec A permits the empty cover: its unit ideal is the zero ideal because A is
   the zero ring. No positive rank or nonempty cover is assumed. -/
theorem affine_pseudoCoherent_localization_cover (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    [∀ f : A, HasDerivedCategory.{wL} (ModuleCat.{u} (Localization.Away f))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : Scheme.IsPseudoCoherent (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M))) :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r, DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M)) := by sorry

end AlgebraicGeometry
