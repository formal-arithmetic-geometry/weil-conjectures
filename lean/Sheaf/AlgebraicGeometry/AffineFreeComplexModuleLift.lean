/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Lifting an affine free complex and its unit coefficient

Source: Stacks Project, Tags 01I7 and 00MT, the affine comparison before pivot elimination.
(blueprint: lem-pc-affine-free-complex-module-lift)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Lift the original complex, before any cancellation, to modules with finite bases.

Source: Stacks Project, Tag 01I7 (affine associated-sheaf equivalence), and Tag 00MT
(the supplied matrix entry). (blueprint: lem-pc-affine-free-complex-module-lift)

Proof: In degree k take the module of finitely supported functions on the supplied basis
in degree -k. Identify its associated sheaf with P.X (-k) using tildeFinsupp and e.symm.
Use fullness of tilde to lift the conjugated differential, and faithfulness to prove
its shape and square-zero equations. These give a chain complex C. Reindex the canonical
ULift basis by Fin, set m k = n (-k), and transport the supplied pivot indices.
The isomorphism isoTop, followed by the structure-sheaf global-sections isomorphism,
identifies the coordinates of the lifted differential with freeMatrix. This is an
isomorphism of rings, so the given unit coefficient stays a unit. The chosen sheaf
identifications give φ and its differential compatibility. Double negation gives
m (-j) = n j. No rank reduction or homotopy equivalence is asserted here; this is only
the affine lifting step. Empty bases cannot contain the supplied indices; the zero
ring is allowed, since preservation of units does not use nontriviality. -/
theorem exists_affine_free_complex_module_lift (R : CommRingCat.{u})
    (P : CochainComplex (Spec R).Modules ℤ) (n : ℤ → ℕ)
    (e : ∀ j : ℤ, P.X j ≅ SheafOfModules.free
      (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin (n j))))
    (i : ℤ) (p : ULift.{u} (Fin (n i))) (q : ULift.{u} (Fin (n (i + 1))))
    (hunit : IsUnit (freeMatrix ((e i).inv ≫ P.d i (i + 1) ≫ (e (i + 1)).hom) q p)) :
    ∃ (C : ChainComplex (ModuleCat.{u} R) ℤ) (m : ℤ → ℕ)
      (b : ∀ k : ℤ, Module.Basis (Fin (m k)) R (C.X k))
      (p' : Fin (m (-i))) (q' : Fin (m (-i - 1))),
      (∀ j : ℤ, m (-j) = n j) ∧
      IsUnit (LinearMap.toMatrix (b (-i)) (b (-i - 1))
        (C.d (-i) (-i - 1)).hom q' p') ∧
      ∃ φ : ∀ j : ℤ, tilde (C.X (-j)) ≅ P.X j,
        ∀ j k : ℤ, (ComplexShape.up ℤ).Rel j k →
          (φ j).hom ≫ P.d j k = tilde.map (C.d (-j) (-k)) ≫ (φ k).hom  := by sorry

end AlgebraicGeometry.Scheme.Modules
