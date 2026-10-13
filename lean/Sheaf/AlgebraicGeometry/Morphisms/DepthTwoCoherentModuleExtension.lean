/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # A coherent depth-two module extending a finite etale algebra

Source: Stacks Project, Tags 0EY6, 0EBJ, 0EBI and 0E9I.
(blueprint: lem-sbc-depth-two-coherent-module-extension)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- The underlying finite etale module admits a coherent extension of depth two.

Source: Stacks Project, Tag 0EY6 proof of (1), Tags 0EBJ and 0EBI.
(blueprint: lem-sbc-depth-two-coherent-module-extension)

Proof: On each affine Noetherian open V, U intersect V is quasi-compact.
The finite etale direct image on this intersection is finite locally free.
Extend it to a finite module M on V and sheafify its double dual N. Localization
commutes with duals of finite presentations, so the double dual restricts to
that locally free module. Present the dual of M by finite free modules;
dualizing gives an injection of N into a finite free module with image the
kernel of a map to another finite free module. At a boundary stalk choose a
regular pair x,y of the base ring. Multiplication by x is injective on N.
If y n = x n' in N, compute in the free source to write n = x m. The equation
x d(m) = 0 in the free target forces d(m) = 0, so m belongs to N. Thus y is
injective on N/xN. Nakayama gives properness for a nonzero finite stalk;
the zero stalk has infinite depth. The modules N are coherent and have finite
sections on affine opens and finite stalks. On overlaps, Hartogs (Tag 0E9I)
identifies each with the direct image of its common restriction. These canonical
identifications satisfy the cocycle condition and glue the modules and their
restriction isomorphisms. Coherence and boundary depth are local, so no global
quasi-compactness is required. For an empty cover take the zero module. -/
theorem exists_depth_two_coherent_module_extension
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    ∃ N : L.Modules,
      N.IsQuasicoherent ∧
      (∀ V : L.Opens, IsAffineOpen V →
        Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V))) ∧
      (∀ y : L, y ∉ U →
        ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) ∧
      Nonempty (Modules.restrict N U.ι ≅ Modules.restrict B.toModule U.ι) := by sorry

end AlgebraicGeometry.Scheme
