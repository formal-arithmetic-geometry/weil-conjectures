/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Restriction and direct image of a depth-two module

Source: Stacks Project, Tag 0E9I.
(blueprint: lem-sbc-depth-two-hartogs-restriction)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Restriction followed by direct image recovers a coherent depth-two module.

Source: Stacks Project, Lemma 31.5.11, Tag 0E9I.
(blueprint: lem-sbc-depth-two-hartogs-restriction)

Proof: On any affine open of the locally Noetherian scheme, quasi-coherence
identifies N with the sheaf associated to its module of sections. The latter
is finite by hypothesis, hence finitely presented over the Noetherian affine
ring. Thus N is coherent. The canonical map N to j_*(N restricted to U) is
an isomorphism on U. At a point of the complement, the direct-image module
has no associated point there (Tags 0AVN and 05AM): the open immersion is
quasi-compact locally on the Noetherian affine opens, so its direct image
is quasi-coherent and Tag 0AVN applies. N has depth at least two by hypothesis.
The coherent-module comparison criterion of Tag 0AVM now proves that the
canonical map is an isomorphism everywhere. This is exactly the restriction
adjunction's unit: on an open V it is restriction of sections to V intersect U.
Equivalently, apply Tag 0E9I directly after the coherence check. The argument
is local and requires no global quasi-compactness. For U = top the unit is
already invertible; for U empty the criterion implies that N is zero.
The zero module is allowed since its depth is infinite. -/
theorem isIso_restrictAdjunction_unit_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) :
    IsIso ((Modules.restrictAdjunction U.ι).unit.app N) := by sorry

end AlgebraicGeometry.Scheme
