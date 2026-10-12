/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase

/-! # Finite affine realizations of coherent algebras with proper support

Source: Stacks Project, Lemma 09ZT, last sentence, and Lemma 0CYS
(blueprint: lem-weil-pbc-coherent-algebra-affine-finite-proper).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- An affine realization of a coherent algebra is finite, and proper over the base
when its underlying module has proper support.
Source: Stacks Project, Lemma 09ZT, final sentence, and Lemma 0CYS (3).

Proof: On an affine U = Spec R, coherence implies that B(U) is a finite R-module.
The algebra isomorphism identifies g inverse U with Spec B(U), so g is finite.
Proper support gives a closed subscheme Z of X proper over S whose ideal annihilates B.
On every affine U with ideal J defining Z, the projection Y times_X Z to Y is Spec of
B(U) to B(U)/J B(U), an isomorphism because J B(U) = 0. These local identifications
show the projection is an isomorphism. Y times_X Z is finite over Z, hence proper over S,
and transporting properness along the projection gives properness of g composed with f.
The empty realization and zero algebra satisfy the same finite and quotient tests.
(blueprint: lem-weil-pbc-coherent-algebra-affine-finite-proper). -/
theorem coherent_algebra_affine_finite_proper
    {X Y S : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : Y ⟶ X) [IsAffineHom g]
    (B : X.CommAlgebraSheaf) (α : B ≅ 𝒪⁎g)
    (hB : RingedSpace.IsCoherent X.toRingedSpace B.toModule)
    (hp : Scheme.Modules.HasSupportProperOver f B.toModule) :
    IsFinite g ∧ IsProper (g ≫ f) := by sorry

end AlgebraicGeometry
