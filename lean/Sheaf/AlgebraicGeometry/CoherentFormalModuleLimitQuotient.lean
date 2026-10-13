/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

import Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineProjections
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Ideal-power quotients of coherent formal-module limit sheaves

Source: Stacks Project, Lemma 087W, the formula M/I^n M = M_n.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical limit projection identifies the ideal-power quotient with its level.
Source: Stacks Project, Lemma 087W, the projection-kernel calculation; the local
uniqueness argument in Lemma 088B.
(blueprint: lem-weil-pbc-coherent-formal-module-limit-quotient)

Proof: Evaluation on an affine open V preserves limits. The unique isomorphism of
limiting cones identifies the evaluated projection with the module-limit projection.
Apply coherentFormalModule_affine_projections: it is surjective and has kernel
J(V)^(n+1) times the section limit. Apply the ideal-power clauses of
ideal_times_quasiCoherent_affine_sections to the unit sheaf, which is quasi-coherent:
the power inclusion has range J(V)^(n+1). Multiplication followed by the projection
vanishes on pure tensor germs, since the ideal power annihilates the projected level.
Pure tensors generate tensor stalks, so the composite sheaf morphism is zero.
Hence its sheaf image lies in
the kernel, without any assertion that evaluation preserves images of arbitrary
module sheaves. Conversely the kernel formula expresses each affine kernel section
as a finite sum of ideal-power sections times limit sections. Lift each ideal scalar
through the power inclusion and form the sum of pure tensor sections; its image is
that kernel section. Thus the kernel lies in the multiplication image locally, and
the two subsheaves coincide. Affine surjectivity makes the projection epic.
The projection is consequently
a cokernel of that multiplication-image inclusion. Uniqueness of cokernels gives
the displayed isomorphism and its projection equation. No quasi-coherence of the
limit sheaf is asserted or used. For J=0 the kernel is zero; for J=1 every level is
zero and the quotient is zero. The same calculation includes zero and empty schemes.
-/
theorem coherentFormalModule_limit_quotient {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G : CoherentFormalModule Y J) (n : ℕ) :
    ∃ e : formalModuleQuotient J (n + 1) (limit G.obj) ≅ G.obj.obj (op n),
      formalModuleQuotientπ J (n + 1) (limit G.obj) ≫ e.hom =
        limit.π G.obj (op n) := by sorry

end AlgebraicGeometry
