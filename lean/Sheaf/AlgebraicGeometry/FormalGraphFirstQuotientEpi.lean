/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Reduction of a finite formal graph onto the closed fibre

Source: Stacks Project, Tags 0889(1), 087W and 00MB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of the finite comparison graph is surjective modulo J.
No torsion condition on the comparison arrow is required for this closed-fibre assertion.

Source: Stacks Project, Tag 0889(1), affine comparison argument, using the affine
formal-module dictionary of Tag 087W and exact finite completion of Tag 00MB.
Proof: Restrict to an affine open Spec(A). Coherent modules, their pullback and the
kernel of the displayed discrepancy correspond to finite A-modules. The compatible
family θ induces a map between their I-adic completions. Exactness of completion
identifies the completion of this kernel with the kernel of the completed discrepancy
on the completed pullback. Compatibility with a and a' makes (id, θ) a map into this
completed pullback. Its level n+1 component makes its discrepancy zero. Thus it lifts
into the completed kernel, and its first projection is the identity on completed F.
Reducing modulo I makes the completed first projection surjective. For a finite module,
its completion modulo I is canonically the original module modulo I, compatibly with
maps. Hence E -> F/IF is surjective on affine sections. These affine opens cover X,
so the displayed sheaf morphism is epi. For J=0 the graph is the usual graph; for J=1
the target quotient is zero. Zero modules and an empty scheme also satisfy the assertion.
(blueprint: lem-weil-pbc-formal-graph-first-quotient-epi). -/
theorem formalGraph_first_quotient_epi
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) :
    let t : formalModuleQuotient J (n + 1) F.obj ⟶
        formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
    let d : pullback a.hom a'.hom ⟶ formalModuleQuotient J (n + 1) F'.obj :=
      pullback.snd a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
        pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t
    Epi (kernel.ι d ≫ pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J 1 F.obj) := by sorry

end AlgebraicGeometry
