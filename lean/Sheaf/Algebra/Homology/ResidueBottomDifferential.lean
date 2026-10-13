/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # A single bottom differential tested on residue fields

Source: Stacks Project, Tag 00O0 and Tag 00NX.
(blueprint: lem-sc-residue-bottom-differential).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A differential with zero incoming term and vanishing residue homology is a split
injection with projective cokernel.

Source: Stacks Project, Tag 00O0, Lemma `cokernel-flat`, and Tag 00NX.
(blueprint: lem-sc-residue-bottom-differential).

Proof: Extension of scalars sends the zero incoming term to zero. Thus zero homology
at a says exactly that the residue extension of d(a,a+1) is injective. Apply
Module.finiteProjectiveCokernel_residue_localization at every prime to obtain a cover
by principal opens on which the differential is injective and its cokernel finite
projective. Injectivity descends from this cover: an element of the kernel vanishes
in each localization, and a module element vanishing at every prime is zero. Both
terms are finitely presented because they are finite projective. The cokernel is
finitely presented, being the quotient of a finitely presented module by the image
of a finite module. The localized cokernels are flat, so the cokernel is globally
flat; finitely presented flat modules are projective. Finally the abstract opcycles
are canonically isomorphic to the range quotient of d(a,a+1). Transfer projectivity
along this isomorphism and identify module injectivity with categorical monicity.
No boundedness and no vanishing in other homological degrees is used. -/
theorem residue_bottom_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (hz : IsZero (P.X (a - 1)))
    (hf₀ : Module.Finite R (P.X a))
    (hf₁ : Module.Finite R (P.X (a + 1)))
    (hp₀ : Module.Projective R (P.X a))
    (hp₁ : Module.Projective R (P.X (a + 1)))
    (hresidue : ∀ (p : Ideal R) [p.IsPrime],
      let Pp := ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj P
      IsZero (Pp.homology a)) :
    Mono (P.d a (a + 1)) ∧ Module.Projective R (P.opcycles (a + 1)) := by sorry

end CochainComplex
