/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Telescope comparison for complexes of sheaves of modules

Source: Stacks Project, Derived Categories, Lemma 0949, and Cohomology on Sites,
Section 21.17 (blueprint: lem-pc-complex-hocolim-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  (E : ℕ ⥤ CochainComplex
    (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)

/-- The `1 - shift` endomorphism of the direct sum of a sequential system of
complexes (Stacks, Derived Categories, Definition of derived colimits;
blueprint: lem-pc-complex-hocolim-colimit). -/
noncomputable def telescopeShift :
    (∐ (fun n : ℕ => E.obj n)) ⟶ (∐ (fun n : ℕ => E.obj n)) :=
  Sigma.desc (fun n : ℕ =>
    Sigma.ι (fun n : ℕ => E.obj n) n -
      E.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι (fun n : ℕ => E.obj n) (n + 1))

/-- The canonical map from the direct sum of a sequential system of complexes
to its colimit (Stacks, Derived Categories, Lemma 0949;
blueprint: lem-pc-complex-hocolim-colimit). -/
noncomputable def telescopeToColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ colimit E :=
  Sigma.desc (fun n : ℕ => colimit.ι E n)

/-- (blueprint: lem-pc-complex-hocolim-colimit) For a sequential system of cochain
complexes of sheaves of modules on a ringed site, the canonical map from the cone
of `1 - shift` on its direct sum to its termwise filtered colimit is a
quasi-isomorphism (Stacks, Derived Categories, Lemma 0949).

In each degree, `1 - shift` is injective by examining the least nonzero summand.
Its cokernel is the filtered colimit, since the quotient relations identify an
element with its image in the next summand. The cone maps to this cokernel by
projection onto the unshifted summand. The kernel of this projection is
contractible: in the notation of the source proof, the homotopy sends
`(u(c), k)` to `(0, c)`. The long exact cohomology sequence of the resulting
short exact sequence makes the projection a quasi-isomorphism. -/
theorem quasiIso_telescopeColimit
    : ∃ f : mappingCone (telescopeShift R E) ⟶ colimit E,
      mappingCone.inr (telescopeShift R E) ≫ f = telescopeToColimit R E ∧
      (mappingCone.inl (telescopeShift R E)).comp
        (Cochain.ofHom f) (add_zero _) = 0 ∧
      QuasiIso f := by
  sorry

end CochainComplex
