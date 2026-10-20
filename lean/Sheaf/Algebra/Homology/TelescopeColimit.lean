/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.Algebra.Homology.TelescopeColimit

/-!
# Telescope comparison for complexes of sheaves of modules

The source library provides the canonical telescope-to-colimit quasi-isomorphism,
including its restrictions to both summands. The former shift name is retained as
an abbreviation of the source construction.

Source: Stacks Project, Derived Categories, Lemma 0949
(blueprint: lem-pc-complex-hocolim-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  (E : ℕ ⥤ CochainComplex
    (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)

/-- The `1 - shift` endomorphism of the direct sum of a sequential system of
complexes. This is the source library's construction (Stacks, Tag 0949;
blueprint: lem-pc-complex-hocolim-colimit). -/
noncomputable abbrev telescopeShiftColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ (∐ (fun n : ℕ => E.obj n)) :=
  telescopeColimitShift R E

end CochainComplex
