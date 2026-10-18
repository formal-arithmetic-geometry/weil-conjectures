/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Torsion subsheaf of an injective complex

Source: Stacks Project, Cohomology on Sites, Tag 0DD7, `lemma-torsion`
(blueprint: lem-trf-torsion-injective-subcomplex).
-/

@[expose] public section

set_option autoImplicit false

universe u v t w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/--
The torsion subsheaf comparison for an unbounded complex of injective abelian sheaves.
Source: Stacks Project, Cohomology on Sites, Tag 0DD7, `lemma-torsion`
(blueprint: lem-trf-torsion-injective-subcomplex).

The conclusion records the termwise torsion subsheaves by their sectionwise image
criterion. Step 1 uses restriction, common refinements, and composition of coverings
from `def-weil-pbc-sites-and-cohomology` to make the torsion sections a subcomplex.
Step 2 uses `lem-trf-injective-abelian-sheaf-divisible` and
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` to divide sections locally in
all degrees. Step 3 uses `def-weil-abstract-derived-category`,
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, and
`lem-weil-pbc-sheafification-exact` for local cycle representatives and boundaries.
Step 4 corrects a cycle by a locally divisible primitive to prove local surjectivity
on cohomology, and Step 5 applies the same construction in degrees `r - 1` and
`r - 2` to prove local injectivity; these steps use the preceding four dependencies.
Step 6 glues the local preimages by the sheaf axiom and identifies the result with
`QuasiIso`, using `def-weil-pbc-sites-and-cohomology` and
`def-weil-abstract-derived-category`. The argument applies in every integer degree
and chooses annihilating positive integers only after local refinement, so it assumes
neither boundedness nor a common annihilator.
-/
theorem torsion_injective_subcomplex
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v t}]
    (I : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}) ℤ)
    (hI : ∀ r : ℤ, Injective (I.X r))
    (hH : ∀ r : ℤ,
      ∀ (U : C) (s : ((HomologicalComplex.homology I r).obj.obj (Opposite.op U))),
        ∃ (R : Presieve U), R ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), R f →
            ∃ n : ℕ, 0 < n ∧ n • (HomologicalComplex.homology I r).obj.map f.op s = 0) :
    ∃ (T : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v t}) ℤ)
      (j : T ⟶ I),
      (∀ r : ℤ, Mono (j.f r)) ∧
      (∀ (r : ℤ) (U : C) (s : (I.X r).obj.obj (Opposite.op U)),
        ((∃ t : (T.X r).obj.obj (Opposite.op U),
            (j.f r).hom.app (Opposite.op U) t = s) ↔
          ∃ (R : Presieve U), R ∈ J U ∧
            ∀ (V : C) (f : V ⟶ U), R f →
              ∃ n : ℕ, 0 < n ∧ n • (I.X r).obj.map f.op s = 0)) ∧
      QuasiIso j := by
  sorry

end CategoryTheory.Sheaf
