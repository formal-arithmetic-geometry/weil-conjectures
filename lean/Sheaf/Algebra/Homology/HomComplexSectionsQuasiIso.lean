/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal

/-!
# Sectionwise invariance of Hom complexes into K-injectives

Source: Stacks Project, sites-cohomology.tex, Lemmas 0A94 and 0A95
(blueprint: lem-pur-hom-complex-sections-quasi-iso).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The map of Hom complexes induces a quasi-isomorphism on sections over every site object.
Source: Stacks Project, sites-cohomology.tex, Lemma 0A95, using Lemma 0A94
(blueprint: lem-pur-hom-complex-sections-quasi-iso).

Proof: fix an object `U` and a degree `n`. The product projections in `homComplex_exists`
identify sections with families of morphisms on `C/U`. In degree zero the cocycle equation
is the chain-map equation, and degree-minus-one coboundaries are precisely null-homotopies.
The same calculation after shifting the first complex by `-n` identifies degree `n`
cohomology of sections with morphisms from the shifted first complex to the second in the
localized homotopy category, compatibly with pre- and postcomposition. Restriction of module
sheaves to `C/U` has exact extension by zero as a left adjoint, hence preserves K-injectives;
restriction itself is exact, hence preserves the quasi-isomorphisms `s` and `t` and their
shifts. Apply the canonical bijection `rhom_into_kinjective_local` to the shifted complexes
and both K-injective targets. The induced cohomology map is then composition with the
images of restricted `t` and `s` in the localized derived category. These images are
isomorphisms, so composition with their inverses is an inverse to the cohomology map.
Thus the homology map on sections is bijective in every degree, which for abelian groups
is equivalent to being an isomorphism. This is the claimed quasi-isomorphism. No step here
uses exactness of sheafification or a comparison with cohomology sheaves. -/
theorem homComplex_sections_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] (U : C) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    QuasiIso (((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)) := by
  sorry

end CategoryTheory
