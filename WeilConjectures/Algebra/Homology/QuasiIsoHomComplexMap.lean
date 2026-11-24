/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoOfSections

/-!
# Quasi-isomorphisms of sheaf Hom complexes into K-injectives

## References

* Stacks Project, Tag 0A94
* Stacks Project, Tag 0A95
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The map of sheaf Hom complexes obtained by precomposing with `t` and postcomposing
with `s` is a quasi-isomorphism when `s` and `t` are quasi-isomorphisms and both targets
of the Hom complexes are K-injective.
-/
theorem quasiIso_homComplex_map
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] :
    QuasiIso (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s) := by
  apply quasiIso_of_sections
  intro U
  exact homComplex_sections_quasiIso s t U

end CategoryTheory
