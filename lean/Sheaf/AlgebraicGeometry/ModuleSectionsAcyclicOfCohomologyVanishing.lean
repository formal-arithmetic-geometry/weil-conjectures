module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Module-cohomology vanishing on all opens implies acyclicity for sections on all opens.

Source: Stacks Project, Cohomology of Sheaves, Tag 01E1 (2), and the final clause of 01EX.
(blueprint: lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing).

Proof: Fix V and choose an injective resolution F → J• in S.Modules, which has enough
injectives. Restriction to V is exact and preserves injectives by Tag 01E1 (2), so the
restricted augmented complex is an injective resolution of F|V. Evaluation of J• at V
computes the right derived functors of the module-valued sections functor on S.Modules.
Global sections of the restricted resolution compute moduleCohomology on V.toScheme.
For each term, restricted global sections are the original sections on V. The canonical
identification of O_V(V) with O_S(V) transports the scalar module structures; it is
compatible with all differentials. Hence these complexes have the same cohomology up
to that scalar equivalence. Equivalences preserve and reflect zero objects. The assumed
vanishing in degree q+1 gives IsZero for the (q+1)-st right derived sections object.
Quantifying over q is rightAcyclic, and quantifying over V gives the conclusion. -/
theorem module_sections_acyclic_of_cohomology_vanishing (S : Scheme.{u}) (F : S.Modules)
    (hcoh : ∀ (V : S.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace p).obj
        ((restrictFunctor V.ι).obj F))) :
    ∀ V : S.Opens,
      (SheafOfModules.forget.{u} S.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} S.ringCatSheaf.obj (op V)).rightAcyclic F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
