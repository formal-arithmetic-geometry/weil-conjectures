# SheafOfModules.finite_ring_action_local_constancy

## Reason

Server stage-3 preflight flags the added section-local `variable` commands, expanded
`open` command and proof elaboration option as potentially changing the module
interface. This record documents their scope. The new helper sections contain only
private, fully proved definitions and theorems, and each variable section ends
before the original theorem. The original public theorem signature and every
public import are unchanged. There is no statement or definition repair, and no
new public declaration, notation, attribute or instance.

## Old

The original theorem has this signature, verbatim:

```lean
theorem finite_ring_action_local_constancy
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (Λ : Type (max uC vC)) [CommRing Λ] [Finite Λ]
    (F : CategoryTheory.ringedSiteModules.{max uC vC}
      ((sheafCompose J.toGrothendieck
        (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})).obj
          ((constantSheaf J.toGrothendieck CommRingCat.{max uC vC}).obj
            (CommRingCat.of Λ))))
    (hF : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ X : Type (max uC vC), Finite X ∧
          Nonempty
            ((((sheafCompose J.toGrothendieck
                (CategoryTheory.forget AddCommGrpCat.{max uC vC})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
              (constantSheaf (J.toGrothendieck.over V) (Type (max uC vC))).obj X)) :
    ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
          Nonempty (F.over V ≅
            ((commutativeSiteConstantModuleFunctor J.toGrothendieck Λ).obj M).over V)
```

The original module commands include:

```lean
set_option autoImplicit false
universe uC vC
open CategoryTheory
namespace SheafOfModules
```

There were no helper sections or section-local variable commands.

## New

The complete public theorem signature above is unchanged. The proof uses the
following module-local commands and helper sections:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC vC
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
noncomputable section

section ScalarRestriction
variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  (Λ : Type (max uC vC)) [CommRing Λ] {R : Sheaf K RingCat.{max uC vC}}
  (η : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
-- Private scalar-restriction and constant-model constructions.
end ScalarRestriction

section SliceConstants
variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ]
-- Private slice comparison constructions.
end SliceConstants

section FiniteRefinement
open CategoryTheory.Sheaf.ConstantForget
variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ] [Finite Λ]
  {F : Sheaf K (ModuleCat.{max uC vC} Λ)} {X : Type (max uC vC)} [Finite X]
-- Private finite image module proof.
end FiniteRefinement

section LocalRefinement
variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ] [Finite Λ]
  (G : Sheaf K (ModuleCat.{max uC vC} Λ))
-- Private relocalization proof.
end LocalRefinement
```

The helper-section variables do not enter the existing theorem's binders. The
noncomputable section closes after the existing theorem. Namespace opens and the
elaboration option are local to this file and do not change imported definitions.
The helpers construct actual functors, units, comparison isomorphisms and finite
image submodules; every proof is complete. The original theorem now uses those
helpers to prove exactly its original conclusion.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FiniteRingActionLocalConstancy | W6 | Original theorem proved; all existing public signatures and public imports unchanged. |

`python3 tools/downstream.py Sheaf.CategoryTheory.FiniteRingActionLocalConstancy
--uses finite_ring_action_local_constancy` reports zero downstream modules and
finds the theorem name only in the item itself. A source search confirms there are
no current Lean importers. This does not make the item unnecessary: its unfinished
DAG parent still needs exactly the original conclusion, which this proof supplies.
No consumer adaptation or target-statement review is required because no existing
public statement or definition changes meaning.

## Status

landed 20261021T120853-L-3974501 2026-10-21 (merge of deliver/W6/Sheaf.CategoryTheory.FiniteRingActionLocalConstancy)
