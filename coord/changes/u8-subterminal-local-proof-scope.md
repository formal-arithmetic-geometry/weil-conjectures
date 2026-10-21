# SheafOfModules.SubterminalLocal.subterminal_module_local_calculus

## Reason

The completed proof needs local helper typeclass registrations and an elaboration option.
Preflight conservatively flags changes to section commands, opens and attributes as potentially
visible to importers. They are scoped inside `section LocalCalculusProof`. All six helper
registrations are `attribute [local instance]` on proved private theorems; no global instance is
added. The original top-level `open` command is preserved. The comparison's additional site
variables and `open PresheafOfModules` are in its nested section.

## Old

```lean
theorem subterminal_module_local_calculus
    [J.Subcanonical]
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool ↦ if b then U else V)
      (fun b ↦ terminal.from (if b then U else V)) ∈ J (⊤_ C)) :
    Nonempty (Intersection.{c, v, r, w} R U V (U ⨯ V) prod.fst prod.snd) ∧
    (∀ Z : C, Z = U ∨ Z = V ∨ Z = (U ⨯ V) →
      ExactRestriction (jstar.{c, v, r} R Z) ∧
      ExactRestriction (jbang.{c, v, r} R Z) ∧
      DerivedExact.{_, _, _, _, w, w} (jstar.{c, v, r} R Z) ∧
      DerivedExact.{_, _, _, _, w, w} (jbang.{c, v, r} R Z) ∧
      PresheafFormula.{c, v, r} R Z ∧ SheafificationRestriction.{c, v, r} R Z) ∧
    JointDetection.{c, v, r, w} R U V := by
  sorry
```

There was no local proof section or private helper instance API. The original declaration
signature of `subterminal_module_local_calculus` is retained verbatim in the delivered Lean file;
none of its binders, universes, hypotheses or conclusion changes.

## New

```lean
section LocalCalculusProof
set_option backward.defeqAttrib.useBackward true
-- proved private helpers; registered only within this section:
attribute [local instance] sliceExtension_additive
attribute [local instance] sliceExtension_limits
attribute [local instance] sliceExtension_colimits
attribute [local instance] sliceRestriction_additive
attribute [local instance] sliceRestriction_limits
attribute [local instance] sliceRestriction_colimits
-- original public theorem with a complete proof
end LocalCalculusProof
```

These local helpers prove additivity and finite exactness of the constructed slice functors.
There is no changed public signature or definition, and no user adaptation is necessary.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SubterminalModuleLocalCalculus --uses
subterminal_module_local_calculus` lists the item and its sole downstream module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SubterminalModuleLocalCalculus | U8 | One hole closed; private proof helpers only. |
| Sheaf.CategoryTheory.SubterminalCoverModuleSES | unclaimed (no current claim file) | Unchanged signature and definitions; no adaptation. |

## Status

landed 20261021T171851-L-3168855 2026-10-21 (merge of deliver/U8/Sheaf.CategoryTheory.SubterminalModuleLocalCalculus)
