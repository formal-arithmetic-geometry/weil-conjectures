# AlgebraicGeometry.schemeGlobalHom_baseChange_exchange

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Its archive already has
zero textual holes. Compiling that archive fails at its final simpa: the historical
schemeGlobalSectionsDirectImageIso occurs in the proof, but the adopted
schemeGlobalHomDirectImageMap uses mixedGlobalSectionsDirectImageIso. The compatibility
and adopted Leray definitions choose from the same existential proposition. A private
reflexivity theorem identifies these choices, including inverse components, by proof
irrelevance. Rewriting with that theorem repairs the exchange proof without expanding
both large Leray constructions in the final equation. Expanding both in that equation
was tested and timed out at 60 seconds; the separate equality compiles in 2.6 seconds.

No public signature, definition, instance, attribute, or public import changes relative
to the archive. No source-library file changes. The existing source boundaries and the
unit route are preserved. No Challenge target or definition used by a target changes
meaning. The quarantine archive is retained, and the actual original module and its
Lean attachment are restored rather than withdrawn.

## Old

The file is absent from lean/, with its preserved source at
quarantine/Sheaf/AlgebraicGeometry/GlobalHomBaseChangeExchange.lean. That archived
public theorem signature is retained byte for byte. Its final normalization was:

```lean
      simpa only [schemeGlobalDerivedHom, schemeGlobalHomDirectImageMap,
        schemeGlobalDerivedHom_pullback_comparison, Functor.comp_map, Functor.comp_obj,
        b, b₁, d, E, E', a, p, H, c, Functor.prod_obj, Functor.op_obj,
        Functor.map_comp, Category.assoc] using ht
```

## New

Restore the archived module and theorem, adding this proved private equality:

```lean
private theorem schemeGlobalSectionsDirectImageIso_eq_mixed
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeGlobalSectionsDirectImageIso f = mixedGlobalSectionsDirectImageIso f := by
  rfl
```

The private theorem is scoped under the two backward.isDefEq.respectTransparency
options set to true. Add its name to the final simpa only set:

```lean
      simpa only [schemeGlobalDerivedHom, schemeGlobalHomDirectImageMap,
        schemeGlobalDerivedHom_pullback_comparison,
        schemeGlobalSectionsDirectImageIso_eq_mixed, Functor.comp_map, Functor.comp_obj,
        b, b₁, d, E, E', a, p, H, c, Functor.prod_obj, Functor.op_obj,
        Functor.map_comp, Category.assoc] using ht
```

Remove the five redundant private imports named in report.md. The public import of
GlobalHomPullbackComparison stays exactly as archived. The node keeps its declaration,
Lean attachment, statement, and dependencies; its final proof step records the rewrite.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | M2 (assigned rework) | Restore path and repair final proof; zero holes before and after. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | quarantined; unchanged | Sole archived direct importer and declaration user, at its exchange invocation. Exact original exchange signature is unchanged; a separate compiled consumer applies the restored theorem at that signature. No adaptation required. |

No active source importer was found by searching both library roots. tools/downstream.py
reports unknown module because this rework item's source path is absent. Searches of
quarantine find the one consumer above. The DAG parent
lem-sc-global-hom-base-change-counit-transport continues to use this node; nothing is
withdrawn. The scratch consumer and repaired dependency compiled together in import
order in 39.5 and 5.2 seconds, respectively; no warnings. The private equality has only
propext, Classical.choice, Quot.sound according to its separate print-axioms check.

## Status

landed 20261021T214830-L-1864636 2026-10-21 (merge of deliver/M2/Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange)
