# AlgebraicGeometry.Scheme.AdicStratificationTrivializationCompatibility

## Reason

The expanded normalization condition repeats module restriction, scalar restriction and
adjunction constructions in the final refinement. Kernel checking reached 150000 heartbeats
and 53.2 seconds without completing. Naming that identical condition once on abstract
sites makes the specialization and its proof share the same expression. All four modules
then compile cleanly in import order; the item takes 12.4 seconds. This is a definition
refactor: the original existential uniqueness, every binder, and the exact unit equation
are unchanged by unfolding the new definition. No target type changes, including its
elaborated type up to definitional equality; no mathematical interpretation changes.

The new public import of `Sheaf.AlgebraicGeometry.NormalizedLocalModulePullback` is needed
because the compatibility definition now uses its public predicate. The new generic
predicate belongs to the helper's existing new node. The helper theorem's conclusion is
the same equation expressed by this definition and its proof unfolds it immediately.

The saved work also changes `adicStratificationModelTopology` from an `abbrev` to a
`def` with exactly the same body and inferred type, so unification does not eagerly
expand the induced-topology construction. `adicModelDownContinuous` supplies its
continuity API. This changes reduction behavior only, not the topology or its meaning.
The local irreducibility attributes on this topology and `adicStratificationRho` apply
only inside this file. The standard ring/additive sheafification, local-bijection and
Kan-extension instances expose the existing generic constructions on the small models;
the finite-limit instances are private. None adds a mathematical assumption.

## Old

```lean
abbrev adicStratificationModelTopology (pro : Bool) (X : Scheme.{u}) :=
  (AsSmall.down : adicStratificationModel pro X ⥤ adicStratificationSite pro X).inducedTopology
    (adicStratificationTopology pro X)
```


```lean
def AdicStratificationTrivializationCompatibility
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S : Scheme.{u}}
    (h : T ⟶ S) (G : adicStratificationModules pro S R)
    (P : adicStratificationModules pro T R)
    (b : P ≅ (adicStratificationPullback pro R h).obj G)
    (V : adicStratificationModel pro S) (M : ModuleCat.{u + 1} R)
    (e : G.over V ≅ ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M).over V) : Prop :=
  ∃! d : P.over ((adicStratificationModelBaseChange pro h).obj V) ≅
      ((SheafOfModules.strictPerfectConstantSheaf
        (adicStratificationModelTopology pro T) R).obj M).over
          ((adicStratificationModelBaseChange pro h).obj V),
    ∀ (W : Over V) (x : G.val.obj (op W.left)),
      (d.hom.val.app (op ((Over.post (adicStratificationModelBaseChange pro h)).obj W)))
        ((b.inv.val.app (op ((adicStratificationModelBaseChange pro h).obj W.left)))
          ((((SheafOfModules.pullbackPushforwardAdjunction
            (adicStratificationRho pro R h)).unit.app G).val.app (op W.left)) x)) =
        (((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R h)).homEquiv
          _ _ (adicStratificationConstantMap pro R h M)).val.app (op W.left))
            ((e.hom.val.app (op W)) x)
```

## New

```lean
def adicStratificationModelTopology (pro : Bool) (X : Scheme.{u}) :=
  (AsSmall.down : adicStratificationModel pro X ⥤ adicStratificationSite pro X).inducedTopology
    (adicStratificationTopology pro X)
```


```lean
def AdicStratificationTrivializationCompatibility
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S : Scheme.{u}}
    (h : T ⟶ S) (G : adicStratificationModules pro S R)
    (P : adicStratificationModules pro T R)
    (b : P ≅ (adicStratificationPullback pro R h).obj G)
    (V : adicStratificationModel pro S) (M : ModuleCat.{u + 1} R)
    (e : G.over V ≅ ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M).over V) : Prop :=
  SheafOfModules.NormalizedLocalModuleTrivialization
    (adicStratificationModelTopology pro S) (adicStratificationModelTopology pro T)
    (adicStratificationModelBaseChange pro h) (adicStratificationRho pro R h)
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M) G
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro T) R).obj M) P
    (adicStratificationConstantMap pro R h M) b V e
```

`SheafOfModules.NormalizedLocalModuleTrivialization` expands to precisely the old
existential uniqueness and pointwise normalization equation, with the indicated parameters.
All existing public signatures and visibility are identical. The ring/additive
sheafification and Kan-extension instances added in the item name the existing generic
constructions; they add no hypotheses and choose no arbitrary witnesses.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback
--uses AdicStratificationTrivializationCompatibility` reports 341 transitive downstream
modules and only one module with a direct use of this definition: the item itself.
The corresponding `--uses adicStratificationModelTopology` audit likewise reports
only this item as a direct user (48 uses). A later snapshot has 342 transitive importers;
the direct-user set is unchanged. The transitive importers need no adaptation because the refactored definition is
definitionally equal to its old body. No other held module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback | M5 | Definition refactor and completed proof; public import of the shared predicate. |
| Sheaf.AlgebraicGeometry.NormalizedLocalModulePullback | new in this delivery, M5 | Define the shared condition and prove its normalized transport theorem. |
| Sheaf.AlgebraicGeometry.FiniteTypeConstantModulePullback | new in this delivery, M5 | The existing proof applies the generic theorem and unfolds its shared condition definitionally. |

## Status

landed 20261020T131144-L-1250594 2026-10-20 (merge of deliver/M5/Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback)
