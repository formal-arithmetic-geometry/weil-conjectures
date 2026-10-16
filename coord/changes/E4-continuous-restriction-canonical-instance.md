# AlgebraicGeometry.ProEtale.CondensedRing.continuousFieldSourceMonObj

## Reason

The upstream-sync return requests canonical source-ring instance selection before the field
restriction theorem, because conversion between two sheafification-based monoid structures
previously timed out in the kernel. The retained version selected its source `MonObj` only
inside the proof. Fix the canonical sheaf monoidal structure and source-ring `MonObj` before
the theorem statement is elaborated, in a section limited to that theorem.
No existing definition or statement changes mathematically. The new local instance directly
uses the existing source ring's canonical construction and introduces no assumption or choice.

## Old

The retained proof began with the following local binding, after its statement was elaborated:

```lean
  set_option linter.style.haveILetI false in
  letI : MonObj (Profinite.continuousMapRingObj E) :=
    Sheaf.monObj_sheafCompose_obj _ (Profinite.continuousMapRingSheaf E)
```

The current repository instead has the same field theorem signature with `:= by sorry`.

## New

The following section precedes the unchanged theorem signature and ends after its proof:

```lean
section FieldRestriction

attribute [local instance] Sheaf.monoidalCategory

noncomputable local instance continuousFieldSourceMonObj (E : Type) [NormedField E] :
    MonObj (Profinite.continuousMapRingObj.{u} E) :=
  Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf E)
```

The old proof-local source `MonObj` binding is removed. The source-ring construction is the
same canonical `Sheaf.monObj_sheafCompose_obj`; only its elaboration scope changes.
A scratch theorem with the exact repository signature, using default instances outside this
section, checks direct application of `continuousField_module_restriction`.

## Users

`tools/downstream.py --uses continuousField_module_restriction` lists the item and the lattice
module. The slice-freeness module is the other direct importer. Both direct importers compile
unchanged against fresh sandbox artifacts. None of the 24 transitive downstream modules needs
an adaptation: the original theorem type remains directly usable, no existing definition is
changed, and the new instances are local to the field-theorem section.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | E4 | Field theorem proved with canonical local coefficient instances; original signature checked. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Existing application compiles unchanged against the repaired theorem. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | F1 | Direct importer compiles unchanged; no lines adapted. |

## Status

landed 20261016T221608-L-1614404 2026-10-16 (merge of deliver/E4/Sheaf.Paper.ContinuousModuleEncodingRestriction)
