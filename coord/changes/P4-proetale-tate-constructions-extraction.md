# AlgebraicGeometry.ProEtale.spTwists_commonCover

## Reason

The common-cover proof needs separate one-slice integral/rational and algebraic-closure
basis lemmas. Their statements refer to the existing constructed twists. Keeping their
constructions in the common-cover module would create an import cycle, so the definitions
and already proved auxiliary theorems are extracted verbatim into a lower module.
This extraction is for the proof dependency graph, not a change of mathematical objects.
The original item was restored from its recorded quarantine archive; no archive is deleted.

## Old

The original module physically declared all constructions and proved transition lemmas
before `spTwists_commonCover`. For example, verbatim:

```lean
def spIntegralTwist (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  limit (spIntegralTwistSystem X ℓ E)
```

## New

The identical declarations (names, signatures, bodies, instances and docstrings) are in
`Sheaf.Paper.ProEtaleTateTwistLevels` (finite levels and integral/rational objects)
and `Sheaf.Paper.ProEtaleTateTwistConstructions` (field maps, colimit and signed twists).
The item retains every original public import
and publicly imports the construction module. The example above is literally unchanged.
Only `spTwists_commonCover` and `spTwists_locallyFree` remain physically in the item.
The former now selects the existing finite common-root cover, proves the finite coefficient
clause, and applies the two single-slice lemmas. The latter's proof is unchanged.
No existing declaration changes its type, visibility, mathematical data or public attributes.
Both construction files retain the original local attributes at the phases where they
were in force. The upper construction file privately imports the lower file with
`import all` to reuse the already proved private tensor-linearity helper; that helper
is used only in theorem proofs. The lower files use the finite theorem module directly
instead of the aggregate `TateTwistLocallyFree`, still publicly imported by the item.
Profiling the one-file extraction found distributed instance/elaboration work rather
than one large slow declaration. The finite-level portion is therefore separated at
the existing boundary before field-extension maps. All mathematical data bodies and
exported reducibility remain unchanged.
The node attachments of moved declarations are updated to their physical owning module.
The two new proof modules import only the lower construction module, avoiding a cycle.

## Users

Direct importers, including those recorded in quarantine, retain exactly the same API:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CartesianCoefficients | unclaimed; not edited | All names and objects re-exported identically. |
| Sheaf.Paper.DiagonalTowerSystemInterface | unclaimed; not edited | Same finite/integral twist systems and maps. |
| Sheaf.Paper.NativeIntegralTateFiniteRepresentation | unclaimed; not edited | Same finite levels and transition formulas. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed; not edited | Same integral inverse system and limit. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed; not edited | Same coefficient lines and derived tensor input. |
| Sheaf.Paper.PurityConventions | unclaimed; not edited | Same signed twist definitions. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed; not edited | Same local freeness theorem and constructions. |

All transitive users, including the fixed targets, have the same definitions and signatures.
There are no forced adaptations and no target statement or definition-meaning change.
All seven direct importers compiled unchanged against the extraction through
`lcompile.py` (exit code zero). Their temporary copies were removed before delivery.

## Status

landed 20261026T200332-L-3306344 2026-10-26 (merge of deliver/P4/Sheaf.Paper.ProEtaleTateTwists)
