## What changed

The target theorem now combines two strictly simpler intermediate statements: existence of a single fibre-flat stage and persistence of fibre flatness along a transition. Their proofs remain named `sorry` obligations for follow-up workers. Added imports for the two intermediate modules.

## Proved and sorry left

The target declaration `Module.NoetherianLocalModelTower.eventually_fiberFlat` is proved by applying the two intermediate results. The delivery adds the named sorries `Module.NoetherianLocalModelTower.exists_fiberFlat_stage` and `Module.NoetherianLocalModelTower.fiberFlat_of_le`, with DAG nodes of the same names.

## No longer needed

The original proof-only imports `Sheaf.RingTheory.ColimitEventuallyFlat` and
`Sheaf.RingTheory.Flat.LocalizationPreservesFlatness` are no longer used by the reduction;
the follow-up proofs of the split statements will import what they need themselves.

## Where the brief, the DAG or earlier work was wrong

The full quotient-system construction in the DAG was too large to complete in this worker window; it has been decomposed into its existence and persistence components without changing the target statement or the unit route.

## New nodes

`lem-weil-pbc-noetherian-local-model-tower-fiber-flat-stage` records the existence component.
`lem-weil-pbc-noetherian-local-model-tower-fiber-flat-persistence` records the persistence component.

## Second reading by K3

1. Compared the delivered target module with the repository version. The target signature and all
   existing declaration signatures are unchanged; only its proof and proof-only imports differ.
   Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. There are no errors, forbidden
   declarations, or unlisted `sorry`s; the two split theorems are the only remaining holes.
   Verdict: pass.
3. Read both split statements and their nodes. They are strictly smaller existence and persistence
   components of the target, with source and natural-language proof sketches. Verdict: pass.
4. Checked the target proof against its imports and the unit route. It applies exactly the existence
   and persistence components, preserving the unit's two-step route. Verdict: pass.
5. Checked DAG ownership fields and proof dependencies against the delivered declarations. The new
   nodes record the split declarations, and the target node records the reduction. Verdict: pass.

Changed during second reading: removed two obsolete proof-only imports from the target module and
documented them under `No longer needed`.
