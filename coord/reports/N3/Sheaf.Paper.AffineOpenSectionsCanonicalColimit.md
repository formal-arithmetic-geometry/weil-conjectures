## What changed
Split the target proof into two strictly smaller intermediate theorems in new modules: construction of the canonical natural transformation and colimitness for a supplied transformation. The target now combines these theorems. All three modules compile.

## Proved and sorry left
The target theorem `affineOpenSections_exists_canonical_colimit` is proved from the two intermediate declarations. The new declarations `affineOpenSections_exists_canonical_transformation` and `affineOpenSections_canonical_colimit_core` remain `sorry`, each with its own DAG node.

## No longer needed
None; the original public imports remain required for the displayed statement and the intermediate statements.

## Where the brief, the DAG or earlier work was wrong
No existing Mathlib or library theorem supplies affine-site continuity for the supplied adjunction and fixed coefficient universe. The DAG plan therefore had to be split into the two intermediate statements above.

## New nodes
`affine-open-sections-canonical-transformation` and `affine-open-sections-canonical-colimit-core`, with corresponding modules under `lean/Sheaf/Paper/`.

## Earlier second reading (a previous round; superseded)
The target proof preserves the original signature and derives it by applying the two strictly smaller intermediate statements. Both new statements are true affine-continuity substeps and match their Lean signatures; the unit route is retained.

## Second reading by N3
1. I compared the delivered target module with the repository version.  The target
   declaration has the same signature byte for byte; only its proof and proof imports
   changed.  The two added declarations are new split statements and are recorded by
   matching DAG nodes.
2. I compiled all three modules with `lcompile.py --all`.  They compile without errors.
   The only remaining `sorry`s are the two named split theorems, and neither definition
   contains a `sorry`, `axiom`, `unsafe`, `opaque`, or other forbidden escape.
3. The transformation and colimit-core statements are true consequences required by
   the affine continuity argument and are strictly smaller than the target; their
   hypotheses and displayed component formula are unchanged from the target's route.
   No existing declaration with either statement was found in the library or Mathlib.
4. The proof uses both split declarations exactly once.  The target's original
   `LowerShriek.OpenImmersion.Defs` proof import is therefore replaced by the two
   intermediate proof imports; all three public imports remaining in each module are
   needed by its displayed types.
5. The unit route is retained: the target still proceeds through canonical
   transformation construction and then affine-site colimit continuity, as recorded by
   the unit and the two new nodes.

I changed the report to record this independent second reading.  No Lean statements,
definitions, or DAG statements were changed during this reading.
