## What changed

Added a complete combining proof for `finiteEtale_powerSeries_punctured_section_fully_faithful`.
The target now reduces bijectivity to separately named injectivity and surjectivity statements.
Added proof-only imports and two modules carrying those intermediate statements.
The intermediate modules retain proof-plan imports of Hartogs and the flat local depth formula.

## Proved and sorry left

Closed one original hole: `finiteEtale_powerSeries_punctured_section_fully_faithful`.
Added two holes, listed below. This is a decomposition, not an axiom-free proof of the target.
The parent signature is unchanged, and its complete combining proof uses both strict components.
The following strictly simpler intermediate obligations remain as named `sorry`s:

- `finiteEtale_powerSeries_punctured_section_restriction_injective` (node `lem-sbc-power-series-punctured-section-injective`).
- `finiteEtale_powerSeries_punctured_section_restriction_surjective` (node `lem-sbc-power-series-punctured-section-surjective`).

## No longer needed

Removed the unused proof-only imports `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`
and `Sheaf.RingTheory.FlatLocalDepthFormula` from the parent module. Its combining proof no longer
uses nodes `lem-sbc-depth-two-hartogs-restriction` and `lem-weil-pbc-flat-local-depth-formula` directly.
Their mathematics remains part of the proof plans for the split obligations, whose nodes cite
both dependencies and whose modules import them privately. No module is globally pruned.
The former dependencies are replaced at the parent by the two component nodes.
The net hole change of this delivery is 1 closed minus 2 added = -1; no ledger progress is claimed.

## Where the brief, the DAG or earlier work was wrong

The imported DAG proof combines four substantial arguments in one hole. The Lean target can be
cleanly reduced to the two independent hom-set properties above; no statement was weakened.

## New nodes

`lem-sbc-power-series-punctured-section-injective` and
`lem-sbc-power-series-punctured-section-surjective` record the two strict sub-obligations.


## Second reading by G2

1. Interface: PASS. Read the diff of the existing module against the repository. Its only
   changes are two private imports and the proof body. Compared the entire existing theorem
   signature byte for byte, including the let-bound zero-section map, all ring instances,
   hdepth, positive d, hV, and the quantified arbitrary finite etale P and Q: unchanged.
   No definition, target statement, visibility, or unrelated module is changed. No change
   record is required.
2. Proof and trust: PASS as a decomposition. All three delivered modules compile locally
   in import order. The parent combines injectivity and surjectivity of precisely the same
   pullback hom map. The only local sorries are the two named component theorems in the
   report. No definition is introduced, no arbitrary existence witness is chosen, and the
   forbidden-declaration scan passes. Scratch copies with #print axioms check every delivered
   declaration: each lists exactly propext, Classical.choice, Quot.sound, and sorryAx.
   Thus no forbidden axiom occurs; sorryAx remains because the component statements are open.
3. Split obligations: PASS. Read Stacks 0EY9 (Lemma 58.26.1), 0EKP (Lemma 52.15.1), and
   0EL8 (Lemma 58.17.1). Both new statements have exactly the source's Noetherian local,
   depth at least two, positive-variable, and punctured-zero-section hypotheses, and each
   states only one hom-set property. Neither is a renamed bijectivity theorem. Their
   docstrings include the formal-section comparison and the respective uniqueness/lifting
   arguments. In the associated-prime argument, the fibre is a localization of the domain
   (A/p)[[x]], so fibre depth zero forces the zero prime; pB then specializes to pB+I.
   Krull intersection is applied only at points on the zero section, where I is in the
   local maximal ideal. The quasi-affine Noetherian open is quasi-compact, so finite global
   generation of the dual bundles supplies the universally exact presentations used in
   the comparison. The tensor-square and unit comparisons ensure that the lifted module
   map is an algebra map. Empty source/target covers and variable ranks cause no exception:
   zero bundles are included. Tested the standard depth-two base k[[s,t]], d=1, and split
   covers; the hom maps reduce to ordinary maps of finite sets. The field/Artinian-base
   cases are excluded by hdepth, and d=0 is excluded by hd, exactly as in the source.
   Searched with different words using msearch LeanFinder, Loogle, grep, and LeanSearch
   (unavailable), and rg on both repository roots and the upstream AlgebraicGeometry tree.
   The formal-etale search hits do not provide the required comparison; occurrences of
   0EY9 elsewhere are users of this item, not independent proofs. No quick closure found.
4. Route and pruning: PASS. Read the old two proof dependencies' declarations. They provide
   Hartogs and a flat-local depth formula, not a direct hom-map completion theorem. The
   new statements retain their use in the formal-section comparison. The old dependencies
   are both listed under No longer needed as direct parent dependencies; they remain
   transitively imported and are not claimed as globally pruned. The four public imports
   supply the signature, and the component/dependency imports are private. Read
   dag/units/sk-prop-input-spreading.json: its realized arrays are empty; no designated
   realization was removed. Its depth-two formal splitting step still uses this item and
   the same Hartogs/completion/formal-etaleness route.
5. Nodes: PASS after repair. Matched all three lean.statement fields verbatim to their Lean
   signatures. The parent proof/proof_deps names precisely the two component theorems.
   Corrected its proof_origin to record this reduction. The new nodes have matching module,
   file, declaration, source, proof, creation, chapter and unit fields. Corrected their
   proof_deps and first-step uses to cite both old mathematical inputs, and their blueprint
   provenance to the existing spreading theorem ancestor through this item's route.
   Replaced the generic search records with queries actually run during this reading,
   preserving the unavailable-service result.

Changes in this reading: repaired the split nodes' dependency and blueprint records and
search evidence; added their private proof-plan imports and module blueprint tags; corrected
parent proof provenance; clarified the report's net hole count and absence of global pruning.
No theorem statement or proof term was changed.
