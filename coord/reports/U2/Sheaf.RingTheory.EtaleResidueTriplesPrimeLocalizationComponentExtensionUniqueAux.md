## What changed
Proved the target theorem by combining two strictly simpler intermediate declarations: existence of a compatible descended model and epimorphy of its map. Added imports for those declarations.

## Proved and sorry left
The target `etaleResidueTriples_primeLocalization_component_extension_unique_aux` is proved. The new declarations `etaleResidueTriples_primeLocalization_component_extension_compatible` and `etaleResidueTriples_primeLocalization_component_extension_epi` remain `sorry`, each with its own DAG node.

## No longer needed
The original auxiliary extension module was not needed by the final proof and is not imported.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan omitted the two independent descent and epimorphism substatements needed to combine into the target.

## New nodes
Added `new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible` and `new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi`.

## Earlier second reading (a previous round; superseded)
The target signature is unchanged and its proof combines the two strictly simpler statements. The new statements match their declarations and are true descent subclaims; the unit route is retained through the stated localization argument.

## Second reading by U2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`, while the two explicitly split declarations retain their named `sorry`s. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Read both split statements and their DAG nodes. The compatible statement is the target conclusion with epimorphy omitted; the epi statement supplies the final property for a compatible map. Their source, docstrings, and node metadata are present. Verdict: pass.
4. The proof follows the descended compatible model and then applies the epi result. The duplicate Epi import was removed. The unit `sk-prop-input-spreading` remains the unit recorded by the target and split nodes. Verdict: pass.
5. Updated the target node proof and `proof_deps` to name the two split nodes used by the Lean proof; no statement fields changed. Verdict: pass.

Changed the duplicate import, synchronized the target DAG proof metadata, and recorded this second reading.

## Second reading by U2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`, while the two explicitly split declarations retain their named `sorry`s. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Read both split statements and their DAG nodes. The compatible statement is the target conclusion with epimorphy omitted; the epi statement supplies the final property for a compatible map. Their source, docstrings, and node metadata are present. Verdict: pass.
4. The proof follows the descended compatible model and then applies the epi result. The duplicate Epi import was removed. The unit `sk-prop-input-spreading` remains the unit recorded by the target and split nodes. Verdict: pass.
5. Updated the target node proof and `proof_deps` to name the two split nodes used by the Lean proof; no statement fields changed. Verdict: pass.

Changed the duplicate import, synchronized the target DAG proof metadata, and recorded this second reading.
