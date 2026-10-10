# lem-sc-isogeny-facts

Files written: `dag/nodes/sec-abelian-varieties/lem-sc-isogeny-facts.json` (item, split), `dag/units/sk-prop-av-isogeny.json` (realized fields), and `citations.json`. No new nodes or Mathlib leaves.

Attachments: none. The four Lean declarations named by the item cover separate clauses and rest transitively on sorries in the recorded sorry map; `abelianVariety_estimate` also combines later torsion claims and rests on them.

WANTED: local Stacks Project checkout, Tags 0BFG (multiplication map), 03RP (abelian variety properties), and 0BEV (positive degree), for lem-sc-isogeny-facts. The repository has the tag index but not the Stacks source or the blueprint Markdown. The embedded `blueprint_proof_text` of the item and the unit record supplied the route; I marked the concise assembly proof as agent-written.

The imported proof was an unchecked list of dependencies and included the proof inputs of `lem-sc-mult-n-finite-flat` as though this item used them directly. The existing same-unit node states the substantive finite-flat, rank, and kernel-order result. I cite its statement and leave its Hilbert-degree calculation to its own split. The statement itself is unchanged. I added the definitions of isogeny and fppf covering to its statement dependencies. The unit's second step is realized by the finite-flat node and the final assembly here.

Nothing left unfinished in this one-level split. The cited `lem-sc-mult-n-finite-flat` remains unsplit, as expected for a dependency item.

## Not duplicates

No new nodes were created. `lem-sc-mult-n-finite-flat` is already in the DAG and is cited for its rank and kernel-order claims. `thm-av-final` contains this item as one clause but includes further etale torsion claims, so it is not recorded as an equivalent blueprint node.

## Review by H1

I read the item's embedded blueprint proof, the `sk-prop-av-isogeny` unit record, and the Lean statements and docstrings in `AbelianVariety/Isogeny.lean` lines 300-386. The local Stacks and blueprint source trees are absent, as noted above. The item restricts to an algebraically closed field; each cited isogeny and finite-flat statement holds over any field, so that specialization preserves every hypothesis. At `n=1`, the rank and kernel order are both one; at dimension zero the claimed order is also one. Neither case conflicts with the cited statements.

Step 1 reads `lem-sc-mult-n-isogeny` for surjectivity and a finite kernel, `def-sc-isogeny` for the criterion, and `def-sc-mult-n` for the identity of `A[n]` with the kernel. Those statements say exactly those things. The inference is a direct application of the definition.

Step 2 reads `lem-sc-mult-n-finite-flat` for finite flatness, rank `n^{2g}`, and kernel order `n^{2g}`; `lem-sc-isogeny-degree` identifies the finite flat rank with the degree of an isogeny. Both apply to the same positive `n` and the same abelian variety. The degree calculation is therefore a one-line comparison; no claim about the proof inside either cited node is used.

Step 3 uses the finite locally free assertion of `lem-sc-mult-n-finite-flat` and the surjectivity of `lem-sc-mult-n-isogeny`. Finite locally free implies locally finite presentation, and flatness of the finite kernel over a field follows from exactness of vector-space tensor products. The definition in `def-pc-fppf-site` gives the fppf covering condition for the singleton map. I checked these inferences at `n=1`, when the map is the identity cover.

I searched the DAG for the degree and fppf facts and checked the blueprint index. The needed finite-flat node already exists; the fppf site definition is a generic tool from another unit and is declared in `split_report.tool_uses`. The two Mathlib phrasings found only unrelated elliptic-curve and abstract-group results; the grep found no matching declaration, and LeanSearch returned a service error. There are no new-node checks under B1-B9. I removed the imported indirect proof dependencies, added the missing statement notions, and wrote exact citation quotes for every cited node.

## Second reading by H1

Step 1 checked against `lem-sc-mult-n-isogeny`, `def-sc-isogeny`, and `def-sc-mult-n`: the cited statements give surjectivity, finite kernel, the isogeny criterion, and the kernel identification; the short inference is elementary. Verdict: sound.

Step 2 checked against `lem-sc-mult-n-finite-flat` and `lem-sc-isogeny-degree`: their statements give finite flatness, rank and kernel order, and identify isogeny degree with finite-flat rank. The comparison is elementary once Step 1 supplies that `[n]` is an isogeny. Verdict: sound.

Step 3 checked against `lem-sc-mult-n-finite-flat`, `lem-sc-mult-n-isogeny`, and `def-pc-fppf-site`: finite locally free gives flatness and local finite presentation, the multiplication map is surjective, and the cited site definition supplies the fppf covering criterion. Flatness of a finite scheme over the field is elementary. Verdict: sound.

There are no new nodes, so B1-B7 and duplicate/Mathlib-leaf checks are vacuous. I checked the item statement against the embedded blueprint and the recorded Stacks tags, and tested the edge cases `n=1` and `g=0`; both give degree and kernel order one. The local Stacks `.tex` checkout is absent, so tag verification is limited to the source metadata and blueprint text already recorded.

Changes made in this second reading: none to node statements or citations; added this audit section to document the checks and the absence of new nodes.
