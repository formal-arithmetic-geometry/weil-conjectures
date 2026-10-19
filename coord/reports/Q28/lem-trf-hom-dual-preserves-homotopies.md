# Stage-1 report: lem-trf-hom-dual-preserves-homotopies

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-hom-dual-preserves-homotopies.json`: split statement; no new nodes and therefore no Mathlib leaves.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carries the item, and no exact declaration was found by keyword or blueprint-tag search.

## WANTED

None.

## Not duplicates

No auxiliary node was created. The whole-DAG and blueprint searches found no existing node stating the precomposition homotopy formula; the existing `def-sc-module-total-hom-complex` is only the definition of the Hom complex and is a dependency, not a duplicate.

## Review by Q28

I read the item node and the chapter/unit records (`sec-trace-formula` and `sk-p-trace`), the source proof `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-p-trace/sk-p-trace.proof.md`, and the statements of both dependencies `def-weil-abstract-derived-category` and `def-sc-module-total-hom-complex`. I searched the slopmaster2 source for the item id, its mathematical keywords, and blueprint tags; no finished declaration exists. I also ran LeanFinder, Loogle, grep, and LeanSearch searches for total-Hom precomposition and homotopy preservation; Mathlib returned generic `Homotopy.compLeft`/`compRight` and `CochainComplex.HomComplex.δ_ofHomotopy`, but no exact statement for this signed module-valued total-Hom formula, so the item remains a project lemma.

Step 1 uses exactly the total-Hom differential and the definition of a chain map; expanding $D(\\varphi f)$ and using $d_Rf=fd_P$ gives $(D\\varphi)f$. Step 2 uses only composition of component maps, checking identity and contravariant composition pointwise. Step 3 uses the same differential formula and the homotopy equation $f-f'=d_Rh+hd_P$; I expanded both $DS_h$ and $S_hD$, checked the signs in degrees $j$ and $j-1$, and verified cancellation of the $d_T$ terms. Steps 4 and 5 are direct specializations and applications of the already established identities. I checked edge cases including $h=0$, $f=f'$, zero complexes, and characteristic two (where the displayed signs still agree because $-1=1$). Every cited node says exactly the differential or chain-map property quoted in `citations.json`; `proof_deps` is the union of the step uses. No hypothesis or coefficient category was changed, no SGA source was used, and no long step hides a separate lemma.
