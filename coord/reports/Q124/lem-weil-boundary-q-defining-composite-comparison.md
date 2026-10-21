## Files written

- `dag/nodes/sec-six-functors/lem-weil-boundary-q-defining-composite-comparison.json`: statement item, now split into five steps; no Mathlib match for the full composite identity.
- `citations.json`: eight step/node entries, each quoting verbatim the statement used.
- New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, and of the six-functor/category-theory sources for untransposed composites and inverse-projection comparisons, found no project declaration stating this item. The open-immersion inverse-projection associativity/unitality declarations do not state its etale/pro-etale comparison identity. No upstream declaration containing `sorry` was counted as finished.

## WANTED

None. The source comparison paragraph and the Stacks constructions used below are present locally.

## Changes and issues

The original item had an empty proof. Its statement and all seven statement dependencies are retained exactly; its existing source, provenance, and Mathlib search records are preserved. The new proof supplies the calculation promised by the source place. In particular it distinguishes the two tensor orders in `r` and `s`, and uses naturality of the given comparison at the source symmetry, instead of silently identifying the two orders.

There is no statement dispute. The positive boundedness of the inputs is not used to assert positive boundedness of their derived tensor product. All maps are calculated in the ambient unbounded derived categories. Invertibility of only the displayed projection components is used, exactly as assumed.

The original tensor-pullback node states bifunctoriality but does not state preservation of symmetry. I therefore cite the existing `lem-sfb-ringed-derived-monoidal-comparisons` for that additional assertion, and `lem-sf-ringed-derived-closed-symmetric-monoidal` for naturality of the actual native signed braiding on both sites. Neither extra claim is extracted from the proof of a cited node. The three citations are declared generic tool uses in `split_report.tool_uses`.

## Mathlib and duplicate searches

I searched the whole DAG by tensor comparison, symmetry, braiding, inverse image, and projection-comparison terminology, and used `tools/blueprint_refs.py ancestor` and its whole-blueprint searches for `symmetr`, `projection-inverse`, `untransposed`, and `projection.*comparison`. The exact latter three searches had no blueprint matches; the symmetry search exposed existing general tensor-calculus nodes. The existing general ringed-site results suffice, so no new node is justified.

The item was searched through the required `msearch.py` command with LeanFinder (two independent phrasings), Loogle, LeanSearch, and a Mathlib grep. Their exact queries and actual returned names are in `searches.jsonl` and appended to `mathlib_searches`. All five calls succeeded. The LeanFinder queries returned braided naturality identities; Loogle returned braided-functor constructor/faithful transport; LeanSearch returned monoidal structure transport and tensor isomorphisms. I read `Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean` at lines 121-139 and 535-538 to check the relevant naturality and braided-functor equations. These are constituents of the proof, not a declaration stating the composite comparison or a one-line specialization giving it.

## Not duplicates

No new nodes. Reused the existing general statements rather than creating a special-purpose symmetry or inverse-square lemma.

## Review by Q124

I read the item's source, `main-20261015/blueprint/sec-six-functors/sk-thm-sf-pf-proetale/thm-sf-pf-proetale.proof.md`, especially the sentence saying that comparison identifies projection maps. I also read the ancestor's proof in the master `cor-weil-boundary-duality-discharge.md` and the current `main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md`. Its final paragraph motivates this calculation before transposing. This split does not invoke exceptional adjunction or the ancestor as a lemma. I read Stacks `sites-cohomology.tex`, Tag 07A4, label `lemma-pullback-tensor-product`, including the K-flat total-complex construction, and Tag 0FPT, label `lemma-symmetric-monoidal-derived`. The latter omits its proof; I have not treated that omission as an elementary proof of cross-functor coherence. I use the existing node that explicitly states that coherence. The overall proof is marked agent-written, since the displayed cancellation is an expansion rather than a verbatim source proof. There are no new nodes needing separate sources.

For step 1, I opened the statements of all three cited nodes. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` gives the canonical comparison natural simultaneously in both inputs; `lem-sfb-ringed-derived-monoidal-comparisons` explicitly makes those same canonical comparisons symmetric strong monoidal; `lem-sf-ringed-derived-closed-symmetric-monoidal` explicitly gives the native signed symmetry and its naturality on any small ringed site. The relevant topoi have constant commutative coefficients, and the exact module inverse image in the item computes its derived functor termwise. All three apply to unbounded objects with the usual larger-universe small site representatives. None requires properness or finite Tor amplitude.

For step 2, the two cited symmetry statements give exactly the two equalities needed: comparison commutes with signed swap, and swap is natural in `rho_M^{-1}` and `v`. I wrote the equation `r C_Z(sigma_e) = sigma_p s` in full and then used the given naturality of `eta`. The cancellation of `F_p(r^{-1}) F_p(r)` is ordinary functoriality; the resulting input identity has source `F_p C_Z(i_e^*M tensor B)` and target `C F_e(B tensor i_e^*M)`.

Step 3 has no external citation because it multiplies the projection square that is an explicit hypothesis by specified inverses. I checked the types of `V`, `d`, `H`, and `k`, including the direction of `d : F_p B' -> C F_e B`. This produces the inverse-projection identity with `d tensor 1` on its right, which is the factor cancelled later. No general projection-formula theorem or unassumed invertibility is imported.

For step 4, I again opened the same three cited statements and checked that their bifunctoriality, braiding compatibility and braiding naturality say exactly what the step uses. The equation `a_p = C(a_e)d` follows by composing the stipulated arrow compatibility with `F_p(v)^{-1}`. The displayed output identity puts `d^{-1} tensor 1` directly before `k`, matching step 3; this is not an unproved assertion that comparison preserves a final arrow.

Step 5 substitutes these three explicitly proved identities and cancels the adjacent inverse tensor maps. It cites no new fact. Its last formula is the item's full conclusion with the correct source component of `eta`. These elementary steps are applications of cited structure, the hypotheses, and composition/inverse laws; none conceals a separate geometric or homological lemma. Every step is shorter than 2000 characters.

I checked the B-E return criteria against the actual JSON: no new notion, clause-copy, hidden source theorem, orphan citation, plain-text replacement of mathematical formulas, or new-node duplicate. `citations.json` was checked against the verbatim statements, not paraphrases. A read-only traversal of both statement and proof dependencies confirmed that none of the three tools reaches this item. The unit route is unchanged: this is the formal pre-adjunction calculation serving the boundary pairing comparison.

Small cases: if all comparison functors and comparison arrows are identities, the projection-square hypothesis identifies the two projection components and the formula reduces to their identical composites. If `v` or `eta_B` is nontrivial, the explicit `d` and its inverse cancel in the correct order; neither is implicitly set to identity. If `a_e` is zero, the assumed compatibility forces `a_p` to be zero because `F_p(v)` is invertible, so both composites vanish. Zero input objects also give zero composites. For odd-degree factors the signed swap is retained on both sites, and the cited braid compatibility already includes the Koszul sign, so the proof does not discard it. No regularity of the finite coefficient ring or bounded tensor amplitude was used.

## Unfinished work

None in this one-level split. No Lean files were written and no compiler or build tool was run. Delivery validation is recorded below after the required server dry run.

## Delivery validation

The required `deliver.py Q124 lem-weil-boundary-q-defining-composite-comparison --no-push` exited successfully: `OK (not pushed)` at `794f37a06a8`, server preflight passed. It ran the server checks; none of the prohibited local DAG/preflight scripts was run. The only subsequent edit before pushing is this validation record.
