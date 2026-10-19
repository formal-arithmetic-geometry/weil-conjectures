## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-etale-completed-local-ring-iso.json`: item, split into seven steps; not a Mathlib leaf.
- `citations.json`: sixteen entries, one for each step/cited-node pair, quoting the cited statements verbatim.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. I searched the read-only slopmaster2 `WeilConjectures/` and `Comparator/` for the exact item id and searched `WeilConjectures/` for completed-local-ring, completion/etale, and local-ring-isomorphism language. I also checked `dag/lean_names_upstream.json`. No project declaration states the item, including both alternative residue-field hypotheses and all three conclusions. The upstream master checkout was inspected only as reference, not as evidence of a finished proof. The item has no recorded Lean audit to resolve.

WANTED: none. All sources used are present in the Stacks checkout.

The item statement is correct and is preserved verbatim. Its source note mentions 02GL for the residue-field input; the existing stronger local unramified criterion 02GF gives the finite separable extension together with the maximal-ideal equality needed by 0AGX, so the proof uses that node directly. The source's completion argument in Curves 0C57 is expanded to check Noetherianity and both structural residue-field cases. No hypothesis, conclusion, coefficient category, or base-change map was changed. In particular, neither global finite type nor separatedness is added. Nothing remains unfinished.

The node is an auxiliary created node, not the statement node of `sk-i-curve-zero`, so no unit realization file is changed. I read that unit and the trace-formula chapter: the unit now uses contracting correspondences, while this node's recorded ancestry explicitly describes its historical semistable auxiliary branch. This delivery proves the assigned local tool and makes no change to that route or to its historical provenance.

## Sources and searches

I read Curves Tag 0C57 (`lemma-node-etale-local`) and its explicit invocation of the completed-local-ring comparison. I checked the exact statements of Morphisms 02GF (`lemma-unramified-at-point`, equivalence (1)/(6)), 02GL (`lemma-etale-over-field`), 01TE (`lemma-algebraic-residue-field-extension-closed-point-fibre`), 01T6 (`lemma-finite-type-noetherian`), and More on Algebra 0AGX (`lemma-flat-unramified`). I also read Etale 039M and its following residue-degree remark, Fields 09GQ/09GR, Algebra 00FN, and Schemes 01HV. Tags were checked against `literature/stacks-project/tags/tags`.

DAG searches covered 02GL, 01TE, 0AGX, 039M, residue fields, maximal ideals, local Noetherianity, and affine-stalk localization. These found all the necessary inputs. Whole-blueprint searches with `tools/blueprint_refs.py` for `etale completed local ring residue field algebraically closed`, `completed local`, and `02GF`, and text searches of the current blueprint found no blueprint node stating the complete item in another form. The item's `same_as` is therefore `[]`.

The inherited Mathlib search entries were retained. Six new searches were actually run through `msearch.py`; their exact queries and digests are in `searches.jsonl` and were appended to the item's records. They include LeanFinder on the scheme statement and a second phrasing on the general flat-local completion theorem, LeanSearch on the etale completion theorem, Loogle `AdicCompletion, RingEquiv`, and two Mathlib greps. All services answered. The hits provide etale/formally unramified interfaces, residue-field isomorphisms for open immersions, completion flatness (`AdicCompletion.flat_of_isNoetherian`), or congruences from an already given equivalence. These do not state the item. I read `AdicCompletion/LocalRing.lean` (in particular residue-field invariance at lines 151–154) and `AsTensorProduct.lean` (flatness at line 379); neither supplies the missing scheme-level comparison. No new node needs a separate search record.

## Not duplicates

No new nodes were created. Existing nodes were reused, including the actual-local-map unramified criterion and the generic flat-local completion theorem, rather than restating either of them under a new id.

## Review by Q69

I reviewed the seven steps with the cited node statements open, against the Stacks sources just listed. The source statement is valid: the maps to residue fields are the structural k-algebra maps. Merely abstract isomorphisms with k would not justify the second case, and I checked that the item explicitly requires structural isomorphisms.

Step 1 uses exactly the definitions `def-weil-etale-morphism`, `def-weil-unramified-morphism`, and `def-weil-flat-morphism`. The first gives flatness and unramifiedness; the second includes local finite type; the third explicitly says that the stalk map is a flat local homomorphism. These are elementary unpackings. No unsupported passage from an affine map to a stalk map is made.

Step 2 uses the statement of `lem-trf-unramified-maximal-ideal-residue-criterion`, whose clause (ii) specifies both the generated-maximal-ideal equality for the actual stalk homomorphism and the finite separable algebraic residue extension. The hypothesis of local finite type is Step 1. Its clause (i) applies with the whole open D, because e is unramified. This removes the need to identify the residue field of a fibre point with the original residue field through an uncited comparison.

Step 3 uses `def-weil-residue-field` to identify the induced quotient maps and `lem-weil-pbc-algebraic-over-algebraically-closed-subfield` only for its precise elementwise assertion that an algebraic element lies in the image of the algebraically closed subfield. In the kappa(x) case Step 2 gives algebraicity over k after composing with the structural isomorphism; hence every element lies in j(k), proving surjectivity. In the kappa(y) case I wrote the preimage argument with alpha injective explicitly; it needs no finite-generation assumption and does not assume that x was already closed. The map alpha, rather than a chosen field automorphism, is proved invertible.

Step 4 uses `lem-trf-finite-residue-point-closed-in-fibre` with the given locally finite type morphism C to Spec k and the degree-one residue extension from Step 3. Its statement says closed in the fibre, not closed in C; the latter follows because `def-weil-affine-spectrum` says that Spec k has one point and `def-pc-scheme-fibre` explicitly gives the homeomorphism onto the set-theoretic fibre, which here is all of C. I checked these clauses directly.

Step 5 applies the same finite-residue node to e, with local finite type from Step 1 and finite residue extension from Step 2. The fibre homeomorphism is again exactly in `def-pc-scheme-fibre`. The additional topology is written out: e inverse image of the closed singleton x is closed, and a point closed in that subspace is closed in D. No assertion that etale morphisms are closed is used.

Step 6 uses `pqf-def-locnoeth` for its defining existence of an affine cover by Noetherian rings. Spec k has such a cover since a field has only the two finitely generated ideals. `pqf-lem-locnoeth-lft` states precisely the local-finite-type permanence theorem; it applies first to C over Spec k and then to D over C. No composition theorem requiring quasi-compactness is used. I then choose members of those covers containing x and y. Clause (c) of `lem-weil-pbc-affine-open-stalk-localization` states the three localization properties for the actual germ map, exactly the hypotheses of `lem-weil-pbc-localization-noetherian`. Thus A and B are Noetherian. I corrected my initial possible shortcut of citing finite generation of the stalk maximal ideal: that weaker existing node would not say that the stalk ring is Noetherian, so it is not cited.

Step 7 uses only `lem-weil-pbc-flat-local-completion-iso`, whose statement is exactly the general commutative-algebra comparison, not the assigned geometric item. Every hypothesis is now verified: A and B are Noetherian local rings by Step 6, the actual map is flat and local by Step 1, maximal ideals agree after extension by Step 2, and the actual residue map is invertible by Step 3. Its statement specifies the componentwise inverse-limit map and its compatibility with the original ring map, so the result concerns the map in the item, not just the existence of some isomorphism of completed rings. This is the generic off-unit tool used by the source 0C57 itself; it is declared in `split_report.tool_uses`. No node in the curve unit supplies this commutative-algebra statement.

B–E checks: no unsplit new node carries a disguised proof because there are no new nodes. No new lemma restates a clause of the item. All non-elementary inputs above are cited statements, not facts extracted from their proofs. The sixteen quotes in `citations.json` are exact copies of those statements. The local dependency traversal has 132 nodes and does not reach this item; no cycle was introduced. The proof-dependency list is exactly the union of the uses. All seven steps are shorter than 2000 characters (the longest is 840), and none hides a separate comparison lemma: the required comparisons are the cited fibre homeomorphism, cited stalk localization, and cited componentwise completion map. No SGA source is used.

Small cases checked: the identity morphism and an open immersion give the expected identical stalks and completions. A point y in an empty source is impossible, so no empty-source exception is needed. Disconnected and non-quasi-compact locally finite type schemes are covered because all Noetherian arguments are local; non-separated schemes also satisfy the topology used. Nonreduced schemes cause no problem since reducedness is never used. In positive characteristic the argument needs algebraicity rather than separability alone for the algebraically closed field input, and Step 2 supplies it. The second residue-field case is tested on an arbitrary tower k to F to k with structural composite an isomorphism: the explicit injectivity argument forces F=k. Dropping algebraic closedness would allow a finite separable residue extension in the first case, explaining why that hypothesis is used.

## Validation

The required `deliver.py Q69 lem-trf-etale-completed-local-ring-iso --no-push` exited 0 and printed `OK (not pushed)` at dad1329471: server preflight passed, including the required DAG and split checks. No diagnostic required a repair. No Lean was written and no compiler, Lake, or build tool was run.
