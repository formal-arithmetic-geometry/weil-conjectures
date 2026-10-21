## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-zero-dimensional-affine.json`: statement, split into six proof steps; no Mathlib match for the full generality.
- `citations.json`: nine entries, each quoting the cited node's statement verbatim.
- `searches.jsonl`: actual searches made with the required msearch.py command.

Attachments: none. Searched `lean/WeilConjectures/` by the exact blueprint tag and by zero-dimensional, dimension-zero and T1/affineness notions. The project's zero-dimensional cohomology and base-change results concern finite-type schemes over fields; none states this arbitrary qcqs scheme theorem. The imported item has no Lean declaration to audit.

WANTED: none. All sources used are in the read-only repository.

The statement was correct and remains verbatim: every point is closed, quasi-compactness and quasi-separatedness are assumed, and neither Noetherianity nor finite type is assumed. The proof was absent. The split proves that the finite affine charts are closed and uses the existing finite affine closed-cover theorem to conclude. This is a node-level completion of the affine-chart proof of Stacks 0CKV, using the general tool 09NL for its last inference. It changes no unit statement or unit route. The proof is marked agent-written because its final assembly combines these two source proofs rather than reproducing 0CKV's final disjoint-partition induction.

Nothing mathematical remains unfinished in this split. The server checks and delivery are performed after this report is written.

## New nodes

None; zero new Mathlib leaves. Every non-elementary tool already has a node. In particular I did not create a node for the closed-point/maximal-ideal observation or the compact-subset closedness argument: each is a short argument from cited statements and definitions and appears explicitly in the proof steps.

## Searches and blueprint position

The full item's semantic searches were:

- LeanFinder: `A quasi compact quasi separated scheme whose points are closed is affine without Noetherian assumptions`.
- LeanSearch: `A quasi compact quasi separated zero dimensional scheme is affine`.
- Loogle: `AlgebraicGeometry.IsAffine, T1Space`.
- grep in AlgebraicGeometry: `topologicalKrullDim.*[Ii]sAffine|[Ii]sAffine.*topologicalKrullDim|[Ii]sAffine.*T1Space|T1Space.*[Ii]sAffine`.
- Second LeanFinder phrasing: `A quasi separated scheme with T1 topology has affine compact open subschemes`.
- grep in AlgebraicGeometry/Limits.lean: `T1Space|topologicalKrullDim|DiscreteTopology`.

Read the hits, including Mathlib's finite/discrete affineness instance at `AlgebraicGeometry/Limits.lean:700-705`, and the finite affine-cover theorem at `AlgebraicGeometry/Morphisms/QuasiCompact.lean:85-89`. Finite/discrete affineness does not cover infinite profinite spectra, and the returned quasi-separatedness and quasi-affine criteria do not state this item. All six searches succeeded. The original item's earlier searches are retained, with this session's actual log records appended.

I also ran LeanFinder, LeanSearch, Loogle and grep on the closed-singleton/maximal-ideal criterion, and read `PrimeSpectrum.isClosed_singleton_iff_isMaximal` at `RingTheory/Spectrum/Prime/Topology.lean:176-184`. It is an exact Mathlib fact, but no node is created: step 2 instead gives its needed direction in a few lines using the existing maximal-ideal existence node. These additional searches remain in searches.jsonl and are not misrepresented as negative searches for the item.

Searched the full DAG by 0CKV, 04MG, 01I5, closed affine covers, clopen affineness, closed-image immersions, and their declarations. Searched all imported blueprint nodes with blueprint_refs.py for dimension-zero affineness, zero-dimensional, quasi-separated, clopen affine, closed immersion affine, closed maximal, 04MG, and 09NL. No imported blueprint statement matches this item. The Noetherian zero-dimensional affine lemma is strictly more restrictive; it cannot be used here. The existing general closed affine-cover and zero-dimensional spectrum nodes are reused, not duplicated.

`blueprint_refs.py ancestor` returns null for this item: the inherited created.item chain has no mechanically recognized imported ancestor. I preserved that null and its via chain, filled the place precisely, and recorded the actual mathematical connection: Paragraph (3) of lem-sfb-field-profinite-galois-site needs affineness of qcqs field-site objects, below the ordinary direct-image clause of det-thm-sf-ctf-stability-direct-images. The item's chapter and unit metadata are left unchanged, even though the inherited unit record belongs to the older six-functors chapter. No unit realization fields are applicable to this auxiliary lemma.

## Review by NR

I read Properties Tag 0CKV, `lemma-dimension-zero`, in properties.tex, including the full proof and final assertion. Its quasi-separatedness hypothesis is essential to the overlap argument, and its final affineness assertion has only the extra quasi-compactness hypothesis. Its mention of dimension zero allows arbitrary rings; there is no Noetherian or finite-type restriction to import. The item's use of dimension at most zero additionally includes the empty scheme and is faithful to that assertion. The primary hypothesis used in the proof is explicitly that every singleton is closed.

Step 1 uses the statement of lem-pqf-finite-affine-cover-qc-open, which gives a finite affine cover of any quasi-compact open of any scheme. I apply it to the whole open of X; the hypothesis is the given quasi-compactness. Restriction of closed singletons to the charts is a subspace-topology identity, not a new geometric theorem. I read the Mathlib declaration recorded by this existing leaf.

Step 2 uses lem-weil-pbc-proper-ideal-contained-in-maximal only for a maximal ideal containing a given prime, exactly its final sentence. I read Algebra Tag 00E0, `lemma-Zariski-topology`, the maximal-ideal existence assertion and its proper-ideal application, and Tag 00E1, `definition-Zariski-topology`. The second cited node, def-weil-affine-spectrum, supplies the prime spectrum with its Zariski topology. Writing a closed singleton as V(S) shows directly that any prime containing the given prime must be that point; the chosen maximal ideal is therefore equal to it. The elementary step contains this argument rather than citing a definition node as if it asserted the closed-point criterion. For the basic fact that a maximal ideal is prime, one may directly check: if ab lies in m and a does not, write 1=u+ra with u in m and multiply by b to get b in m.

Step 3 uses lem-weil-pbc-zero-dimensional-spectrum-profinite only for its compact Hausdorff conclusion under the all-primes-maximal hypothesis from step 2. I read Algebra Tag 04MG, `lemma-ring-with-only-minimal-primes`, and verified the exact statement of the existing node. It applies to each actual chart ring, without passing to its reduction or imposing reducedness. The separate affine-scheme-qcqs node supplies quasi-compactness of those charts. The statement of pqf-lem-qs-intersection-qc supplies quasi-compactness of their overlaps because X is quasi-separated; I read Schemes Tag 01KO, `lemma-characterize-quasi-separated`, which is the source of this criterion. No overlap is claimed affine merely from quasi-separatedness.

Step 4 is the full finite-neighbourhood argument of Topology Tag 08YB, `lemma-quasi-compact-in-Hausdorff`, proof (1), applied to the quasi-compact overlap inside a Hausdorff chart. I read that proof. The finite subcover and finite intersection of disjoint neighbourhoods prove the claimed closedness from the definitions, so this step is elementary and no new topology lemma is needed. Then closedness of U_i is checked on the original chart cover by writing X minus U_i as the union of the open sets U_j minus U_i. This is the argument behind the affine-chart part of 0CKV, with the global closedness inference written explicitly.

Step 5 uses def-weil-closed-immersion for the factorization defining an immersion (identity closed immersion followed by the open inclusion), and lem-weil-pbc-immersion-closed-image-closed-immersion for precisely its closed-image criterion. I read Schemes Tag 01IQ, `lemma-immersion-when-closed`, and compared the node statement. The hypothesis is global closedness proved in step 4, not just closedness in one chart. The resulting closed subscheme has the original restricted structure sheaf, including nilpotents.

Step 6 uses exactly the whole statement of lem-sc-closed-affine-union-affine: finitely many affine closed subschemes covering a scheme set theoretically imply it is affine. I read Limits Tag 09NL, `lemma-affines-glued-in-closed-affine`, including its proof, and opened the existing node. The source imposes no separation, Noetherianity, finite-type, reducedness, or scheme-theoretic-cover hypothesis. All its actual hypotheses are established by steps 1 and 5. The empty-family case is explicitly present in the cited node and gives the empty affine scheme. This generic tool is not the item restated: it applies to arbitrary-dimensional schemes with a given affine closed cover, whereas the item constructs such a cover from zero-dimensionality and quasi-separatedness. The off-unit spectrum, intersection and closed-cover tools are declared in split_report.tool_uses for the maintainer's review, not in the maintainer-owned tool_uses field.

For delivery-errors B1-B10, there are no new nodes, no duplicated notions and no new attachment or Mathlib-leaf claim. The existing statement stays self-contained and unchanged, sources have tags and labels, and searches are actual logged calls with the returned results. For C1-C8, I compared every cited statement with its use, stored all nine verbatim citation quotes, expanded the two elementary topological/algebraic arguments, and checked by traversal that none of the cited dependencies has a path back to this item. For D1-D5, the item itself carries the construction and local closedness argument; no new node hides it, and the use of the general closed-cover theorem comes after its hypotheses have been proved. No step exceeds 2000 characters. For E1-E7, I checked the hypotheses at each application as above; no source error or statement dispute was found.

Edge cases checked were Spec(0), Spec(k[epsilon]/epsilon^2), and the spectrum of the infinite Boolean ring product over the natural numbers of F_2. The first has no primes and permits the empty cover. The second retains its nilpotents and satisfies all the arguments. The third has an infinite compact Hausdorff spectrum, so the proof must not replace compactness with finite/discrete topology or use the finite-discrete Mathlib instance. An infinite disjoint union of field spectra illustrates why the finite-cover step really uses quasi-compactness. The correction made during self-review was to expose the closed-point/maximal-ideal argument and the compact-Hausdorff argument instead of letting either appear as an uncited standard theorem. I also chose the already available 09NL node for the final inference, avoiding auxiliary nodes for clopen affineness and disjoint-union gluing.
