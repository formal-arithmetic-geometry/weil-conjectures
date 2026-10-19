# Q37: lem-zl-irreducible-fibre-dimension-lower-bound

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-irreducible-fibre-dimension-lower-bound.json`: statement, split into eight proof steps. Mathematical statement preserved; added the existing irreducibility and local-dimension definition citations. Mathlib verdict: no match.
- `citations.json`: 18 entries, one for every step/node pair, with exact relevant text from the cited statement.
- `report.md`: this report. `searches.jsonl` contains the actual search-command records. No new DAG nodes, Mathlib leaves, unit changes, or Lean files.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the blueprint id and the irreducible/fibre/dimension notions, and checked the likely geometry files. The relative-dimension declarations in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` require smoothness. They do not state this result for arbitrary finite-type morphisms. Neither they nor the generic Noether-normalization statements supply every clause of the item. The item has Lean audit state `none`.

## Literature wanted

None. The source and its geometric ingredients are available locally.

## Findings and changes

The item was unsplit, with no proof and no proof dependencies. The sandbox had no earlier item or report, only dispatcher briefs. I preserved the inherited statement, ancestry, audit and search records, adding only explicit definition citations to the statement. There is no statement dispute.

I read `literature/stacks-project/varieties.tex`, label `lemma-dimension-fibres-locally-algebraic`, Tag 0B2L, statement and proof of (1), (2)(a), (2)(b), especially the displayed generic-point transcendence-degree calculation. I also read Tag 0A21 (`lemma-dimension-locally-algebraic`), the local/global and generic-residue dimension clauses; Morphisms 02FZ (`lemma-openness-bounded-dimension-fibres`), 01T8, 01T4, 01T6; Schemes 01JT (the residue-field clause of `lemma-points-fibre-product`); Properties 01OZ; and Topology 04ZA. The proof follows precisely the source route: compute the generic local fibre dimension, then use 02FZ to compare it with each other point and identify the equality locus.

The source treats locally algebraic schemes and invokes their dimension theory freely. To use the existing DAG's finite-type versions without silently changing hypotheses, Steps 1–2 verify that f is actually finite type: the source is Noetherian, every subset is compact, and f is locally finite type by permanence. Its fibres are thus finite type over their residue fields. This is preparatory checking, not a different dimension argument.

I made the blueprint place precise: paragraph 2 of the current main-20261015 Bertini proof, where the universal-family dimension estimate enters the smooth-member argument, through the item's recorded intermediates. The chapter and unit route were read and retained. No key unit statement is being delivered, so no unit realization record was changed.

## Searches and reuse

I searched the whole DAG for 0B2L, its label, fibre dimension, generic dimension, and residue fields. The existing `lem-zl-finite-type-fibre-component-lower-bound` is an affine rational-closed-fibre component bound; it does not state the present pointwise bound for all scheme fibres or the full dense-open equality locus, and is not used as a replacement for this item. The image/fibre dimension bounds are a parent of this item and were not cited back. The existing closed-irreducible dimension, locally-algebraic local/global dimension, tower formula, fibre-product residue-field, openness and finiteness tools suffice; no new node is warranted.

The whole-blueprint searches `dimension fibres locally algebraic`, `generic fibre transcendence degree`, `fibre dimension`, `dimension lower`, and `generic fibre` returned no equivalent blueprint statement. The listed generic-normalization, generically finite and cohomological results have different conclusions. Therefore `same_as` is empty.

For the item I ran the required msearch commands under Q37: LeanFinder with two phrasings, Loogle, LeanSearch, and grep with two patterns. Their full records are preserved in `searches.jsonl` and copied verbatim into the added search entries. I read the returned types: IsDominant and its dense-range equivalence describe the image, the fibre/preimmersion declarations describe the fibre topology, generic-point maps describe partial rational maps, and smooth relative-dimension results assume smoothness. None states this lower bound and equality locus, nor is any a one-line specialization giving it. Loogle and both source greps returned zero hits; the inherited searches are retained, including the old unavailable Loogle query.

## Tool uses

The split declares three non-leaf tools from other units: `lem-sc-closed-irreducible-dimension-trdeg` for the generic-point dimension formula 0B1C; `lem-sc-dimension-locally-algebraic` for 0A21(3) on the irreducible generic fibre; and `lem-weil-pbc-local-fibre-dimension-open` for 02FZ. These are exactly general dimension tools used in the proof of 0B2L. No Bertini-unit step is replaced. Other inputs are Mathlib leaves or Lean-closed tools.

## Review by Q37

I checked every step against the actual cited statements, not their proofs or titles. In Step 1 the finite-type-over-Noetherian node gives scheme Noetherianity, the minimal-closed-subset node gives the required descending-chain condition, and the compact-subsets node explicitly applies to every subset of the underlying space. The field base is Noetherian and one-point quasi-compact. In Step 2 permanence clause (f) says that a locally finite-type composite makes its first factor locally finite type; the k-morphism relation supplies exactly that composite. Every inverse affine-open image is compact by Step 1, so the finite-type definition applies. The base-change node explicitly allows any base morphism, including the residue-field map, and the dimension-finiteness node applies to each resulting field scheme.

Step 3 uses sobriety only for the existence of eta, then writes out the closure argument for xi and the fact that every nonempty open contains eta. In Step 4 the closed-irreducible dimension theorem applies separately to the whole of X and to the closed subset Z of Y; both ambient schemes are finite type, and neither reducedness nor a scheme structure on Z is required by that statement. The tower node states the cardinal identity, and finiteness of the outer transcendence degree makes every term a finite integer, so r is nonnegative and subtraction is legitimate.

Step 5 uses the scheme-fibre statement's actual homeomorphism to the inverse-image subspace, which proves irreducibility and genericity even when X has nilpotents. The fibre-product residue-field node explicitly says its isomorphism respects the two field structures. I wrote out the tensor-with-the-base-field isomorphism and the zero-kernel check, so the extension used in Step 6 is the original kappa(xi)-extension, not an unspecified abstract field isomorphism. In Step 6 the closed-irreducible theorem applies to F itself over kappa(xi), and the locally-algebraic dimension theorem explicitly gives local dimension equal to global dimension for an irreducible locally finite-type scheme. These give the generic local dimension r without a smoothness assumption.

In Step 7 the definition of local dimension supplies a finite nonnegative integer n, since the whole finite-dimensional fibre is one neighbourhood. The openness node assumes only locally finite type and n nonnegative; both are verified. Its set contains x and hence eta, which gives the inequality in the correct direction, r <= n. Step 8 applies that same node at the already established nonnegative integer r. It contains eta and is therefore dense. The lower bound from Step 7 identifies it with the whole equality locus; this proves openness of that locus rather than merely finding some dense open contained in it. Every quoted citation was checked as a literal substring of its node's statement. No proof-only conclusion or undefined comparison is used.

I tested the statement and route on the identity (r=0), a constant map to a closed point (r=dim X), a non-dominant closed immersion (r=0), and the dimension-jump map A^2 -> A^2, (u,v) |-> (u,uv), where the fibre dimension is 1 along u=0 and 0 elsewhere. I also checked a nonreduced irreducible scheme and a non-algebraically-closed base: reduction is not needed, and the residue-field compatibility addresses the latter case. Empty fibres do not enter a claim quantified by x; X itself is nonempty by irreducibility. Thus no extra flatness, dominance, separability, smoothness or properness hypothesis has entered. All eight steps are shorter than 2000 characters; none hides a separate comparison lemma. The main comparisons are explicitly cited existing nodes. B–E checks found no new-node issue, duplicate, circular parent citation, uncited substantial fact, or relabelled clause. No forbidden SGA source is used.

## Unfinished work

None in the one-level split. The preliminary server check_dag and review_split checks passed. The first delivery dry run requested longer citation excerpts for three nodes (four step/node pairs); these were replaced by their complete statements. No mathematical or dependency change was needed. The mandatory dry run is repeated after this correction.
