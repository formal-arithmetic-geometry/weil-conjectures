# Worker report: Q131

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-m-pseudocoherent-criterion.json`: statement, split; both directions of the fixed-degree criterion, seven proof steps, no new nodes. Mathlib searches found no match.
- `citations.json`: one verbatim statement quotation for each of the 26 step citations.
- `searches.jsonl`: actual Q131 searches recorded by the mandated search command. The six inherited Q117 search records in the item remain intact; they are not claimed as searches run by Q131.
- `report.md`: this report and signed review.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` for the blueprint tag, the affine pseudo-coherence notion, and `IsMPseudoCoherent`/fixed-degree variants. The existing `AlgebraicGeometry.isPseudoCoherent_affine_iff` in `AlgebraicGeometry/AffinePseudoCoherentCriterion.lean:74` proves full pseudo-coherence, not the fixed-m assertion. Ring-level `IsMPseudoCoherent` and its localization gluing do not state the scheme comparison. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None. All mathematical sources used here are present in `literature/stacks-project/`.

## Corrections and inherited issues

The original statement is correct and is unchanged. It is the fixed-m clause of Tag 08E7, `perfect.tex`, `lemma-pseudo-coherent-affine`, lines 2223 onward. The item had no proof. The related existing full pseudo-coherence affine criterion is insufficient for this item; the scheme and ring definitions need to agree at the one specified integer, without passing to all integers.

The inherited blueprint ancestry has `from.node: null`; `python3 tools/blueprint_refs.py ancestor lem-sfb-affine-m-pseudocoherent-criterion` confirms the null ancestor. Its long inherited place and via chain locate the prerequisite in direct-images proof (3), via Tag 09VF. They are retained without inventing an ancestor. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, as well as the recorded chapter and unit. No unit or chapter route is changed. The current blueprint supplies the ambient preservation goal; this is its inherited algebraic prerequisite.

The source realizes approximation maps locally by chain maps before taking module sections (Tag 08C9). After finite free refinement, the existing affine derived equivalence instead lifts the derived approximation map itself. This uses fullness in the stated unbounded categories and the natural cohomology comparison, so no new local-chain-map lemma and no target boundedness assumption is necessary. This is a node-level refinement of the same standard-open proof, not a change of unit route.

## Not duplicates

No new nodes were created. DAG searches by Tag 08E7, pseudo-coherence, fixed-degree wording, finite retracts, local actual maps, localization gluing and the affine comparison found the existing tools now cited. Whole-blueprint searches were run with `tools/blueprint_refs.py search` for `pseudo.coherent`, `pseudo-coherent`, `pseudo`, `08E7`, and `finite retract`, and the latest blueprint was searched as text. None states the fixed-m affine criterion in a different form; `same_as` stays empty.

In particular `lem-pc-affine-pseudo-coherent-criterion` only states the full pseudo-coherence equivalence; `lem-pc-affine-pseudo-coherent-localization-cover` and its principal-model lemmas require full pseudo-coherence or a local quasi-isomorphism, rather than a degree-m approximation. They are not cited for conclusions they do not state. `lem-pc-finite-retract-sheaves-affine-trivialization` and `lem-pc-affine-finite-free-sheaf-complex-lift` do state exactly the local trivialization and complex lifting needed, so no duplicate versions were made.

## Mathlib searches

For the item I ran the mandated command with LeanFinder (two different phrasings), LeanSearch, Loogle (`"PseudoCoherent"`), and grep (`pseudo.?coher|IsMPseudoCoherent`). The grep and Loogle searches returned zero hits. LeanSearch returned precoherent site equivalences and affine-space equivalences. LeanFinder returned categories of scheme modules, underived finite presentation/quasicoherence and finite type generator data. I read the returned signatures: none concerns bounded finite free approximations in a derived category. Every newly recorded query is copied exactly from `searches.jsonl`, with the actual hit names and no unavailable service represented as a negative result. No Mathlib leaf is claimed.

## Review by Q131

I read Tag 08E7 in `perfect.tex`, including both directions and the invocation of `more-algebra-lemma-glue-pseudo-coherent`. I also read Tag 06Z0 (`lemma-affine-compare-bounded`) and its cohomology calculation, the fixed-m statement and proof of Tag 066D in `more-algebra.tex`, Tag 01HV in `schemes.tex` (sections, restrictions, naturality and exactness), and the local summand lemma Tag 0BCI in `modules.tex`. These are the source ingredients behind the existing nodes. There are no new-node sources to certify. I opened and read the statement of every cited node, including the Lean-form statements of the finite-free complex lift and all clauses of the ordinary tilde/Gamma adjunction. The quotations in `citations.json` are copied from those statements, not from their proofs.

1. The cohomology comparison node states a *natural* isomorphism for every integer, so it applies to approximation morphisms, not just to the objects. The adjunction node states the unit isomorphism and all-colimit preservation. From these I wrote out full faithfulness, cokernel preservation and reflection of epimorphisms by cancellation. This checks both the isomorphism degrees and the surjective boundary degree without assuming global sections is exact on arbitrary sheaves.
2. The ring definition supplies a bounded finite free source and a derived arrow. The affine derived equivalence supplies its sheaf image; tilde sections and finite coproduct preservation identify its terms with finite free sheaves. The strictly-perfect and scheme-m-pseudo-coherent definitions then give the one-open witness, using Step 1 for the cohomology conditions. Here the ring is A (not a localization introduced later), and no lower bound on the target occurs.
3. The scheme definition supplies local *strictly perfect approximations*, not local quasi-isomorphisms. The perfect-complex definition says these terms are retracts of finite free sheaves and have finite degree support. The simultaneous retract-trivialization node applies to exactly that finite support and to the selected point of the open. It produces one neighbourhood trivializing all terms. This is why an infinite intersection of trivializing opens is not used.
4. The basic-open node states the actual neighbourhood-basis property, and the compactness/unit-ideal node gives precisely the two subsequent finite-cover consequences. The restriction-limits and restriction-colimits statements say kernels and cokernels are preserved. The proof spells out the quotient defining H, so it justifies preservation of the approximation conditions and the derived restriction computation. The finite degree interval survives every restriction.
5. The principal-localization morphism node identifies Spec(A_f) with D(f) as an open subscheme, rather than just homeomorphic spaces. The tilde-sections node gives the actual fraction maps, their restriction compatibility and scalar actions. I wrote the termwise identification on D(g/1), including the fact that these form a basis because every g/f^a differs from g/1 by a unit. Thus the target is the associated complex of the localized representative, with its differentials, not an unidentified derived object. This is the elementary fraction calculation from the cited statements.
6. The finite-free sheaf-complex lift node assumes only an upper bound, and concludes an *actual complex isomorphism*. Our source has a lower bound too. I explicitly recover the same lower bound for the lifted module terms using the ordinary tilde/Gamma unit and replace zero objects by literal zero modules if needed. Fullness of the affine equivalence over A_f supplies the approximation arrow in D(A_f); it applies because both endpoints have quasi-coherent cohomology. Step 1 reflects the cohomology conditions. This avoids claiming the existing lift node states boundedness below, a derived morphism lift, or m-pseudo-coherence by itself.
7. The ring-gluing node explicitly includes the fixed-m clause, not just its pseudo-coherent clause. Every localization has the same m and the finite family generates A by Step 4, so all its hypotheses hold. Passing from the representative N back to M is invariance under the derived isomorphism, built into the definitions.

I tested the degenerate cases: zero approximants and rank-zero terms, any integer m, the zero ring and empty spectrum, and unbounded representative complexes. On the empty spectrum the scheme condition is vacuous, and every module over the zero ring is zero, so the ring condition has its zero-complex witness. For a nonzero ring the finite standard cover is nonempty and no degenerate gluing issue arises. For general rings, boundedness of an approximating source is the only bound used. The proof never uses Noetherianity or all-m pseudo-coherence. Every non-elementary ingredient is a statement citation; the basis fraction comparison, reflection of epimorphisms, and zero-term replacement are written out from those statements. All seven steps are below 2000 characters; none conceals a separate finiteness, descent or comparison theorem. Off-unit generic tools are declared individually in `split_report.tool_uses`; the tools are exactly those required by the Stacks affine proof.

I checked delivery-errors B--E against the files: no new-node schema or search obligations are left; each step's uses has a verbatim quotation; the proof uses no proof-only output of another node; there are no clause-restatement nodes, no appeal to an unlisted source as a lemma, and no coefficient-category or degree changes. I corrected a draft reference to B in the forward implication to A and made the principal-open basis explanation explicit before running checks.

## Unfinished work

None in the authorized stage-1 split. The first prescribed dry run exited successfully: `OK (not pushed) deliver/Q131/lem-sfb-affine-m-pseudocoherent-criterion at 4a9f0924d5c: preflight passed`. It ran the server preflight, including DAG and split checks. After recording this result and removing an accidental backslash before an apostrophe in Step 5, the final artifact is dry-run again before direct push.
