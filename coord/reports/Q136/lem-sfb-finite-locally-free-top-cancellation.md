## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-top-cancellation.json` (statement, split, no Mathlib match), and `citations.json`. No new nodes and no Mathlib leaves.

Attachments: none for the item. The project declarations `AlgebraicGeometry.Scheme.Modules.exists_local_section_of_epi` and `AlgebraicGeometry.Scheme.exists_affine_trivialization_of_finite_retract` already belong respectively to `new-sbc-local-section-of-epi` and `new-pc-single-retract-sheaf-affine-trivialization`; both source files were read and neither contains `sorry`. These supply auxiliary facts, not the whole item.

WANTED: none.

The original item had no proof. Its statement is correct, including the absence of a lower bound, and is unchanged. One bibliographic clarification: Tag 08C6 (`lemma-local-lift-map`) is in `cohomology.tex`, not `modules.tex`. Tags 08DN, 08C6 and 0BCI were checked against `tags/tags` and their actual TeX labels. The inherited blueprint provenance has `from.node = null`, as printed by `tools/blueprint_refs.py ancestor`; this was preserved, as was its existing place and via chain. The latest direct-image proof is shorter than the historical provenance chain: it assembles proper/open direct-image preservation. This item is an auxiliary pseudo-coherence tool in that chain, not a new proof of direct-image preservation or a change of unit route.

Nothing remains unfinished. No Lean was written and no compiler, Lake, or local DAG checker was run. All writes are in the assigned sandbox.

## Searches and reuse

Searched the live project for the exact blueprint tag and for top cancellation, finite locally free, kernel and split-top declarations. `exists_split_top_differential_cancellation` is not an attachment: it assumes support bounded below by zero and a globally split differential, and its conclusion records flatness/quasi-coherence/finite presentation instead of the item's local finite locally free complex. The ring-level finite-free cancellation theorem also does not state the sheaf-local item.

Searched the entire DAG by Tags 08DN, 08C6 and 0BCI and by local splitting, local sections, finite retracts and direct summands. Opened the constant-rank kernel/image node (requires reducedness), the short exact finite locally free splitting node (assumes the kernel already locally free), and the split-top cancellation node (has a lower bound): none can be substituted without extra hypotheses. Found and reused `new-sbc-local-section-of-epi` and `new-pc-single-retract-sheaf-affine-trivialization` instead of duplicating these facts. Blueprint searches included cancellation, local splitting, direct summand, acyclic top, finite retract, and finite locally free; no blueprint node states this local cancellation theorem. `same_as` is empty.

Ran authenticated msearch LeanFinder twice with distinct phrasings, LeanSearch, Loogle, and two source greps. Read all outputs. Results are generic truncation/cohomology/presentation APIs; `CochainComplex.truncLE`, `ιTruncLE`, and `quasiIsoAt_ιTruncLE` were read in Mathlib/Algebra/Homology/Embedding/CochainComplex.lean lines 39–71. They do not give finite local freeness of the changed term. Thus this is not a one-line Mathlib specialization. Exact new queries and returned records are appended to `mathlib_searches`; earlier recorded searches were retained. No new node needs searching.

## Not duplicates

No new nodes. Existing local-section and retract-trivialization nodes are cited directly.

## Review by Q136

I read Stacks `cohomology.tex` Tag 08DN (`lemma-finite-cohomology`), both parts of its proof, and Tag 08C6 (`lemma-local-lift-map`), including its finite-basis lifting argument. I also read `modules.tex` Tag 0BCI (`lemma-direct-summand-of-locally-free-is-locally-free`), and Section 01AF (`section-kernels`) and Lemma 01AG (`lemma-abelian`). The item is exactly the one-step cancellation performed inside 08DN. Boundedness below is used nowhere in that construction: there is only one kernel replacement, not an infinite induction. I read the chapter record, unit record, and the latest blueprint's direct-image proof; the split preserves the auxiliary route given by the parent item.

Step 1 uses the statement of `lem-weil-pbc-ringed-space-module-exactness-local-lifting`, not its proof: it explicitly equates epimorphy with zero cokernel and local lifting. Since the outgoing top differential has zero target, top cohomology is precisely that cokernel. This also prevents an incorrect assumption about surjectivity on global sections.

Step 2 uses exactly the variable-rank statement of `new-sbc-local-section-of-epi`. No finite rank for the kernel, no reducedness, affineness or quasi-coherence is required. The subsequent shrink trivializes only the single term P^(r-1), using the opened definition `def-sc-finite-locally-free-sheaf`, which permits varying ranks. The section persists on that shrink. The kernel's sectionwise description is explicitly in the cited lifting node.

Step 3 gives the actual retraction a ↦ a − sδ(a), proves that its values lie in the kernel, and checks pi = 1. The statement of `new-pc-single-retract-sheaf-affine-trivialization` takes a sheaf on an arbitrary open U of a scheme and a splitting from a finite free sheaf, and returns a smaller affine neighbourhood with a finite-free trivialization. It therefore applies to this kernel after the step-2 trivialization; I checked both its statement and the existing source declaration at SingleFiniteRetractSheafAffineTrivialization.lean:82. This avoids inventing a new direct-summand node. The local-ring condition of 0BCI holds on every scheme, not on a general ringed space.

Step 4 is an explicit definition and verification, not a hidden cancellation theorem. The opened cochain-complex definition states d squared zero and the precise chain-map equation. Factoring the incoming differential through the kernel, then using the injective inclusion, proves its only changed square-zero equation. Both altered chain-map equations are written. Restrictions of a local basis remain bases, and the zero module has the empty basis. No simultaneous trivialization of infinitely many terms is used.

Step 5 checks each degree separately, including r−2 (whose outgoing codomain changed) and r−1 (whose cycles now equal its whole term). For boundary subsheaves the cited exactness/local-lifting node really does state the criterion in terms of locally lifting sections; the same incoming map defines the same image. Hence no unstated restriction-exactness or homotopy-invariance lemma is being smuggled in. At r the split epimorphism directly gives zero cokernel, and above r both terms vanish. There is no appeal to the proof of a cited node.

Small cases checked: empty X (vacuous), P^r = 0 (take zero section; K = P^(r−1)), an identity pair in degrees r−1,r (K = 0), rank-zero P^(r−1), and negative r with an infinite lower tail. These meet the same formulas. A nonzero P^r with P^(r−1) = 0 contradicts H^r = 0 and is never silently admitted. Nonreduced schemes are included: the retract theorem does not assume reducedness. Every non-elementary step is under 2000 characters. There are no new statement-only nodes, no restated clause moved into a dependency, and no source or statement dispute. All citations have verbatim statement quotes in citations.json. Generic off-unit tools and their reasons are declared only in split_report.tool_uses, never in the maintainer-owned top-level field.
