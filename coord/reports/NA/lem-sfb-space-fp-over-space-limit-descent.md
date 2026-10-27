# Stage-1 report: lem-sfb-space-fp-over-space-limit-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fp-over-space-limit-descent.json`: statement item, now split in 11 steps; no Mathlib match. The original statement, statement dependencies, source, creation stamp and inherited blueprint ancestry are retained. Five actual searches from this session were appended to the inherited search records.
- `citations.json`: a verbatim statement extract for each of the 32 step/node citations (the exact number is checked from the file).
- `report.md`: this report. The sandbox also contains the actual `searches.jsonl` and two local writing helpers. Neither helper is a delivered node or a project/launcher modification.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, Tag 07SK, finite-presentation terminology, and algebraic-space/inverse-limit descent. No declaration states this full algebraic-space-base theorem. In particular a scheme theorem cannot attach this item, and an upstream sorry would not be a finished proof.

## WANTED

None. Read `literature/stacks-project/spaces-limits.tex`, Tag 07SK (`lemma-descend-finite-presentation`), statement and complete proof, and Tag 07SF (`lemma-directed-inverse-system-has-limit`). For effectivity I read `spaces-descent.tex`, Tag 0ADT (`lemma-descent-data-sheaves`), and `bootstrap.tex`, Tag 04S6 (`theorem-final-bootstrap`), condition (3), and Tag 0ADV (`lemma-descend-algebraic-space`), especially its singleton/countable-cover argument. For finite presentation I read `spaces-descent.tex`, Tag 041V (`lemma-descending-property-finite-presentation`) and the quasi-separatedness proof preceding it. There are no new nodes needing further sources.

## Errors, scope and blueprint

The imported statement is correct against Tag 07SK; no statement dispute or weakening was needed. Its last sentence, that the bases need not be schemes, is essential. The existing scheme-base theorem does not itself prove that clause. I supply the passage from scheme bases to space bases by atlas gluing; this is an agent elaboration of the source's atlas route, recorded as `proof_origin.by = agent`, rather than claiming that the source wrote these exact steps.

The source presentation argument omits checks on relations. Here inverse equations, the diagonal identity, and the triple-overlap cocycle are all descended by the existing equality clause. I do not conclude that an arbitrary pair of etale maps is an equivalence relation. Likewise Tag 0ADT and its DAG node assert sheaf realization, not algebraicity: the proof separately verifies every scheme-test hypothesis of the atlas bootstrap.

`python3 tools/blueprint_refs.py ancestor lem-sfb-space-fp-over-space-limit-descent` reports `blueprint.from.node = None`. The creation chain terminates at `lem-sfb-admissible-direct-image`, created from a Lean module rather than an imported node; I have retained that inherited null ancestor and its detailed place/via chain rather than inventing an imported ancestor. Searches of the entire imported blueprint for `07SK`, `algebraic spaces`, `descent datum`, `finite presentation` and `inverse limit` found no full duplicate. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof (3). This generic approximation input lies below the inherited direct-image/alteration branch; no chapter or unit route is replaced. Generic tools filed in other units are declared only in `split_report.tool_uses` for maintainer review.

## Not duplicates

No new node was created. The item is stronger than `lem-sfb-fp-space-qcqs-base-limit-descent`: that node assumes all bases are schemes, whereas this item permits arbitrary qcqs algebraic-space bases. `lem-sfb-fp-space-limit-category` is restricted further to affine scheme bases. They are reused, not copied. `lem-sfb-etale-space-single-cover-effective-descent` only descends spaces etale over the covering space, and cannot descend our arbitrary finitely presented V_j; I deliberately use the general sheaf-realization and atlas-bootstrap statements instead. `lem-sfb-space-finite-type-fppf-effectivity` has a scheme base, so it is not silently applied to B_j.

## Mathlib searches

The five queries in this session were run with the required `msearch.py`; all services answered successfully. They consist of LeanFinder, Loogle, grep under `AlgebraicGeometry`, LeanSearch, and a second LeanFinder phrasing. I read every returned hit. The best geometry hits are scheme-only: `AffineTransitionLimit.lean:635-645` proves eventual equality for maps between schemes; `Morphisms/FinitePresentation.lean:35-57,91-96` defines and base-changes a property of scheme morphisms; `Morphisms/FlatDescent.lean:175-185` is scheme property descent. `CategoryTheory/Presentable/Finite.lean:84-94` concerns maps out of an already categorically finitely presentable object into a colimit, and supplies neither the geometric finite-presentation hypothesis nor descent over an inverse system of space bases. None is an exact match or a one-line specialization. The inherited five searches remain marked as inherited evidence, not searches I claim to have run in this session.

## Review by NA

I reviewed B--E of `coord/delivery-errors.md` point by point with the item, all 14 cited node statements and the Stacks files open. I checked the original statement against all three clauses of 07SK and did not add separatedness, affineness of the bases, or a finite-type ambient S. I checked every proof dependency for a path back to this item; none has one. The proof uses existing, strictly smaller scheme-base and descent tools, so it neither relabels its own clauses as new nodes nor moves the whole theorem into a new node. No step exceeds 2000 characters. Every step using a theorem is marked non-elementary; elementary fibre-product associations, coordinate descriptions and finite common-stage choices are written in those steps.

Steps 1--2 use the affine-atlas node for exactly its existence assertion, and the representable-scheme-test node to ensure double and triple overlaps are schemes. The affine-scheme-qcqs, qcqs fibre-product and affine-locality statements establish the finiteness hypotheses. The affine-limit node explicitly provides the limit, affine projections, and arbitrary base change. The fibre-product/etale-cover node makes the pulled-back atlas a cover. I checked that R_i and T_i need only be qcqs, and may be nonaffine; that is why the qcqs scheme-base descent theorem, not just its affine version, is used.

Step 3 uses the arbitrary-space base-change clause of the flat/proper/fp-locality node and the object clause of the qcqs scheme-base theorem. The latter is stated over Spec Z: forgetting S is harmless because the resulting U_i-map, and later B_i-map, recovers S. Step 4 applies its morphism clause to both the overlap map and its inverse, and its equality clause to both inverse equations. All objects involved are fp over R_i, which was checked to be a qcqs scheme. Step 5 uses the same base-change statement for the two fp objects over T_i, and the equality clause on T_i and U_i for the cocycle and diagonal equations. A finite number of enlargements has a common upper bound; no infinite simultaneous stabilization is asserted.

Step 6 uses covering calculus to turn the etale atlas into an fppf cover, the sheaf-realization node for a sheaf with exactly the prescribed gluing map, and the fibre-product node for the scheme A x_{B_j} U_j on each scheme test. This verifies the bootstrap's flat, lfp and surjectivity hypotheses, so the bootstrap node supplies algebraicity. The corrected distinction is explicit: sheaf descent alone does not say that F is a space. No finite-type restriction on V_j is needed for this singleton bootstrap argument.

Step 7 applies the fp-locality node only with scheme target A. Its covering Q=A x_{B_j} U_j is a scheme, and covering calculus (4) verifies it is an fppf cover in the scheme sense. Its local object is literally the base change of V_j. Step 8 checks qc and qs on their own scheme tests; the relative diagonal is tested using the two maps from A, and its tested fibre is a base change of the diagonal of E/A, not the absolute diagonal over S. The qc base-change node supplies exactly that permanence fact. The chart-test statement supplies lfp with target atlas U_j and a scheme atlas of V_j. Thus I did not overread the scheme-target restriction of the fp-locality node.

Step 9 uses full faithfulness of sheaf realization to identify two objects with exactly the same datum, producing an isomorphism over B. Step 10 uses fp base change and morphism descent over U_i, equality descent over R_i for the displayed compatibility equation, then full faithfulness to descend the map itself. Step 11 uses equality descent over U_i followed by the same faithful restriction to the atlas. In steps 9--11 the covers are fppf by the cited covering-calculus statement; no uncited assertion that an arbitrary map out of an atlas descends is made. For every cited node at every step I copied the actual statement passage into `citations.json`, rather than quoting a proof or an external theorem in place of it.

I tested the argument on a singleton index set (ordinary atlas descent), empty Z, empty bases and atlases, constant systems with non-scheme bases, and a qcqs nonseparated base with nonaffine double overlap. Empty schemes are affine and admit the same fibre-product identifications; all equations and cover tests remain meaningful. None requires a nonempty space or an affine overlap. The argument handles a small directed poset without a least element by the explicitly justified cofinal tail. All gluing is along one atlas, so no countability/size issue for an unbounded covering family is introduced. I found no false small-case statement and no source error.

## Unfinished work

No mathematical part of this stage-1 split remains. Formal Lean proofs remain outside this assignment. The required server dry run and direct delivery follow this report; no local checker, Lean compiler or Lake invocation has been used.
