# Stage-1 delivery: lem-trf-birational-curve-quasifinite

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-birational-curve-quasifinite.json`: existing statement node, now split in five proof steps; no exact Mathlib match.
- `citations.json`: seven verbatim statement excerpts covering every node cited by every proof step.
- `searches.jsonl`: four new searches made with the required msearch.py, with their returned hits read.
- `report.md`: this report.

## New nodes

None. Zero new nodes and zero new Mathlib leaves.

## Attachments

None. I searched the read-only project Lean under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its precise blueprint tag, birational/quasi-finite combinations, dominant maps of curves, and integral curves. No project declaration was found that proves this statement. Existing results about quasi-finite morphisms and divisors assume additional properties; they do not establish this item. The imported item has no own Lean audit/declaration to inspect. The upstream master checkout was not used as evidence of a finished proof.

## WANTED

None. All mathematical sources used below are present in the repository.

## What changed and what was wrong

The item was a true, unsplit statement with a reference to a general theorem. I preserved its statement verbatim and retained its original source, ancestry and inherited search history. I added the already existing definitions of schemes over a base and separatedness (`def-weil-scheme-over-base`, `def-weil-proper-morphism`) to its statement dependencies. No target statement or definition was changed.

Stacks Tag 0AB6, `varieties-lemma-quasi-finite-in-codim-1`, condition (1), does imply the statement: a finite-type curve over a field is Noetherian, its local rings have dimension at most one, and the unique generic residue extension is finite. Instead of manufacturing a new node restating that general quasi-finiteness theorem, I give a direct proof in the present one-dimensional finite-type-over-a-field setting. This is allowed below the unit level. It keeps the same quasi-finiteness input for the proper birational curve argument and changes no unit or chapter route. The generic-extension and separatedness assumptions are redundant in this direct proof but remain in the statement.

The current blueprint ancestor's main-20261015 proof has no verbatim projective-preparation sentence: that geometric input is exposed by its existing descendant chain (the item's blueprint.from/via and its parent split). I preserved that historical ancestry rather than inventing a different unit or changing maintainer metadata. The chapter and unit records were read, and neither is edited.

The inherited audit for `pqf-lem-locqf-fibre-discrete` mentions an old ProperQuasiFinite module path absent from this local source snapshot. My proof uses the node's actual statement, not that historical path or an unchecked attachment claim. No new closed audit is asserted.

## Searches and existing material

I searched the whole DAG for Tag 0AB6, `quasi-finite-in-codim-1`, dimension-formula and finite-fibre statements, and for closed-point field/finiteness statements. I ran blueprint_refs.py searches for `quasi-finite`, `dimension formula`, `closed point field`, and `curve`, plus its ancestor lookup for this item. The quasi-finite hits include `pqf-lem-locqf-fibre-discrete`; the closed-point and closed-subset facts are already `lem-kun-closed-point-field` and `lem-kun-finite-closed-subscheme`. Those are reused without modification. No different blueprint node states this dominant-curve theorem, so blueprint.same_as stays empty.

The four new Mathlib searches are the exact queries in the appended mathlib_searches entries and searches.jsonl: LeanFinder for dominant locally finite-type integral curve maps; Loogle for QuasiFiniteAt and LocallyOfFiniteType; grep `quasiFinite` in AlgebraicGeometry; LeanSearch with the second formulation, nonconstant curve maps having finite fibres. All services returned hits. I read the outputs and inspected Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:303–304: `LocallyQuasiFinite.of_finite_preimage_singleton` supplies the final finite-fibre conversion, but the finiteness of curve fibres remains to be proved. None of the returned declarations supplies the whole item. No unavailable service was recorded as a negative result. The inherited older searches remain clearly distinct from these Q76 searches.

## Tool uses

The item declares the generic tools in split_report.tool_uses: `lem-sc-scheme-sober`, `lem-kun-closed-point-field`, `lem-kun-finite-closed-subscheme`, and `pqf-lem-locqf-fibre-discrete`. The first supplies generic points, the next two supply closed-point and finite-set facts, and the last converts finite fibres to pointwise quasi-finiteness. They are used as black boxes for their written statements; no alternate Kunneth or Picard proof route replaces the trace-formula unit. Definitions are notion dependencies. No maintainer-owned top-level tool_uses field was added.

## Not duplicates

No new nodes were created. In particular, the closed-point characterization, finiteness of closed subsets consisting of closed points, sobriety, and finite-fibre criterion all reuse existing nodes. The generic/non-generic point classification and the intermediate-field finite-dimensional argument are written out as short arguments in the item's own steps, not created as nodes or moved into a restatement of the item.

## Review by Q76

I read Stacks varieties.tex Tag 0AB6 (`lemma-quasi-finite-in-codim-1`, lines 3187–3264), especially its hypotheses, condition (1) and its dimension-formula proof. It confirms the item's conclusion without assuming normality, smoothness, properness, algebraically closed k, or surjectivity. I also read schemes.tex Tag 01IS (`lemma-scheme-sober`, lines 1930–1948), varieties.tex Tag 0478 (`lemma-locally-finite-type-Jacobson`, lines 2670–2692), morphisms.tex Tags 01TE and 01TF (closedness and residue extensions), Tag 01TH (`lemma-quasi-finite-at-point-characterize`, lines 3664 onward), and properties.tex Tag 0BA8 (`lemma-Noetherian-irreducible-components`, lines 523–532). The tag-to-label mappings were checked in stacks-project/tags/tags. For the two Kunneth tools, I read both full node files and their blueprint source statements/proofs; for the finite-fibre tool, I read its full node statement and proof. There are no new nodes with separate sources to review.

Step 1 cites the exact sobriety statement: each irreducible closed subset of a scheme has a unique generic point. The integral-scheme definition explicitly supplies nonemptiness and irreducibility. The dimension definition explicitly forbids chains of length two when dimension is one. The displayed strict-closure-chain argument proves closedness of every non-generic point; uniqueness of generic points justifies both strict inclusions, so no tacit T0 theorem is missing. A singleton space has dimension zero, proving the generic point is not closed. This reasoning works for each of E and C. It is a short direct argument from the cited definition and sobriety, not an unstated classification lemma.

Step 2 is elementary continuity and density, written out: p(E) is contained in the closure of the image of the generic point and is dense, so that image is the unique generic point. No finite generic field extension or properness is silently substituted for dominance.

Step 3 uses precisely part (a), in both directions, of lem-kun-closed-point-field. E and C are both of finite type over the same field k, exactly its hypotheses. The residue-field definition explicitly gives the homomorphism from kappa(p(x)) to kappa(x). A field homomorphism preserving 1 is injective, and the k-morphism hypothesis makes it k-linear; its image is a subspace of a finite-dimensional k-space. This two-line linear-algebra deduction proves that the image point has finite residue extension and hence is closed. It does not infer closedness from an arbitrary continuous image.

Step 4 first proves the generic fibre set is exactly one point, using Steps 1–3 and nonclosedness of the generic target point. For the other fibres, y is closed, so its inverse image is closed; dominance excludes eta_E, and the Step 1 classification makes every remaining point closed in the ambient E. The statement of lem-kun-finite-closed-subscheme is exactly about a closed subset of a finite-type scheme over any field consisting of ambient closed points. It therefore gives finiteness here, including the empty set. No unproved scheme-theoretic factorization from mere image containment is used, nor is a fibre assumed reduced. Tag 0BA8 itself supplies only the finite-components ingredient; the full closed-subset conclusion is taken from the cited existing node, not incorrectly attributed verbatim to that tag.

Step 5 takes the exact statement of pqf-lem-locqf-fibre-discrete: local finite type and a finite preimage of the singleton y imply quasi-finiteness at every point over y. Both hypotheses have been supplied. The conclusion is pointwise quasi-finiteness in the statement's sense, without an identification of incompatible definitions or a missing quasi-compactness hypothesis. The seven excerpts in citations.json are verbatim parts of the relevant statements and cover every use.

I checked delivery-errors B–E. B: no new-node shape/source/definition problems arise; TeX is escaped once in JSON, inherited data is retained, and the item has its blueprint place and same_as. C: all non-elementary inputs are cited for their statements, and citations never use hidden constructions from their proofs. Off-unit tools are declared with their reasons. D: the actual fibre argument remains in the item rather than a new child carrying the conclusion. E: finite type over the original field is checked before each closed-point/finiteness application, and local finite type is checked at the final criterion. Nothing uses an affine intersection, normality, perfectness, catenarity, or a finite-type target hypothesis beyond what is assumed.

Small cases checked: t maps to t^n on A1 (also in characteristic dividing n, so inseparable maps are allowed); normalization of a nodal integral curve (several points may lie above one closed point); the open immersion A1 minus {0} into A1 (empty fibre at zero); and identity maps (generic singleton and closed singleton fibres). A constant curve map fails dominance and would have a one-dimensional fibre, pinpointing why Step 2 is necessary. The integral hypothesis excludes a second component contracted to a point. If k is not algebraically closed, closed-point residue extensions can have degree greater than one and the intermediate-field argument still works. No step exceeds 2000 characters; their lengths are 903, 272, 580, 698, 356, so no long step hides a lemma.

I corrected no disputed statement. I replaced an absent proof by the five checked steps, added the two missing notion dependencies, and recorded that this is an agent-written direct curve proof rather than pretending to reproduce the more general dimension-formula proof of 0AB6. There is no SGA citation. All writes are confined to the designated sandbox; no Lean was written and no compiler, Lake, or local DAG/preflight checker was run.

## Unfinished work

None in the one-level split. Required server dry run and direct push follow this review; their results are recorded below after completion.
