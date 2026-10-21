# Worker report: lem-pe-scalar-cone-tensor-model

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-scalar-cone-tensor-model.json`: statement, split into six steps; unchanged statement, no whole-item Mathlib match.
- `citations.json`: a verbatim statement quotation for every citation of every proof step.
- `searches.jsonl`: five actual N6 searches made with msearch.py. The item's seven inherited search entries are retained unchanged.
- `report.md`: this report.

No new nodes, no Mathlib leaves, and no Lean files. The sandbox initially contained only dispatcher brief markers; there was no earlier split to preserve or dry-run first. All writes are inside the assigned sandbox.

## Attachments

No whole-item attachment. I searched WeilConjectures for the exact blueprint tag (none) and the scalarCone/tensorScalarCone concepts, and read TensorMappingCone.lean with its full binder context. DerivedCategory.kFlat_scalarCone, isIso_μ_scalarCone, tensorScalarConeIso', tensorScalarConeIso'_hom_naturality, tensorScalarConeIso and tensorScalarConeIso_hom_naturality have explicit proofs without sorry in their own bodies. They cover the first three assertions, but do not explicitly state the final localization descent assertion. I therefore retained the existing lean_candidates metadata and supplied an actual split, rather than asserting an attachment of only part of the item. No transitive axiom closure is claimed from source text alone.

## WANTED

None. The current blueprint, project source, Stacks source and Mathlib localization source needed here were available locally.

## Findings and changes

The statement is well-typed and needs no correction. Its arbitrary scalar b need not be regular: the cone is K-flat regardless, while it need not resolve a quotient concentrated in degree zero. I kept that distinction and made no quotient identification. In particular the general module-sheaf tensor-cone lemmas from the Picard chapter are not applicable to an arbitrary monoidal abelian category; I read their statements and did not cite them.

The main missing argument was the sign in the right tensor model. With target-first cone coordinates C^n ⊕ C^(n+1), the right model needs diag(1,(-1)^(n+1)); the left model is already the cone. The differential and inverse checks are written in step 1. Step 2 supplies the diagonal map and naturality, so the proof does not silently treat arbitrary cone choices as functorial.

For K-flatness I reused the general cochain short-exact long exact sequence, its naturality and the five lemma. These are genuine generic Mathlib tools, valid in arbitrary abelian categories. I searched the DAG for cone, K-flat, tensor-mapping-cone and localization nodes and used the existing results. Blueprint searches for scalar cone and tensor mapping cone found no exact duplicate. No new-node duplicate comparisons are required.

The five N6 Mathlib searches have the exact tool/query strings in searches.jsonl and the item. I read all returned hits. Tensor-unit HasTensor instances and HomologicalComplex.tensorObj construct tensors, the HomComplex hits express scalar identities, and Module.Flat hits concern ordinary flat modules. None states this combined K-flat scalar-cone model, naturality and localization descent. I read Algebra/Homology/Monoidal.lean:34-64 for the tensor construction. A second semantic phrasing again found unit-tensor existence rather than the assertion. Loogle and grep returned no hits; no unavailable service is recorded as absence.

## Route and tools

The item belongs to the Nakayama resolution unit; the current unit and chapter records and the current resolution proof were read. The proof realizes precisely the On X paragraph, “hence K-flat” and the natural cone computation. It neither changes the chapter nor replaces the unit's resolution/pullback route. The single off-unit non-leaf tool, lem-sfb-derived-monoidal, is declared in split_report.tool_uses: the item already assumes its general derived tensor, and the Nakayama unit supplies no general derived-monoidal construction. The other theorem tools are existing Mathlib leaves. No unit realization file needs editing for this supporting node.

## Review by N6

I read TensorMappingCone.lean:37-158, including the ambient HasDerivedCategory, closedness, braiding, additivity, functorial flat resolution, Linear and MonoidalLinear assumptions. They agree with the item's hypotheses and its fixed universe convention. I also read the current sk-lem-pe-derived-nakayama-resolution.proof.md (its internal blueprint id is det-pe-derived-nakayama-resolution), and the unit/chapter records. The proof here is marked agent-written: it expands the source calculation and the descent consequence rather than pretending that the source already declares all of it. There are no new nodes whose sources require separate review.

Step 1 uses the actual signed total differential and tensor maps of def-sfb-preserves-kflat-quasi-iso, the target-first cone and shift formulas of def-weil-abstract-derived-category, and the natural unitors of def-sfb-monoidal-category. I checked the two finite summands and both matrix entries: s_(n+1)=-s_n and s_n squared is 1. All statements cited in this step say these precise things. The tuple notation is explicitly biproduct matrix notation, so no element reasoning in an arbitrary abelian category is assumed. All other summands vanish because additive functors preserve zero objects; no exactness claim about arbitrary tensor functors is inserted.

Step 2 uses the same three definition statements. B-linearity of composition and tensor, assumed in the item, makes diag(f,f) a chain map and gives naturality with respect to the unitors. Identity and composition hold componentwise. This is an explicit elementary matrix calculation and not a new lemma moved out of the item.

Step 3 uses the cone/shift definition to produce the short exact sequence and its morphism. The cited long-exact theorem really allows arbitrary abelian categories and Z-indexed complexes with degreewise short exactness; the cone sequence is split in every degree. The cited naturality statement supplies the boundary square, not just existence of a long exact sequence. The five-lemma statement applies to the displayed five terms with the middle cone cohomology as third term and all four other vertical maps invertible. I read Stacks homology.tex, Tag 0117 (lemma-long-exact-sequence-cochain, including the functoriality sentence) and Tag 05QB (lemma-five-lemma). There is no boundedness restriction and no unsupported cone-preservation citation.

Step 4 takes exactly the two-sided definition of K-flatness from its cited node. Its inputs are steps 1-3: both fixed-factor tensor maps are conjugate to the cone map by actual natural chain isomorphisms, so each cohomology map is invertible. It does not appeal to a one-sided or module-only K-flat convention. The argument is a few-line consequence and appropriately has no auxiliary node.

Step 5 uses the statement of lem-sfb-derived-monoidal, which explicitly supplies the same ambient hypotheses, the derived bifunctor, computation by replacing either argument by a K-flat resolution, and lax monoidal localization. The identity resolution of the already K-flat P_b therefore computes the canonical comparison even for arbitrary C. I checked this against isIso_μ_scalarCone and tensorScalarConeIso in the source; naturality is the composition of the comparison's naturality and the explicit chain naturality of step 2. I read the current blueprint statement and the project's HasMonoidalDerivedCategory implementation as well. No flatness of C, regularity of b, or symmetry stronger than the stated braiding is required.

Step 6 uses the derived localization definition, and clauses (1) and (2) of lem-weil-pbc-localization-universal-property. The cited node explicitly states both factorization and lifting of natural isomorphisms. I read Stacks categories.tex Tag 04VG (lemma-properties-left-localization), and Mathlib Localization/Predicate.lean:295-364: Stacks supplies the functor factorization, while the existing node correctly supplies the natural transformation lifting from Mathlib. The source and target of the lifted iso are H and the descended cone functor; composing with eta inverse gives exactly the required compatibility after Q. No smallness of a newly constructed index category is assumed.

I checked the B-E return cases: no new statement-only node, relabelling, duplicate, fabricated search, missing non-elementary citation, citation of a node's proof rather than its statement, hidden hypothesis, cycle introduced by a new lemma, wrong coefficient category, SGA route, or unsupported naturality remains. All six steps are below 2000 characters; the non-elementary facts have explicit existing-node citations. The elementary matrix and inverse arguments stay in the proof. Every quote in citations.json was checked against the actual cited statement.

Small cases checked: C=0 gives zero; b=0 gives C ⊕ C[1] with the displayed right-tensor sign; b=1 gives a contractible scalar cone and a contractible cone on every C; in characteristic two all signs coincide; an arbitrary zero divisor b still gives the same two-sided K-flat complex without falsely identifying it with its cokernel. These checks exposed no needed statement repair. The naturality check includes negative degrees and has no boundedness assumption.

## Unfinished work

None in this one-level split. Required server dry run and delivery are performed after writing this report; the tool output is the validation record.
