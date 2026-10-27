# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-free-shift-derived-hom.json`: existing statement node, now split; no exact Mathlib match.
- `citations.json`: three verbatim citation entries, one for each step that cites a node.
- `report.md`: this report.

No new nodes and no Mathlib leaves were created. The sandbox had no earlier item, report, or searches at entry. The repository copy's statement, blueprint provenance, source, historical searches and other fields are retained. Six actual new searches are appended from searches.jsonl.

## Attachments

None. Searched the whole project WeilConjectures tree for the exact blueprint id and for DGModule, DgModule, DGAlgebra, DifferentialGraded and differential graded. Only a Koszul-algebra comment appeared; there is no exact project declaration for the item. No Lean files were written and no compiler was run.

## WANTED

None. The Stacks source used here is present locally.

## What was wrong and what changed

The item was a correct statement with no proof. Its unit and chapter were read, followed by the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` statement and proof. Its precise supporting provenance remains the inherited 09R3 free-shift reduction. The blueprint ancestor command reports None for this existing created-node chain; its original null ancestor is preserved rather than inventing a blueprint identifier.

The essential localization comparison already exists as `lem-sfb-dg-homotopically-projective-hom-derived`. I reused its statement and proved the rank-one hypothesis directly. The alternative existing `lem-sfb-dg-free-module-hom-cohomology` is the shift-reformulated rank-one result itself; citing it would merely transfer the item into a near-identical clause, so it is not the proof used here. No new lemma is needed for the elementary evaluation calculation.

DAG searches covered 09K1, 09KY, 09KM, K-projective and differential graded modules; the blueprint index was searched for differential graded, 09K1 and homotopically projective. The latest blueprint was searched for the free-shift/cohomology formula. No imported blueprint node states this general-DG-algebra comparison. There are no new-node pairs requiring a Not duplicates section.

Mathlib searches were actually run through the required msearch command: LeanFinder twice with different phrasings, LeanSearch, Loogle, and two source greps. All six succeeded. Loogle finds `CochainComplex.IsKProjective.Qh_map_bijective`, whose source was read at Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean:43. LeanSearch and the second LeanFinder find `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`, read at Mathlib/Algebra/Homology/HomotopyCategory/HomComplexCohomology.lean:170. These are for complexes in a fixed category, not modules with a differential satisfying the Leibniz rule over a general DG algebra with nonzero differential. The latter cannot be substituted into those declarations in one line. The DGModule/DGAlgebra grep found no declarations. All queries and top hits are in searches.jsonl; no unavailable service was presented as a negative result.

## What could not be finished

Nothing remains in the requested one-level split. The existing comparison theorem remains an unsplit dependency, which is exactly the stage-1 contract; this delivery does not edit or claim to prove it.

## Review by Q16

I read Stacks dga.tex Tag 09K1 (`lemma-hom-from-shift-free`), the shift definition (`definition-shift`), the mapping-complex conventions (`section-hom-complexes`), Tag 09KM (`lemma-property-P-K-projective`) and Tag 09KY (`lemma-hom-derived`, part (1) and its proof). The statement agrees with these sources: right DG modules over an associative unital DG algebra over Z, the shift differential (-1)^k d and unchanged right action, arbitrary integer k, and no boundedness, flatness or countability assumption. I left the statement unchanged. There are no new-node statements to review.

Step 1 cites the existing comparison node specifically for its definition of the mapping complex: graded right-linear maps with differential d_N f - (-1)^r f d_P. I opened its statement and verified that exact convention. Evaluation at 1 and inverse x -> (a -> xa) are written explicitly. The derivation rule gives d(1)=0 without dividing by 2. In degree r, the two d_A(a) terms cancel because r-k and r+k have the same parity. Thus the calculation is valid for noncommutative DG algebras with nonzero differential; it does not silently assume an ordinary ring. This is a direct substitution into the definition, not an uncited theorem.

Step 2 uses the same node's explicit definition Hom_K=H^0 of the mapping complex and its homotopy convention. I checked that it gives exactly the quotient needed. A boundary d(y) in degree -k is realized by the displayed homotopy s(a)=ya, of degree -1. Conversely evaluating any homotopy at 1 gives precisely d(s(1)). These calculations prove the cycle and boundary identifications rather than quoting the desired derived-category clause.

Step 3 invokes the comparison node's actual theorem: localization is bijective on morphisms out of any homotopically projective DG module. Its hypothesis is that the entire internal Hom complex into every acyclic N is acyclic. Step 1 checks every degree, giving cohomology H^{r-k}(N)=0; checking only H^0 would not suffice for that stated hypothesis. The theorem has no additional freeness or size restriction beyond the ambient convention. Surjectivity supplies a DG-map representative, injectivity supplies the boundary criterion, and sums of representatives give addition in the additive localization. This is the one non-elementary step and it cites the existing theorem rather than a new restatement of the item.

Step 4 uses no theorem: composition on representatives gives (hf)(1)=h(f(1)), and a DG map preserves cycles and boundaries. This is the claimed naturality formula, with the correct degree -k, written out rather than asserted by transport.

For E1-E7 I checked k=0, k=1, k=-1, M=0, the zero unital algebra, an algebra concentrated in degree 0, and characteristic 2. At k=1 the generator is in degree -1 and homotopies in degree -2, so the signs and indices agree; the parity cancellation still holds in characteristic 2. For A=0 the unit and unital action force every module to be zero. No step needs an affine hypothesis, a bounded resolution, flatness, or commutativity. No statement dispute or source error arose. Each proof step is under 700 characters, so no long step conceals an additional lemma. The only changes needed were adding the proof, its existing dependency, actual searches, and the split record. The source citations are checked verbatim in citations.json. No SGA reference or enhanced-localization replacement route is used.
