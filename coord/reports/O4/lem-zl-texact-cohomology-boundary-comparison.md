# Stage-1 report: lem-zl-texact-cohomology-boundary-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-texact-cohomology-boundary-comparison.json`: statement, split into six steps; no Mathlib match. The statement and all inherited metadata and searches are retained. Fresh searches from this sandbox are appended.
- `citations.json`: nine entries, one per cited node per step, copied verbatim from its current statement.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log; `write_split.py` is a sandbox-only writing helper.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record is changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, t-exact terminology, cohomology comparisons, and boundary comparisons. The project has t-exact truncation comparisons and compatibility with the boundary of the *truncation* triangle in `WeilConjectures/Mathlib/CategoryTheory/Triangulated/TStructure/SpectralObject.lean` (notably `eTruncGEδLT_comm`, lines 241–278). This is not the requested heart-valued comparison for an arbitrary distinguished triangle. `TStructure/Homology.lean` constructs the cohomological functor, but does not state this item's comparison. There is no exact attachment claim.

## WANTED

None. The BBD PDF is present and was read locally.

## Problems and changes

No statement dispute or correction. The input was an unsplit generic comparison extracted from BBD, with an empty proof. The six steps now construct the comparison explicitly and calculate its boundary square; the proof does not silently assume that natural truncation comparisons already commute with arbitrary cohomology boundaries.

The item defines cohomology by `H^r(M)=H^0(M[r])`, as the cited heart lemma does. With this convention the proof needs neither a new lemma commuting truncations with shifts nor a separate lemma asserting shift compatibility of the degree-zero comparison. All shift compatibility is computed from the **given** natural and coherent comparisons sigma. Step 4 writes the shift associator and its coherence equation rather than treating associators as equalities. Step 5 is the actual four-line boundary calculation. No new node is a restatement of a clause of the item.

## Searches and duplicate review

The initial sandbox contained only dispatcher marker files, with no prior node, report, or searches to recover. The repository's item and its inherited Q45 searches have been retained. The new searches were run only through `batch2/msearch.py`, and their exact query text and actual command log records are appended to `mathlib_searches`.

The first semantic query concerned a t-exact functor and heart cohomology. The second concerned natural transformations of homological functors with shift comparisons. LeanFinder found `homologySequenceδ_naturality`, zero-composition lemmas, and general triangulated/homological-functor infrastructure. LeanSearch also found comparisons for *short-complex homology* and images of *spectral objects*. Loogle's query combining `homologySequenceδ` and `NatTrans` returned zero hits. The two logged Mathlib greps searched boundary comparisons in `CategoryTheory/Triangulated` and then t-exact/truncation infrastructure in `CategoryTheory/Triangulated/TStructure`. These do not supply the whole item. Read `HomologicalFunctor.lean` lines 172–200: `homologySequenceδ` is the shifted third arrow, its naturality is for one fixed functor and triangle morphisms, and `comp_homologySequenceδ` means a composite is zero, not comparison between functors. The spectral-object source concerns a different category of objects. Thus no exact or one-line Mathlib specialization was identified.

Searched the whole DAG and blueprint for cohomology-boundary and t-exact comparison formulations with `rg` and `tools/blueprint_refs.py search`, and obtained the ancestor with `tools/blueprint_refs.py ancestor`. The fixed-pair cohomology node has additional finite-field and equivariant data and is not the abstract arbitrary-triangle assertion; the coefficient-stage descent node concerns stage transitions, not arbitrary-triangle boundaries; the Kummer coefficient-base-change hit concerns tensoring one particular coefficient sequence. None is needed as a new dependency or is an exact duplicate of this item. Reused the existing generic truncation-comparison and heart lemmas.

## Not duplicates

No new nodes; no new/existing pairs to justify.

## Review by O4

I read BBD Proposition 1.3.3 and Theorem 1.3.6 in the local PDF, printed pp. 29–31, for canonical adjunction truncations, the full heart and cohomological `H^0`. I also read 1.3.16–1.3.17, printed pp. 36–37, for t-exact functors and their restriction to hearts, and 1.1.1, printed p. 18, for the iterated shift convention. This is an agent-written formal consequence of those constructions, not a claim that BBD prints this comparison theorem. There is no Stacks tag for this abstract t-structure form; the existing t-structure node explicitly records why the complex-truncation tags 0118 and 08J5 have a different scope. No SGA source is used.

For step 1 I opened the **statements** of `def-weil-t-structure`, `lem-pod-texact-truncation-comparison`, and `lem-weil-heart-short-exact-triangles`. The first defines the heart as the intersection, so preservation of both halves makes the restriction meaningful. The second states two natural comparison isomorphisms for exactly the bounded, exact, degreewise t-exact hypotheses we have. The third explicitly defines `H^0` in the order lower-after-upper truncation. The written composite consequently has the required source and target. Fullness supplies heart morphisms and inverses without an extra lemma. For step 2 the truncation lemma actually states object-naturality of both isomorphisms: applying lower truncation to one square and composing the two squares proves naturality of e. No compatibility with boundaries is borrowed from it.

For step 3 the same heart statement explicitly says `H^i(K)=H^0(K[i])`. Evaluating e at `M[r]` and then applying `H^0` to sigma is therefore the stipulated cohomology comparison. Its naturality is the substitution into step 2 at `f[r]` and the naturality equation of the supplied sigma. It is not a new cohomology-identification theorem.

For step 4 I checked the exact-functor clause of `def-weil-triangulated-category`: the shifted third arrow is the one used when mapping a triangle. The two equations used beyond this are respectively the assumed shift coherence and naturality of sigma, written with the associator `(A[1])[r] -> A[r+1]`. Their substitution gives the identity on shifted third arrows. This is a two-equation calculation from hypotheses, not an unprovided result. In step 5 the cited heart statement (5) gives the cohomological functor and standard long exact sequence. The boundary's definition is `H^0` of the shifted third arrow, verified also against Mathlib's `homologySequenceδ` definition at lines 172–178. The four displayed equalities follow in order from the definition of c and delta, step 2, step 4, and preservation of composition. In particular no unjustified assertion that comparisons “transport boundaries” remains.

For step 6 I read the TR3 clause of the triangulated-category statement: a triangle morphism satisfies `a[1] w = w' d`. Shifting that equality and applying `H^0` gives the boundary naturality face. Applying P and naturality of sigma gives its target counterpart; step 3 supplies the two comparison faces. These are exactly the faces needed for naturality of the squares in the statement. All quotes in `citations.json` are actual substrings of those cited statements, including clause (5) for steps 5–6 and TR3 for step 6.

I tested degree 0, degree -1, arbitrary negative shifts, the identity functor with its standard coherence, zero objects and zero boundaries, and the split distinguished triangle. The formula always uses `r+1`, with the associator in the forward direction. No bound on r, nonzero object assumption, heart exactness theorem, coefficient hypothesis, or triangulation of Weil pairs is used. A general nonzero third arrow is retained throughout the calculation, so the proof is not limited to the vacuous split case. The sign comes only from the supplied exact-functor shift structure; no rotation of the triangle is made and no unaccounted `(-1)^r` is inserted.

I reviewed delivery-errors B–E point by point. B: no new nodes, the item remains self-contained, and new searches are logged exactly as run. C: every cited statement was read; the only non-elementary construction is the cited truncation comparison; all other steps are explicit compositions, naturality equations or definitions. D: no content has been moved into a renamed clause. E: the categories and all hypotheses remain those of the statement, and the essential boundary calculation is written out. Step lengths are 939, 384, 651, 819, 911, and 686 characters, all below 2000; none hides an independent lemma. The two general tools are declared in `split_report.tool_uses` because they come from other units. The unit and chapter route remain the existing coefficient long-exact-sequence route of open–closed reduction.

## Unfinished work

None in this one-level split. Existing cited nodes remain owned by their existing records. No Lean file was written and no compiler, Lake, build, local DAG check, local split review, repository write or direct git command was run. Required server validation and push follow via the unmodified delivery tool.
