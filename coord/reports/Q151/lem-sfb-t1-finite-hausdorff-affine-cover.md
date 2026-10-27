# Stage-1 report: lem-sfb-t1-finite-hausdorff-affine-cover

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-t1-finite-hausdorff-affine-cover.json`: statement, split; unchanged statement, four proof steps, five existing dependencies, no whole-item Mathlib match.
- `citations.json`: a verbatim statement excerpt for each node used in each step.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

No new nodes and no new Mathlib leaves. The sandbox contained only dispatcher markers before this attempt; no earlier split or report existed to resume. The source node's earlier searches were retained, read and supplemented with the five actual queries in the local log, including two semantic phrasings. Returned finite-cover/compactness declarations were checked against Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:78–89. Those declarations do not assert the T1-to-Hausdorff conclusion, so the whole item is not a Mathlib leaf.

## Attachments

None. Searching the project source for the blueprint tag, T1 affine statements and Hausdorff statements found no declaration of the whole item. SpectralSpace.totallySeparatedSpace in WeilConjectures/Topology/SpectralSpace/Constructible.lean:78 proves only a topology implication, not the finite covering and maximal-prime clauses. It is not an attachment for this item.

## WANTED

None. All source passages used are present locally.

## What needed repair

The imported node was statement-only, not a completed split. Its statement is correct as written, including the empty scheme and omission of quasi-separatedness. The proof now makes explicit the closed-singleton argument that turns chart primes into maximal ideals, rather than merely invoking the informal dimension-zero wording of 0CKV.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor returns None for this chain. The precise inherited place and via chain are retained. Whole-blueprint searches for Hausdorff, finite affine, zero-dimensional, 04MG and 0CKV found no alternate blueprint statement of this lemma. Existing DAG statements for finite affine covers, prime closures, maximal ideals and profinite spectra were reused. No chapter or unit route was changed, and this node is not the unit's key statement, so no unit realization was edited. coord/dag-sync.md named in the inherited standing brief is absent; the current prompt identifies this read-only shared clone as authoritative.

## Not duplicates

No new nodes. In particular, the ring-topology assertion is already lem-weil-pbc-zero-dimensional-spectrum-profinite and the cover assertion is already lem-weil-pbc-qcqs-finite-affine-open-cover. The former is a generic tool from another unit, declared in split_report.tool_uses; the latter and the other two theorem citations are Mathlib leaves. No existing statement is restated as a child.

## Review by Q151

I read Properties Tag 0CKV, lemma-dimension-zero, its opening affine-chart paragraph and final finite-cover paragraph. I also read Algebra Tag 04MG, lemma-ring-with-only-minimal-primes, especially condition (6) and its implication to compact Hausdorffness; Tag 00ES, lemma-irreducible, part (1) and its proof; and Schemes Tag 01IT, lemma-basis-affine-opens. I read the existing maximal-ideal node and its source reference to 00E0, and the quoted ideal-existence assertion. No new node requires a separate source review. These arguments follow the same local affine-spectrum route as the source, without claiming the whole non-quasi-separated scheme is Hausdorff or affine.

In step 1, I opened lem-weil-pbc-qcqs-finite-affine-open-cover and checked that its *statement*, despite the historical qcqs name, requires only a quasi-compact scheme. It supplies the finite affine opens of this X. I read def-pc-scheme: affine means isomorphic to a spectrum of a commutative ring, so the selected A_i and h_i require no new existence theorem. The finite-cover lemma has the exact Mathlib finite-union result, read at QuasiCompact.lean:85–89. The case X empty can be handled immediately by an empty family, independent of any chosen cover.

Step 2 is solely the subspace definition: intersect the ambient closed singleton with U_i. A scheme isomorphism and its inverse induce continuous maps, hence a homeomorphism; this identifies closed singletons in the chosen spectrum. No implication from T1 to Hausdorff for arbitrary spaces is used.

In step 3, I opened lem-weil-pbc-spec-irreducible-closed-subsets-primes and checked that clause (1) gives exactly closure of {p} = V(p), including the membership criterion by ideal containment. Step 2 makes that closure a singleton. I opened lem-weil-pbc-proper-ideal-contained-in-maximal and checked its last clause applies to *every prime ideal*, with no finite-generation, domain, Noetherian, reducedness or nonzero-ring assumption. It supplies m containing p. The short written maximal-implies-prime argument uses 1 = c + ra and b = cb + rab. Thus m is a point of V(p), so m = p. This is elementary assembly of the two cited statements, not a new theorem or a hidden invocation of an uncited prime-ideal existence result.

In step 4, I read the complete statement of lem-weil-pbc-zero-dimensional-spectrum-profinite: its sole ring hypothesis is that all primes are maximal, exactly step 3, and its conclusion explicitly includes compact Hausdorffness in the Zariski topology. It applies to every A_i. The homeomorphism carries any open cover to an open cover and disjoint neighborhoods back to disjoint neighborhoods, giving the two required properties in U_i's subspace topology. The additional total disconnectedness in that cited statement is harmless and unused. The generic 04MG tool supplies no replacement for any six-functor argument of the unit. It has no dependency on this item or on the stronger qcqs-affineness parent.

For B1–B10 of the delivery errors, there are no new unsplit statements or new notion leaves; all cited definitions are present, TeX is singly escaped after JSON decoding, the Stacks tags and labels were checked in tags/tags, and no exact project declaration was mistaken for an attachment. For C1–C8, each non-elementary fact has its own existing cited statement, all five quotes were tested as literal substrings of those statements, and proof_deps is exactly the union of uses. Elementary subspace and ideal calculations are written out. The off-unit topology lemma is disclosed as a generic tool. For D1–D5, the proof carries the finite-cover choice, point-to-prime argument and transport, rather than moving this item or one of its clauses to new nodes. For E1–E7, I checked every applied hypothesis and all identifications; the only transport is a genuine homeomorphism, whose effect on covers and neighborhoods is spelled out. No source or statement correction was needed.

The empty scheme and zero ring cause no maximal-ideal existence problem, since step 3 is quantified over a prime and is vacuous when there is none. Spec(k[epsilon]/epsilon^2) tests nonreduced charts: its unique prime is maximal and the chart is compact Hausdorff. Infinite Boolean spectra test the non-Noetherian/non-discrete case: compact Hausdorff does not imply finite or discrete, and no such assertion is made. The proof never uses intersections of affine opens, so it has no concealed quasi-separatedness assumption. All four steps are below 2000 characters (the entire proof text is 1753 characters).

## What remains unfinished

Nothing mathematical for this one-level split. Validation and direct delivery use the prescribed server tools; their final result is recorded by the delivery process.
