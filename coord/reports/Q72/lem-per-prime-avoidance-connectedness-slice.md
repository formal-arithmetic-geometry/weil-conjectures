# Worker report: lem-per-prime-avoidance-connectedness-slice

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-avoidance-connectedness-slice.json: statement retained verbatim; split into eight steps of simultaneous prime-avoidance slicing. Existing Mathlib searches retained and the sandbox's actually logged follow-up searches retained.
- dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-local-closed-points.json: one new statement-only unsplit lemma. Every nonempty locally closed subset of the punctured spectrum of a Noetherian local ring contains a point closed in the whole puncture. No Mathlib match found.
- citations.json: fourteen entries, one per step/node citation, each quoting the complete statement actually read. This is a sandbox verification artifact.

There are one new node and zero new Mathlib leaves. All the existing algebraic and topological facts cited by the item are Mathlib leaves already present in the DAG.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item tag, punctured Jacobson spectra, closed points in punctures, prime avoidance, and connectedness slicing found no project declaration stating the item or the new auxiliary lemma. The hits for graded prime avoidance, regular local rings, and Hilbert polynomials concern different statements. No upstream master sorry declaration was treated as a proof.

## Wanted literature

None. The required Stacks sources are present locally.

## Faults found and changes made

This resumes an interrupted attempt whose sandbox already contained a split, the auxiliary node, citations, and sixteen logged searches, but no report. I compared that item with the current shared node: its original statement, source, created metadata, chapter, unit, and blueprint ancestry still agree. I retained the earlier proof and search evidence. No statement dispute or correction is needed.

The original item was unsplit and Stacks 0ECR says only that equations can be chosen inductively by prime avoidance. The delivery supplies the induction and the ideal in which to choose every equation. Its elements vanish at previously chosen points in the prescribed locally closed pieces while avoiding every positive-dimensional component prime of the current cut. A dimension upper bound suffices; the proof does not assume equality of successive dimensions, catenarity, or equidimensionality.

During this continuation I made Step 1 cite the spectrum node for the fact that closed subsets are exactly zero loci, rather than taking that fact from the radical-equality node. I also expanded Step 7's finite-closed-cover argument so that its use of irreducibility is explicit. These are citation/completeness repairs, not changes to the statement or route. The second phrasing search for Jacobson localizations is now recorded on the auxiliary node as well, with the missing original-ring Jacobson hypothesis identified.

## Unfinished work

The new closed-point lemma is intentionally unsplit, as required for a new non-Mathlib node. Its proof and dependency decomposition are future work; the item's proof uses only its stated conclusion. There is no unfinished step of the item itself.

## Not duplicates

lem-per-punctured-local-closed-points vs lem-per-prime-avoidance-connectedness-slice: both source entries mention 02J6, but the new node supplies a point closed in the puncture inside an arbitrary locally closed piece; the item constructs e simultaneous equations cutting a different closed subset to the maximal ideal while meeting finitely many pieces. Neither equation construction nor dimension reduction appears in the new node.

lem-per-punctured-local-closed-points vs lem-per-complete-local-connectedness-bound: both mention 02J6 in their sources, but the existing node is a connectedness inequality for a complete local ring and an ideal with a bounded number of generators. It does not assert the closed-point existence statement and is a parent of the item, so citing it for that statement would also risk circularity.

The whole-DAG searches by tags 02J6, 02IM, and 005U found only those two existing nodes. Broader searches for punctured Jacobson spectra and closed points in punctures, and blueprint_refs.py searches for punctured and Jacobson, found no node stating this lemma. I also opened lem-a1-local-spectrum-open-classification: it is restricted to dimension at most one and gives discrete affine punctured opens, not the arbitrary-dimensional closed-point theorem. The support-filtration and purity search hits concern other assertions. blueprint_refs.py ancestor identifies lem-per-artin-gabber-affine-curve as the ancestor, as recorded on both delivered files; the new node's via list prepends this item.

## Review by Q72

I read Stacks algebraization.tex, Tag 0ECR, label lemma-punctured-still-connected, especially the second half of its proof; morphisms.tex, Tag 02J6, label lemma-ubiquity-Jacobson-schemes, case (4); properties.tex, Tag 02IM, label lemma-complement-closed-point-Jacobson, case (1); and the paragraph immediately after topology.tex, Tag 005U, definition-space-jacobson. The tags/tags mapping confirms these identifiers. 0ECR first chooses points closed in the puncture, then cuts the obstruction locus by parameters retaining those points. The completeness assumption belongs to its connectedness theorem, whereas this extracted slicing argument uses only the hypotheses of the item. 02J6(4)/02IM(1), together with 005U's locally closed characterization, gives precisely the new lemma without requiring completeness, excellence, a field, or finite dimension. The new statement introduces its ring, spectrum, puncture, and locally closed subsets, defines local and locally closed inline, and cites the existing Noetherian-ring and spectrum notions. It has no proof or proof dependencies.

I opened the statement of every cited existing node, not merely its proof or source, and checked the steps as follows.

1. lem-weil-pbc-spec-irreducible-closed-subsets-primes explicitly identifies the closed subsets of Spec A with V(I). lem-weil-pbc-zero-locus-eq-iff-radical-eq explicitly states the radical/intersection formula; it identifies the radical ideal recovered from a closed set and reverses inclusion. def-weil-pbc-noetherian-ring says every ideal is finitely generated. The union-of-an-ascending-chain argument then proves stabilization in a few lines; closed subspaces inherit it. This is an elementary deduction from the cited statements, not a new theorem quoted without a node.

2. The new lemma states closed-point existence for every nonempty locally closed subset of U. Each W_j is nonempty by hypothesis and locally closed in U because U minus T is open; the proof writes this subspace calculation. The spectrum node explicitly gives closure{p}=V(p), so closedness of w_j in U gives V(p_j) intersect U={w_j}. Every proper prime lies in the unique maximal ideal, hence V(p_j)={w_j,m}. No closed point of all of X is asserted to lie outside m.

3. The invariant includes both membership in all p_j and dim T_n <= e-n. The spectrum node supplies specialization to m; closedness of T and membership f_i in m keep m in every T_n. def-kun-topological-krull-dimension supplies the chain interpretation used throughout. The induction starts at the actual T with its given dimension, not an equidimensional replacement.

4. lem-sc-noetherian-finite-irreducible-components states precisely finiteness for a topologically Noetherian space, established for T_n in Step 1. Coverage by maximal irreducible closed subsets is justified by bounded chain length, not smuggled into that lemma's statement. The spectrum node supplies component primes. For a positive-dimensional component prime q, q differs from m; if p_j were contained in q, Step 2 forces q=p_j or m, and both alternatives contradict q in T_n and w_j outside T, or positive dimension. This checks the crucial hypothesis of the ensuing prime-avoidance application.

5. The product a times the b_j belongs to the finite intersection J and avoids q because q is prime. The proof explicitly handles the empty product when s=0. This is elementary ideal arithmetic and the definition of prime, so no auxiliary node was created for it.

6. lem-weil-pbc-prime-avoidance says an ideal J contained in none of a finite nonempty list of ideals, all but at most two prime, has an element outside all of them. Here all of the avoided component ideals are prime and Step 5 verifies noncontainment separately for each. When there are no positive-dimensional components, the proof takes zero and does not apply a nonempty-family lemma to an empty family.

7. The dimension node defines dimension as the supremum of lengths of irreducible closed chains. Since T_{n+1} is closed in T_n, its chains are chains in T_n. Irreducibility and the finite component cover put their top member in one component. If that component has positive dimension, it is not contained in the next hypersurface, so appending it lengthens the chain by one. The zero-dimensional case is dealt with separately. This proves the required upper bound directly and is an elementary chain argument. It hides no independent dimension comparison theorem.

8. The spectrum node shows that q distinct from m in a closed local subset creates the strict chain {m} subset V(q). The dimension definition rules this out in T_e. All f_i lie in each p_j by the invariant, giving the retained point in every W_j. This establishes both clauses of the original item.

I tested the new lemma on a field and on a nonzero Artinian local ring: U is empty, so its nonempty-W premise is impossible. For a DVR, U is the singleton generic point, closed in U, so the conclusion holds even though it is not closed in X. For higher-dimensional local spectra, merely choosing an arbitrary closed point of W would not suffice; the assertion deliberately requires closedness in all of U, exactly as 02J6/005U supplies. For the item, e=0 gives T={m} and no equations; s=0 gives J=m and no retention obligations. Redundant equations equal to zero are harmless after all positive-dimensional components have disappeared. Nilpotents and nonreduced rings cause no change because the zero-locus and radical statements apply to every commutative ring.

For Mathlib I reused the logged actual searches in searches.jsonl and inspected the significant candidate source statements. Topology/JacobsonSpace.lean:82,107 gives jacobsonSpace_iff_locallyClosed and nonempty_inter_closedPoints only once JacobsonSpace U is supplied. RingTheory/Jacobson/Ring.lean:215 gives isJacobsonRing_localization only for an originally Jacobson ring, which an arbitrary Noetherian local ring need not be. RingTheory/Spectrum/Prime/LTSeries.lean:33 gives prime-chain insertion below the maximal ideal, not closed-point existence in each prescribed locally closed subset. Thus none is a one-line specialization proving the new node. The item searches additionally returned height-parameter existence without the simultaneous retention condition. Search query text and tool names are copied from executed records, not reconstructed queries; no unavailable service is treated as a negative match.

I checked B through E against the files: the only new node is self-contained, statement-only, sourced by the verified tags, not a restatement of a clause of the item, and not a duplicate found by the whole-DAG/blueprint/Lean searches. All non-elementary steps cite their actual supporting statements, with verbatim quotations in citations.json. The other steps carry short elementary arguments. Every proof step is shorter than 2000 characters. The chapter and unit files are untouched. The unit's Fourier-exactness route and the inherited dualizing/connectedness ancestry are preserved; no SGA source is used. All existing off-unit proof tools are already Mathlib leaves, while the new lemma inherits the item's unit.
