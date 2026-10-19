# Stage-1 report: lem-zl-bertini-independent-functions

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-independent-functions.json`: item, split in six steps; no exact Mathlib match. The statement and its six statement dependencies are unchanged.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-finite-type-fibre-component-lower-bound.json`: new statement-only lemma, unsplit, no exact Mathlib match. This is the general affine rational closed-fibre component bound of Stacks Tag 0B2L (2)(a).
- `citations.json`: twelve entries, one for each cited node in each item step, quoting its statement verbatim.
- `searches.jsonl`: actual msearch output records, including two formulations of both mathematical questions. The new node records nine searches and the item retains its imported searches and adds four searches from this sandbox. `write_split.py` is a sandbox-only preparation script.

One new node, zero new Mathlib leaves. Existing Mathlib leaves are reused.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item's exact blueprint id, algebraic independence, independent functions, and Bertini. The Bertini file concerns the ancestor curve theorem, not this algebraic assertion. GenericIrreducibility concerns different field-extension statements. No exact declaration for either this item or the new fibre-bound lemma was found. No Lean was written or compiled.

## WANTED

None. Both sources are present locally.

## Problems found and changes

The item was a statement-only child sourced to Tag 0G4E. Its statement is faithful to the local Stacks source, including arbitrary (possibly finite) base field, existence rather than generality of the constants, and existence of just one component of the specified dimension. No STATEMENT-DISPUTED correction is needed.

The source proof selects a closed point on the relevant component outside the other components. This split instead uses the component form of its cited dimension inequality directly; this avoids needing a separate Jacobson closed-point selection theorem. The map and the same special fibre are exactly those in the source. The general component theorem, rather than the whole conclusion or a clause of the item, is the only new node. The quotient isomorphism and the nonzero-kernel dimension drop are explicit elementary steps, not additional nodes.

I did not use the superficially related `lem-wf-affine-dimension-drop` as a black box: its recorded Lean declaration covers the domain clause only. Step 4 proves the required prime-chain bound itself, from the definition of ring dimension.

The generic finiteness-of-dimension tool `lem-weil-pbc-finite-type-domain-dimension-trdeg` is declared in `split_report.tool_uses`. It supplies only finiteness in Step 2; no unit-level proof route is replaced. The ancestry remains the current blueprint's paragraph 3 of `lem-zl-bertini-finite-cover-curve`, through `lem-zl-bertini-irreducible-member`.

## Unfinished work

The new general fibre component theorem is intentionally left statement-only, as required for a one-level split. The argument supporting its truth and its source specialization is checked below. Nothing else is left unfinished in the item's natural-language proof.

## Not duplicates

The whole DAG was searched for Tag 0B2L and its Stacks label; neither occurred before this creation. Blueprint searches for `0B2L`, `dimension fibres`, `fibre dimension`, `fibre component`, `fiber component`, `closed fibre`, and `minimal prime` found no existing statement of this lower bound. Searches for `algebraically independent`, `independent functions`, and `generic linear` found no blueprint equivalent of the item. Keyword scans of all node statements and the project Lean files were also read. Nearby statements differ as follows:

- lem-zl-finite-type-fibre-component-lower-bound vs lem-sbc-flat-fibre-component-dimension-specialization: that statement assumes flatness and compares local dimensions along a specialization; the new lemma assumes finite type over a field and bounds each closed-fibre component using the image dimension, without flatness.
- lem-zl-finite-type-fibre-component-lower-bound vs lem-sbc-flat-fibre-component-dimension-specialization-open: that statement gives a constant-dimension neighbourhood under flatness; it gives no lower bound in terms of source and image dimensions.
- lem-zl-finite-type-fibre-component-lower-bound vs lem-trf-flat-family-generic-dimension-bound: that statement has flatness and an upper bound from the generic fibre, not the componentwise lower bound needed here.
- lem-zl-finite-type-fibre-component-lower-bound vs lem-weil-pbc-fibre-dimension-bounded-open-upstairs: that statement gives openness of a local upper bound near a given point; it neither compares source and image dimensions nor bounds all components from below.
- lem-zl-finite-type-fibre-component-lower-bound vs lem-zl-bertini-independent-functions: the new lemma concerns an arbitrary algebra map and arbitrary rational closed fibre, has no chosen g_i, no polynomial family or coefficients to choose, and no independence conclusion. It is the dimension-theoretic input used in the contradiction, not a renamed clause.

## Review by NV

I read the local Stacks proof of Tag 0G4E (`more-morphisms.tex`, `lemma-algebraically-independent`, lines 9011--9052) for the item. I read Tag 0B2L (`varieties.tex`, `lemma-dimension-fibres-locally-algebraic`, starting at line 3953) for the new node, together with the supporting local-dimension descriptions in Tag 0A21 (`lemma-dimension-locally-algebraic`). The latter says that local dimension is the maximum dimension of the irreducible components through the point. For the new node take X=Spec C, Y=Spec B. Since C is a domain, X is irreducible, and its generic point maps to P=ker(phi); hence the closure of the image is V(P)=Spec(B/P). At the generic point of a chosen component W of the rational closed fibre, the only fibre component through that point is W, so its local dimension is dim W. Tag 0B2L (2)(a) now gives precisely the new inequality. The fibre is Spec(C/J) because B/m=k as a k-algebra. This also explains why no algebraic-closedness, separability, flatness, or rational point of Spec C is required. The source's inequality is a substantive theorem and is therefore a new cited node; this reasoning is recorded in the report rather than placed as a proof inside the unsplit child.

I opened and read every statement cited in the item's six steps:

1. Step 1 takes finite generation from `def-weil-pbc-finite-type-algebra`, evaluation and its universal property from `def-weil-pbc-mv-polynomial-ring`, and the absence-of-polynomial-relations meaning of independence from `def-kun-transcendence-degree`. The coefficient embeddings and leading-monomial argument are written explicitly; no dominance or function-field theorem is smuggled in.
2. Step 2 takes finiteness of dim A from `lem-weil-pbc-finite-type-domain-dimension-trdeg`; A satisfies every hypothesis (field k, finite type, domain). `lem-wf-affine-noetherian-components` explicitly says A is Noetherian, and applies also to k itself. `lem-sf-noetherian-polynomial-dimension` explicitly gives dim R[x_i]=dim R+n for a finite variable set over any Noetherian ring, so it applies to A and k. I also read the installed Mathlib polynomial dimension declaration at `Mathlib/RingTheory/KrullDimension/Polynomial.lean:120`.
3. Step 3 takes affine contravariance from `def-weil-affine-spectrum`, maximal irreducible subsets from `def-weil-irreducible-components`, and dimension by chains in the subspace topology from `def-kun-topological-krull-dimension`. The equality of ideals uses the displayed identity h-g1; the quotient maps are explicitly specified and inverse on constants and variables. This proves the fibre identification, preserves exactly the component of the hypothesis, and checks rationality downstairs without assuming a rational point upstairs.
4. Step 4 uses exactly the prime-chain definition in `def-weil-pbc-krull-dimension-ring`. Every lifted prime contains a nonzero kernel ideal, so the prepended zero prime is strictly smaller. No external dimension-drop theorem is required. The domain and nonzero hypotheses, finiteness from Step 2, and the fact that P is proper were checked before subtracting one.
5. Step 5 cites the new lemma's whole componentwise lower bound. Its statement actually names both finite type k-algebras, the domain C, arbitrary algebra homomorphism, rational maximal ideal, and the extended ideal J. Steps 1 and 3 verify all those hypotheses. The selected component has exactly d-2, while the source-image calculation forces at least d-1. This is a contradiction between finite integers.
6. Step 6 uses the independence definition again. Its constants exist over every field, and their sum is g2; injectivity already proved gives all n+2 elements, rather than independence of a proper subfamily.

For delivery-errors B I checked that the only new node is self-contained, has empty proof and proof dependencies, names the correct source tag and label, introduces all objects, and records only executed searches. The definitions it cites do define the stated notions. The JSON uses single TeX escapes after parsing. Its ancestry is the ancestor printed by `blueprint_refs.py` with both intervening items in `via`. No Mathlib leaf is claimed: the semantic hits were independence definitions, finite fibre/Jacobson facts, or inertia degrees; the potentially relevant height inequality needs a separate dimension formula and is not a one-line specialization of the new theorem.

For C I checked statement support as detailed above and wrote the exact statement quotations in `citations.json`. The only non-elementary item steps are the existing dimension calculation and the new general fibre bound; both have explicit cited statements. The child has only definition dependencies, so it cannot create a cycle back to the item. The off-unit finiteness tool is declared.

For D I checked that the actual choice of coefficients, map, special fibre, dimension drop, contradiction and final independence all remain in the item's steps. The child is a reusable theorem on arbitrary algebra maps, and does not state any clause of the item. No statement is cited after being proved circularly.

For E I checked small cases: n=2 and A=k[u,v], g1=u, g2=v, where the special fibre is a point and the dimensions are 4 and 4; arbitrary extra g_i, which disappear after x_i=0 for i>=2; d<2, where the component hypothesis cannot hold; one or both g1,g2=0, which cannot yield a component of dimension d-2 in a finite type domain. Finite fields and positive characteristic need no change because only 0 and 1 are chosen. For the new lemma I checked an isomorphism (bound 0), a projection of affine spaces (equality), a constant map (image dimension 0 and nonempty fibre the whole source), and a rational maximal ideal outside the image (empty fibre, vacuous assertion). These also test the sign and the essential use of image dimension rather than target dimension.

All six proof steps are shorter than 2000 characters. No SGA source, Lean write, build, shared-project mutation, launcher mutation, or worker git command was used.
