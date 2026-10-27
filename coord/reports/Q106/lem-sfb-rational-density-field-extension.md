# Q106 — lem-sfb-rational-density-field-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-density-field-extension.json`: item, statement, split. No new nodes and no Mathlib leaves. Retained the statement, its statement dependencies, source, creation data and blueprint ancestry; supplied five proof steps, exact proof dependencies and an agent proof-origin record.
- `citations.json`: one verbatim quotation of the cited node statement for each proof-step citation.
- `report.md`: this report. The search command also produced `searches.jsonl` in this sandbox.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and rational-density terminology. `AlgebraicGeometry.Scheme.Hom.denseRange_baseChangeFieldPoint` in `AlgebraicGeometry/DensePoints.lean` requires a smooth scheme over a separably closed field and uses the whole family of rational points; it does not state the present item with its arbitrary field and specified dense subset. Its helper about uniqueness over a rational point is only a partial result, not an attachment of this item.

## WANTED

None. The actual proof source is present locally and was read. I did not rely on an unavailable BLR PDF or any SGA source.

## Audit and source

The item is true as written. I read EGA IV_3, Corollaire 11.10.7, printed p.172 (PDF text extracted together with 11.10.5–11.10.8). It applies to an arbitrary scheme X over a field and a family of geometrically reduced source schemes, without finiteness restrictions. Taking the sources to be Spec(k) gives the claim. The reduced closure in that corollary is important: for nonreduced X, topological density does not imply injectivity of evaluation on functions. The delivered proof implements the corollary by affine coefficient algebra instead of creating a new lemma that restates it.

I read the exact statements of every cited node, and Stacks `algebra.tex`, Tag 00E0 (`lemma-Zariski-topology`), together with `schemes.tex`, Tags 01I4 (`lemma-fibre-product-affine-schemes`) and 01JR (`lemma-open-fibre-product`). The source statements supply the affine fibre product and the radical/intersection-of-primes formula. The tensor universal property and the scalar-extension common-kernel result are existing nodes. The latter is already split and in this item's unit; its statement explicitly allows arbitrary index sets and arbitrary-dimensional vector spaces. Its coefficient proof was also read, but the delivered item uses only its statement.

I searched the whole DAG and blueprint for rational-point density, scalar extension, universal schematic density and tensor coefficient statements. `blueprint_refs.py ancestor` returns None: this long chain of created nodes has no imported blueprint ancestor. The inherited explicit BLR clause in `blueprint.from.place` is preserved. I read the latest blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the DAG's chapter and unit records; this is a generic geometric input below that unit, not a replacement of its six-functor route. `cor-pc-dense-points-curves-sections` is restricted to smooth schemes over separably closed fields and includes further assertions, so is not the same statement. No `same_as` entry was warranted. No unit realization fields were changed because this is not a unit key node.

## Not duplicates

No new nodes. In particular the existing `lem-sfb-common-linear-kernel-field-extension` is reused instead of recreating its coefficient-basis result. `lem-sfb-dense-rational-closed-subscheme-descent` assumes finite type and concerns descent of a given reduced closed subscheme; `lem-sfb-separable-point-closure-universal-density` assumes locally finite type and a Galois-stable family over a separable closure. Neither supplies the unrestricted item, and neither is cloned.

## Mathlib searches

Preserved the five actual searches inherited with the live item and read their results. Ran five additional searches through the mandated Q106 search command: LeanFinder with two concept phrasings, Loogle, grep under AlgebraicGeometry, and LeanSearch. Read all returned hits. The results concern dominance, domains of rational maps, algebraic base-change properties or elliptic-curve point maps, not density of an arbitrary specified rational-point family after scalar extension. The logged query strings are copied exactly into the item's search records. No unavailable service was interpreted as an empty search and no new node needs additional searches.

## Review by Q106

I checked B–E against the actual node statements and the source text. There are no new statements requiring separate small-case tests or new definition dependencies. The existing statement remains unchanged, with every object introduced and every notion in its statement dependencies. All steps are below 2000 characters; their lengths are 891, 573, 452, 657 and 942 characters. There is no hidden comparison theorem or standard argument left inside a long step.

Step 1 uses the definition of rational point to get a section and its induced point; affine spectrum to identify it with a k-algebra map; affine-chart-base-change-iso to identify the inverse-image chart with Spec(L tensor A); and algebra-tensor-pushout-universal-property to give the induced evaluation formula. I checked that the chart lemma permits all schemes and zero rings and specifies the two projection maps. Its order of tensor factors is handled by the explicit swap isomorphism and its inverse; there is no unproved identification with the other factor convention. Restriction of density to an open subset is written out. This is a generic off-unit chart lemma and is declared in split_report.tool_uses; it does not replace the unit's proof route.

Step 2 uses precisely the open/nonvanishing assertion in basic-open-function and the radical/intersection-of-primes formula in zero-locus-eq-iff-radical-eq. The application is I=(0), not a reducedness claim. The field codomain kills nilpotents, giving the reverse inclusion. In particular A=k[epsilon]/(epsilon squared) with its unique rational point has evaluation kernel (epsilon), not zero; the proof retains this kernel and works. I explicitly ruled out the tempting false assertion that density forces all vanishing functions to be zero.

Step 3 uses the statement of common-linear-kernel-field-extension, applied to V=A as a k-vector space and all evaluations indexed by E. Its common kernel is exactly K from step 2; its scalar extension is exactly the map from step 1. No finite-dimensionality or finiteness of E, D, or L/k is assumed. The conclusion is a finite linear combination because it is membership in a linear span, not an infinite product or sum.

Step 4 cites the actual multiplication formula in algebra-tensor-pushout-universal-property. The remaining finite-sum nilpotence argument is elementary and is fully written: exponent 1+sum(n_i-1), distributive expansion and the pigeonhole count. This needs commutativity, available for A tensor L, but no characteristic assumption and no bound on the nilradical. Even an algebra with arbitrarily large nilpotence orders causes no problem, since each one function uses finitely many summands. The empty sum is treated separately. I did not create an elementary nilpotence node.

Step 5 uses only the affine spectrum's Zariski topology and the preceding steps. A closed set containing each evaluation prime forces each member of its ideal into all evaluation kernels; it is nilpotent by steps 3–4 and hence in every prime by repeated primality. Thus every such closed set is the whole affine chart. Passing to the affine open cover is explicitly a test against a nonempty open. There is no assumption that X is affine or quasi-compact and no need for intersections of affine opens to be affine. The empty scheme and empty family cases are checked explicitly. Nonseparated schemes, reducible schemes and inseparable or infinite field extensions cause no change to any cited hypothesis.

Each entry of citations.json quotes the cited node's complete statement verbatim, so the cited clause can be checked without relying on that node's proof. proof_deps is exactly the union of the uses lists. No cycle is introduced: the cited algebra and affine interface nodes do not depend on this item. The proof creates no lemma that is a restatement of a clause of the item.

## Unfinished work

None in the stage-1 split. Existing dependencies keep their own stage status; this delivery does not claim Lean proofs for them or write any Lean. Required server dry-run results and the delivery outcome are recorded by deliver.py.
