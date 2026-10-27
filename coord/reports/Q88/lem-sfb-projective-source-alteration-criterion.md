# Q88 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-source-alteration-criterion.json`: existing statement split into six steps; Mathlib searches found no declaration giving the complete item.
- `citations.json`: one entry per citation per step, quoted verbatim from the live dependency statement.
- `report.md`: this report. `prepare.py` is sandbox-only preparation, and `searches.jsonl` is the search command's original log.

New nodes: 0. New Mathlib leaves: 0. All mathematical dependencies already exist.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint id, alteration, generically finite, projective-source and graph-projectivity terminology found no declaration stating all clauses. Chow graph and normalization/function-field declarations are partial results for different hypotheses; they do not attach this item. The upstream projective-space graph API supports an existing permanence node, rather than the full item.

## WANTED

None. All sources used here are present in the read-only literature tree.

## Corrections and route

The statement is unchanged. Its H-projective convention is essential and is supplied by the existing `lem-per-h-projective-permanence`, which preserves the same finite projective-space dimension. No switch to projective bundles or unmentioned normality, smoothness, perfectness or separability is made.

The imported source mentions 0B1C, but a dimension/transcendence-degree theorem is unnecessary: the affine generic-fibre calculation proves the stronger concrete identification with Spec k(X). For the final finite neighbourhood I use the existing proper-finite-fibre theorem (Stacks 02UP), the proper special case of the 02NW conclusion. Properness has already been proved, so this does not change the alteration reduction, and avoids introducing Noetherian bookkeeping not needed by that theorem. No claim is made that proper dominant implies finite globally.

The item's existing blueprint ancestry terminates at null, as `tools/blueprint_refs.py ancestor` reports; the existing exact place and via list are retained. I read its recorded chapter, its unit `sk-thm-sf-ctf-stability`, the current chapter source, and the corresponding three-level constraints in SETUP. This is an auxiliary scheme-theoretic tool in the marked-curve alteration preparation, not the unit's key theorem. No unit realization or chapter record is edited. Off-unit generic tools are declared in split_report.tool_uses.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own stage-1/stage-3 obligations.

## Not duplicates

No new nodes. Before deciding none were needed I searched the whole DAG and imported blueprint for projective source, graph, projective morphism, generic fibre, function field, finite function, and the tags 01WC, 02NW, 01RV and 0C4Q. The existing H-projective permanence and affine fraction-field nodes supply the exact facts required; the existing generic-finite-open and proper-finite-fibre nodes supply the final shrinking theorem. The larger projective-fibre-product closed-model and graph-alteration nodes have additional constructions and are not used to restate the item's conclusion.

## Review by Q88

I read delivery-errors B through E in full and checked each of the six steps against the actual dependency statements, rather than their proofs. I read Stacks morphisms.tex Tag 0C4Q (lemma-projective-permanence), Tag 01WC (lemma-locally-projective-proper), Tag 02NW (lemma-generically-finite) including its qcqs qualifications, and Tag 01RV (lemma-integral-scheme-rational-functions). I also read schemes.tex Tag 01HV (lemma-spec-sheaves), Tag 01JR (lemma-open-fibre-product) and its neighbouring affine tensor-product construction, and more-morphisms.tex Tag 02UP (lemma-proper-finite-fibre-finite-in-neighbourhood). There are no new nodes with additional sources to audit. The algebra and gluing expansion is explicitly agent-written.

Step 1 uses def-kun-projective for a finite-space embedding and lem-per-h-projective-permanence for exactly the same-n embedding after factoring through a separated morphism. I checked Z=X, T=Y, B=Spec k and that b u=a comes from being a k-morphism. No separatedness of u is assumed in this application.

Step 2 uses lem-kun-projective-implies-proper with the embedding from Step 1. Its statement says every projective morphism is proper in this convention. def-weil-proper-morphism then supplies universal closedness and finite type; those assertions are literally in its statement.

Step 3 is elementary: by def-weil-proper-morphism the identity base change is closed; the closed image of the whole source is dense by dominance. def-weil-surjective-morphism identifies equality of that image with surjectivity. No lemma asserting proper plus dominant is used without its argument.

Step 4 uses lem-sc-integral-function-field-affine-fraction on each nonempty affine chart of X and Y; its statement applies to arbitrary integral schemes, not just curves, and gives domains, injective germ maps, and the precise fields of fractions. The generic point of X maps to that of Y by the displayed continuity/density argument. Thus every nonzero denominator from R remains nonzero in C and L. The singleton case r=1 of lem-sbc-finite-affine-tensor-base-change computes the chart fibre over Spec K. This node gives a scheme isomorphism, not merely an equality of section rings. The singleton coproduct is the chart itself by its one coprojection's universal property. lem-weil-pbc-open-immersion-base-change gives open charts; their projections and inverse-image cover show they cover the fibre. lem-sbc-affine-fibre-sections-tensor supplies the explicit c maps to c tensor 1 formula, which the singleton tensor node alone does not state for the first projection. Finally lem-weil-pbc-generic-fibre-localization-domain-irreducible gives precisely the localization/domain assertion. Its domain and injectivity hypotheses have just been verified, and exchanging tensor factors is the usual defining tensor symmetry.

Step 5 uses no unproved generic-fibre dimension assertion. Localization injects into L by the explicit fraction map. As a K-linear subspace of the finite-dimensional K-space L it is finite-dimensional. The cited lem-weil-pbc-finite-dimensional-domain-is-field says exactly that such a domain is a field. The fraction-field node then proves its image is all L: it contains C and inverses of every nonzero element of C. def-pc-scheme-fibre states that the fibre projection is a homeomorphism onto the set-theoretic fibre; hence points of different singleton charts coincide after showing their contracted prime in C is (0). This avoids incorrectly assuming distinct singleton charts glue to one point. One chart exists since the generic point lies above eta. Any nonempty open in a singleton scheme is the whole scheme, giving the scheme-level identification Spec L and its K-structure, rather than just a bijection of spaces. def-weil-affine-spectrum explicitly gives the residue field of the spectrum of a field; def-pc-integral-scheme gives integrality from the domain chart. Dimension zero is the direct prime-chain calculation.

Step 6 uses def-pc-scheme-fibre to translate the singleton scheme fibre into the finite underlying preimage required by lem-trf-proper-finite-fibre-finite-near. I checked that this node has no Noetherian base hypothesis and that properness is already available. Its statement gives a finite restriction over an open neighbourhood of eta. Density follows because eta is generic. The alteration conclusion is then exactly the inline definition in the item.

For edge cases, if X and Y are dimension zero, the argument reduces to a finite extension of fields and one can take the whole target. Purely inseparable finite extensions work because the only field argument is finite dimension, never separability or geometric reducedness. A blow-up of an integral projective variety illustrates why the finite restriction is asserted only on an open. If dominance is absent (for example a constant map P^1 to P^1), only the first proper/H-projective clause is used. If the function-field extension is infinite, the field-subspace argument is not applied; a projection from a product with P^1 illustrates this necessity. Empty schemes are excluded by integrality, so a nonempty affine chart is legitimate.

No proof step exceeds 2000 characters; the longest is the explicit affine-chart argument at 1317 characters. There is no hidden lemma moved into a new node or restatement of the item's clauses. I preserved the prior searches and added only queries actually run through msearch.py, whose hits I read. Rational-map spreading and finite cancellation hits do not state this item. Nothing was compiled, no Lean was written, and all writes are in this sandbox.
