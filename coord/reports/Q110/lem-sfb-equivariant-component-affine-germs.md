# Stage-1 report: lem-sfb-equivariant-component-affine-germs

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-component-affine-germs.json: the assigned statement, unchanged, with a complete seven-step split; no Mathlib match for the whole conjunction.
- citations.json: fifteen entries, one for every step/node citation, quoting the cited statement verbatim.
- report.md: this report. searches.jsonl is maintained by the required search command.

New nodes: 0. New Mathlib leaves: 0. The existing DAG supplies every non-elementary input; creating separate equivariance or generic-map nodes would merely extract short calculations from the item.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for equivariant/component/affine/germ terminology. AffineTorsorEquivariantAlgebra.lean constructs an equalizer algebra for a split torsor; it does not give this item's product of varying component domains or its generic residue-map comparison. FunctionField.lean and FunctionFieldLimit.lean supply individual notions and results, not all the item's clauses. No complete project declaration was found for attachment.

## WANTED

None. All foundational sources needed here are present in literature/stacks-project/.

## Corrections and scope

No statement dispute and no change to the statement or its statement dependencies. The formerly empty proof is replaced with an argument for all its clauses, including the actual restriction and residue-field maps. The word equivariant has been made explicit using inverse pullback: a ring map B_i -> B_hi is (h^{-1}|_{W_hi})^*, and the product's hi coordinate is this map on its i coordinate. Ordinary pullback by h would point in the opposite direction.

The source already calls the equivariance and generic comparison agent-written. The split is accordingly proof_origin.by = agent, with precise Stacks places for the existing inputs; it does not attribute the combined statement to a Stacks lemma.

The current latest blueprint was read at sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3). The item is an auxiliary added input below that route. Its existing ancestry reaches lem-sfb-admissible-direct-image, whose created.item is a module name; blueprint_refs.py ancestor consequently prints None. I retain the existing null from.node and its detailed place/via rather than inventing an imported ancestor. Searching the blueprint for fraction, disjoint, clopen, affine fraction, equivariant and generic germ found no blueprint statement equivalent to the assigned conjunction. same_as remains [].

## Not duplicates

No new nodes, hence no new/existing node pairs. Reused lem-weil-pbc-spec-clopen-idempotent (00EE), lem-weil-pbc-affine-open-section-vanishing-prime (01I3/01HV), lem-weil-pbc-sheaf-disjoint-union-product, lem-sc-integral-function-field-affine-fraction (01RV/01HV), lem-weil-pbc-scheme-stalk-map-composition (008M), and lem-weil-pbc-fraction-field-lift. This avoids creating six duplicate inputs.

## Mathlib search results

The required msearch.py commands were actually run, with exact queries recorded in searches.jsonl and appended to the item's prior search history. LeanFinder was tried in two phrasings; Loogle, grep and LeanSearch also ran. Services returned hits, not unavailable, in this attempt. The semantic hits concerned finite affine morphisms, finite affine coproducts, residueFieldMap, and affine naturality; none states the full conjunction. I read Mathlib/AlgebraicGeometry/FunctionField.lean, especially germToFunctionField (41), germ injectivity (55), functionField_isFractionRing_of_affine (116), and functionField_isFractionRing_of_isAffineOpen (148). These give the existing generic-field input but not the whole item. The prior 2026-10-22 search history, including its genuinely unavailable LeanSearch result, is retained verbatim. No search was invented or recorded as negative when unavailable.

## Review by Q110

I read the assigned statement against Stacks schemes.tex 01I3 (lemma-standard-open-affine) and 01HV (lemma-spec-sheaves), algebra.tex 00EE (lemma-disjoint-decomposition), and morphisms.tex 01RV (lemma-integral-scheme-rational-functions). I also read morphisms.tex 01WH (definition-integral), properties.tex 01OK (definition-integral), schemes.tex 01I5 (lemma-disjoint-union-affines), and sheaves.tex 008J (definition-f-map) and the germ construction preceding 008M (lemma-compose-f-maps-stalks), plus the definition 01HB of locally ringed spaces. These places distinguish a coordinate-ring identification from an arbitrary isomorphism and ensure that the maps used are the actual maps in the statement.

For step 1 I opened def-weil-finite-integral-morphism and checked that its statement includes affineness, so no theorem about finite morphisms is being inferred just from a finiteness label. I opened def-sc-generic-point: its closure formulation proves directly that xi_j lies in V. Disjointness of the target components forces precisely the indices in O to occur. This also proves nonemptiness of every W_i without assuming flatness of q or normality of either scheme.

For step 2 I read def-weil-affine-spectrum and both cited clopen/principal-open nodes. The former theorem supplies D(e_i) on the affine W, and clause (b) of the latter explicitly says that this open is affine. Thus a mere topological clopen does not silently become an affine scheme. I read def-pc-integral-scheme and used its nonempty affine-open domain clause exactly on V in Z_j and W_i in X_i. No assumption that arbitrary intersections of affines are affine is used.

For step 3 I opened lem-weil-pbc-sheaf-disjoint-union-product, which states the binary restriction map as a ring isomorphism. The finite induction is written out, starting with the one-component identity. At each induction stage the rest is an open union disjoint from the chosen component. Its projections are still restrictions, so the final isomorphism is exactly the restriction map, not just a ring with the same abstract product type.

For step 4 I read def-weil-locally-ringed-space-morphism, including its restriction-compatible section maps and its composition rule. Those statements suffice for the displayed coordinate identity and the action laws. I checked the directions on a two-component swap: inverse pullback sends a section on component i to a section on component hi. The equality qh=q, also applied to h^{-1}, makes W stable and makes the action compatible with A. This is a short calculation from definitions, not an unproved equivariant descent theorem.

For step 5 I read the entire statement of lem-sc-integral-function-field-affine-fraction and verified its hypotheses individually. It supplies injective actual germs and the fraction representation, not only an unspecified field isomorphism. I read def-weil-residue-field and used that a field's maximal ideal is zero. The equality with ambient stalks is checked on neighbourhood/germ representatives; this requires only that the component is open. In particular no normality or Noetherian assumption is slipped in.

For step 6 I read lem-weil-pbc-scheme-stalk-map-composition, whose clause (a) states precisely the germ square used. Together with the definition of the residue-field map this gives the displayed equation on elements of A. A field homomorphism is injective by the ideal-kernel argument, so the equation and the already established injection A -> kappa(xi_j) prove that a_i is injective; this avoids an unquoted scheme-theoretic dominance theorem. I then opened lem-weil-pbc-fraction-field-lift and checked that its injectivity hypothesis holds for gamma_i composed with a_i. Its existence and uniqueness statements, and its a/s formula, give the claimed canonical extension.

For step 7 the same germ-square theorem is applied to h^{-1} fixing the component. Integral schemes have the unique generic point used in step 5, so its action fixes eta_i. The field formula follows on every b/c and has nonzero denominator because beta is a ring isomorphism. The fraction-extension theorem provides uniqueness, and stalk-map composition clause (b) agrees with the inverse-pullback convention. There is no claim that all of H fixes an individual component; only D_i acts on its own field.

I checked the small cases of a singleton component set, a nontrivial two-component permutation, a trivial group or stabilizer, zero-dimensional integral components (fields), and a finite non-flat map of integral schemes. All the arguments still apply. The empty chart case is excluded explicitly by the item; every B_i is nonzero because eta_i belongs to W_i. Components outside O contribute nothing, and an empty complement in the finite induction causes no extra hypothesis. Finite H is more than the action calculation needs, but it is retained.

Against delivery-errors B--E: all objects stay self-contained in the unchanged item; no unsplit node or hidden proof sketch was created; every non-elementary input is a cited existing statement; every cited statement was opened and is quoted verbatim in citations.json; no source proof is used as an unstated interface; no new dependency points to a descendant of the item; and no clause is outsourced to a renamed copy of itself. The steps marked elementary are the set-theoretic cover argument, finite binary-product induction, restriction/action calculation, and substitution on fractions after the cited theorems. All seven steps are below 2000 characters. The reused theorem nodes are Mathlib leaves, so no off-unit route replacement or tool-use approval is required. No Lean file was written and no compiler, Lake or build tool was run.

## Unfinished work

None in the mathematical split. The dry run and direct delivery are performed with the required launcher tool.
