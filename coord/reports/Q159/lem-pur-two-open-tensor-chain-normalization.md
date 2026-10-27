# Q159 — lem-pur-two-open-tensor-chain-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-two-open-tensor-chain-normalization.json: statement, split into seven explicit calculations. Statement unchanged. Mathlib verdict: no exact match; the uniqueness-of-adjoints results are generic components, not the full geometric statement.
- citations.json: one verbatim statement quotation for every step/node pair.

No new nodes; zero Mathlib leaves. searches.jsonl contains the actual command searches. The original imported searches have been retained, and all searches made in this attempt have been appended to the item's record.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, twoOpenTensor, two_open_tensor, tensorChainNormalization and the open/tensor notions. The nearby OpenCover and OpenImmersionProjection results concern different assertions. The existing FiniteOpenProductSwap definitions were read to pin down comp, gamma, rho, tensorPullIso and pullComp; they are operations, not a finished proof of this item.

## WANTED

None. The required Stacks source files and current blueprint proof are present.

## Problems found and corrected

The item had no proof. The supplied statement is well typed after making its explicitly specified pullback-composition identifications. No statement dispute, weakened conclusion, or added hypothesis was needed. The blueprint proof supplies a symmetry reduction, rather than a literal theorem with this full arbitrary-unbounded statement; proof_origin therefore remains explicitly agent-written. In particular, this split does not use a bounded constructible projection formula, the smooth-purity theorem, or the general external-product symmetry theorem it is intended to support.

The main possible error was to omit the units when writing 'restriction is identity'. The proof instead records the equations for the actual restricted gamma and rho, then retains both open units until the compositor equation cancels them. The right-order argument is written separately with output Q tensor T. No assertion of unsigned symmetry is used: both Koszul braidings are present.

## Unfinished work

None for this one-level split. The cited existing nodes retain their own independent proof obligations.

## Not duplicates

No new nodes were created. Whole-blueprint searches for open tensor, tensor normalization, two-open and projection formula found no blueprint node stating this two-open normalized-chain assertion; the results include general/bounded projection formulas and unrelated Nagata two-open statements. Existing DAG statements searched for leftAdjointUniq/unit, composite adjunction and open-comparison normalization do not supply an alternative exact attachment. Reused def-weil-pbc-composite-adjunction for the explicit composite unit rather than creating a generic categorical leaf.

## Review by Q159

I read the chapter and sk-prop-an unit, the item's recorded ancestry through finite-open-product-swap, the current main-20261015 Kunneth-coherence proof (symmetry paragraph), Stacks sites-cohomology.tex Tag 0GL1 (lemma-j-shriek-and-tensor) and sites-modules.tex Tag 0E8I (same label). Those tags give the derived and underived open projection formulas, respectively; neither literally states this normalized two-open chain theorem. I also read the existing item-dependency statements, including the whole finite-level clause and coherence conclusion of lem-pur-derived-pullback-tensor-iso, and the defining comp/gamma/rho expressions in lean/Sheaf/Paper/FiniteOpenProductSwap.lean. The ordinary unbounded category is essential throughout. The proof follows the recorded open-extension reduction below the fixed unit, using generic categorical tools, and does not change a unit or chapter route.

For step 1, lem-sf-open-tensor-normalization explicitly gives invertible open units, gamma for arbitrary objects, and its identity after unit/tensor identifications. def-sf-finite-open-tensor-operations pins those maps to the actual operations, and lem-pur-derived-pullback-tensor-iso identifies the comparison mu. I rewrote the normalized identity with all source and target units visible. For step 2, the definition supplies exactly the two signed braidings; the same pullback-tensor statement explicitly gives signed-symmetry compatibility. Naturality moves the inverse unit through the braiding and the two signs cancel. This is a short calculation from the cited statements, not a new lemma to be split off.

For step 3, I opened def-weil-pbc-composite-adjunction: its statement explicitly gives the composite unit and composite Hom bijection. def-sf-finite-open-tensor-operations defines comp as the unique-left-adjoint map for precisely this adjunction, after pullComp. Evaluating its defining Hom bijection proves the requested unit equation. This calculation can also be checked against Mathlib/CategoryTheory/Adjunction/Unique.lean lines 33–56: unit_leftAdjointUniq_hom_app has the expected direction. It is not being cited as an unrecorded DAG lemma; the proof expands the definition of the specified comparison. No extra categorical theorem is needed.

In step 4, I checked the types of b, h, d and f_L. The first two existing geometric nodes give precisely the unit inverses and tensor naturality used. In step 5, unit naturality for the actual arrow f_L moves v* v! f_L through eta^v; mu composition and naturality identify the remaining tensor map with r_L, and the already proved compositor equation gives the final identity. Step 6 repeats this calculation with f_R, retains the order Q tensor T, and uses the same cited naturality/composition clauses rather than a vaguely asserted transport. Step 7 uses only invertibility supplied by the normalization node, the preceding calculations, functoriality and the definition of the compositor. Each step is under 2000 characters and is a routine equation from these inputs; none hides a new non-elementary comparison theorem.

I verified that A is the constant finite coefficient ring of def-pur-conventions; ell is invertible on the k-schemes, as required by the finite pullback comparison. All three opens and all restricted complexes remain in the ambient unbounded categories. The cited normalization theorem permits arbitrary unbounded inputs and constant A, so no finite-Tor or constructibility assumption is smuggled into a tensor. The formulas were checked for identity opens (both units/compositor become their canonical identities), empty W (all objects on W and their extensions vanish), zero F or Q, and arbitrary degree shifts. For two odd-degree homogeneous factors, the two braidings in rho contribute minus signs twice and cancel, as required. The parameter delta is never replaced by an unspecified support isomorphism: its restriction is explicitly the factor d.

I checked delivery-errors B through E: no new-node form, duplication, hollow restatement or new statement hypotheses; every use is quoted verbatim in citations.json; no dependence on a parent's conclusion; no forbidden SGA source. The two off-unit results are declared as generic tool uses in split_report. The remaining composite-adjunction node is a Mathlib definition leaf. No Lean code or compiler/build was run, and all writes are in the designated sandbox.
