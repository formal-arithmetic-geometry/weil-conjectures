# Stage-1 worker report: lem-rp-local-frobenius-models-agree

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-rp-local-frobenius-models-agree.json`: the existing item, now split in five proof steps; its statement and hypotheses are unchanged.
- `citations.json`: verbatim quotes for every cited node in every step.
- No new nodes, no Mathlib leaves, no Lean files, no unit edits and no compilation.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `/home/ubuntu/weil-newtargets-master/WeilConjectures/` for the exact blueprint id, the title, `stalkFrobenius`, rational local Frobenius and the trace-formula local operator. The source has the finite-stage `WeilComplex.stalkFrobenius` API, but no sorry-free project declaration stating this E-stage comparison. The target therefore is not an attachment.

## WANTED

None. The proof expands the supplied blueprint/interface sentence using existing DAG statements; no additional literature is required.

## Issues found and repaired

The inherited item was unsplit and had an empty proof. Its source asserts that the induced geometric-stalk Frobenius is the trace-formula local Frobenius without spelling out the comparison. The retained delivery expanded that assertion rather than introducing a node that merely restates one of the item's clauses. The rationalized stalk comparison is unpacked from the existing rational point-fiber and pullback conventions; the E-stage formula and the normalized point-transport comparison are then applied at the same point and with the same iterate. No hypothesis was added or dropped. The closed-point degree is positive by the existing closed-point convention, and the rational point `y` is exactly the point represented by the chosen embedding.

## Not duplicates

There are no new nodes. A whole-DAG search for the item's title, `local Frobenius models`, `trace-formula local Frobenius`, and `stalkFrobenius` found only this item and the parent corollary's citation. `lem-weil-local-frobenius-conjugacy-class` concerns changing the embedding and does not compare the trace-formula model operator with the geometric-point operator, while `lem-trf-local-frobenius-transport-normalization` supplies only the generic transport normalization and not this item's Weil-complex comparison. Blueprint searches for the same phrases and for the source sentence found no separate node stating the item.

## Mathlib searches

The retained report described the following original searches. Its original `searches.jsonl` was not present when this repair resumed, so these historical descriptions are retained as history, not presented as the current log. The repair searches recorded below are the searches now present in `searches.jsonl`:

- LeanFinder for an E-stage trace-formula/geometric-point local-Frobenius comparison returned only Witt-vector and arithmetic-Frobenius declarations; verdict no match.
- LeanSearch for the same comparison returned only Witt-vector/isocrystal and arithmetic-Frobenius declarations; verdict no match.
- Loogle for `Frobenius, stalk, WeilComplex` returned zero hits and reported the compound identifier as unknown; this is recorded as unavailable/inconclusive for Mathlib, not a claimed match.
- grep for `Frobenius.*stalk|stalk.*Frobenius` in `Mathlib/AlgebraicGeometry` returned no hits.

The retained report says the returned declarations were read and no match was found. This repair independently reads the current query results described below.

## Review by Q150

I read the item, `sec-purity-real-sheaves`, unit `sk-p-real-rankin`, the imported source `thm-weil-grothendieck-lefschetz-trace.proof.md` Step 1, and the full statements of every node cited by the retained four steps and the repaired five steps. The blueprint's relevant sentence is the last sentence of Step 1: the trace-formula chapter supplies the induced Frobenius operators on geometric stalks. The parent `cor-rp-euler-product` uses exactly this comparison when it identifies its local factor. The item remains under the real-rankin unit; the trace-formula normalization lemma is an off-unit generic tool, so I report that use for the lead to record at merge.

Step 1 uses the rational-model proposition's statement that `K_E` is the same object in the rationalized category, the point-fiber definition that `Fib_s` at `E` is `Gamma(s,-) tensor E`, and the rational pullback convention that rational objects use the integral operations on objects. These statements give the canonical E-linear comparison between the lattice stalk tensored with `E` and `C_xbar = Fib_s(L xbar^* M)`. The construction is natural because all three cited operations are functorial; no separate finiteness theorem is silently used.

Step 2 now fixes the comparison families required by the returned normalization citation. I read the complete statement of `lem-trf-integral-pullback-comparison-realization`, including its formula `c = eta^{-1} composed with R lim(c_n)`, independence of representatives, associativity, unit, equality-of-scheme-morphisms, iteration and rationalization clauses. The coefficient extension can be the identity `E=E`; all schemes here have characteristic `p` with `ell != p`, so `ell` is invertible on them. The complexes lie in the stated derived-complete constructible categories through the given lattice. The local-Frobenius definition explicitly uses the integral compositors and their rationalizations, so fixing their canonical construction adds no hypothesis on the Weil map. I also read Stacks Tag 099N (2),(5) in `proetale.tex` and Tag 0D6D in `sites-cohomology.tex`. Those tags explain completed pullback and ordinary composition; the stronger specified realization and coherence facts used here are cited from the existing realization node, not attributed directly to Stacks.

Step 3 uses the E-stage operator and the entire stalk-normalization paragraphs of `prop-trf-rational-frobenius-integral-model`. I reread the current statement of `lem-trf-local-frobenius-transport-normalization`, especially its new requirement to use the strict-system realization comparisons. It identifies its successive point transport `t` with `J(kappa^[e]) rho` under the iterated compositor; after applying `J(c_e^{-1})`, this is the actual `tau_{y,e}` of the model proposition. Its integral/rational clause identifies the specified maps, so the proof does not infer equality from uncoordinated levelwise reductions. The displayed composite in `def-weil-local-frobenius-trace` is precisely this transport followed by `J(theta^[e])`. I checked `e>=1` using that definition's closed-point clause, the same residue embedding and point `y`, `phi_E=theta`, and the return equality `g_X^e xbar=xbar g_s^e`. Naturality of Step 1's comparison gives the correctly typed identity `alpha composed with F_trf = F_geom composed with alpha`; I corrected the retained prose, whose first composite had been reversed.

Step 4 uses the explicit cohomology functor and finite-dimensionality clauses in `def-weil-coefficient-cohomology-modules`, and the local-trace definition's identification of cohomology-sheaf stalks with `H^j(C_xbar)`. Thus applying `H^j` to the complex isomorphism and its intertwining equality gives every required E-linear comparison. Step 5 transports a basis along this isomorphism, so both matrices and hence determinants agree. Applying `E -> Qlb` coefficientwise preserves that determinant polynomial. This last step uses only elementary finite-dimensional linear algebra.

I checked small cases `X_0=Spec(k_0)` with a rank-one constant Weil complex (both operators are the identity), the zero complex (all cohomology and determinants are zero/one as appropriate), degree `e=1`, and a two-term complex with a nontrivial differential (the comparison is on the derived point complex and remains functorial on both cohomology degrees). The proof has no hidden denominator choice: the proposition's E-stage operator is independent of the lattice presentation, and only its stated rationalized formula is used. No SGA source is cited, no statement was corrected, and no long step exceeds 2000 characters.

## Repair of return L (2026-10-18)

The return identifies reviewed branch head `e1ea054b4f`: its landing refused the changed statement of `lem-trf-local-frobenius-transport-normalization`. I retained the delivered node and report rather than restarting the split. Comparison with the current repository item found changes only in `status`, `proof`, `proof_deps`, `proof_origin` and `split_report`; its statement, statement dependencies, source and blueprint ancestry agree. The prescribed delivery command fetches current main and overlays only the split-owned fields, so this repair is rebased through that command rather than through a worker git operation.

I reread every proof dependency, not only the one named by the return. The current normalization statement requires the actual integral compositor and scalar comparison families from the existing realization node. The repair adds a separate short step choosing these comparisons, cites their construction, and writes `b_e=J(c_e^{-1}) t` to make the target of the normalized transport precise. No arbitrary family is silently substituted for the specified one. The previous operator comparison is retained with this substantive clarification. `citations.json` was missing despite being named in the retained report; it is restored with all ten current verbatim excerpts.

Both the normalization and realization statements serve as generic tools from the trace-transport work: the real-rankin unit uses local operators but gives no construction of integral pullback comparisons. These uses are declared in `split_report.tool_uses` for independent review. The mathematical route through the trace-formula local normalization is unchanged.

For B I checked the existing node's complete statement and ancestry; there are no new nodes, so new-node schema, duplicate-tag, source and standalone-statement issues do not arise. For C I opened all seven current proof-dependency statements and checked every one of the ten step citations against its actual statement; the excerpt for each is literal text, not text taken from a proof. The new construction is an existing node rather than a duplicate. For D the five steps carry an explicit comparison argument; no new node restates any conclusion, and all proof dependencies are the union of step uses. For E I checked coefficient categories, invertibility of ell, constructibility, positive degree, the same embedding and iterate, compositor orientation, and the typed intertwining identity. The zero complex gives determinant 1; a rank-one complex with Weil scalar lambda gives lambda at degree 1 and lambda^e at a degree-e point on both sides; a bounded complex with a nonzero differential is handled before taking cohomology, so no splitting of that complex is assumed. No step is longer than 2000 characters.

The item statement and hypotheses are unchanged, there is no statement dispute, and no mathematical part remains unfinished. There are zero new nodes and zero new Mathlib leaves. No SGA route, Lean edit or compiler is used.

## Searches in this repair

The normalization question now explicitly includes the specified integral pullback composition comparisons. Because the retained sandbox has no old search log, I ran the new comparison question and a second phrasing with `msearch.py`; only these actual runs are appended to the item's inherited `mathlib_searches`. The inherited unavailable records remain distinguishable from these logged runs.

- `grep` query `Frobenius.*(stalk|transport)|((stalk|transport).*Frobenius)`: 0 hits. No match: the signatures concern structure-sheaf stalks, arithmetic ring Frobenius or Witt-vector isocrystals; none states a pro-etale Weil-complex local-operator comparison.
- `leansearch` query `At a closed point the scheme Frobenius stalk operator of an l adic Weil complex is conjugate to the geometric Galois point transport operator`: 8 hits. Returned `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo`, `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_closedPoint`, `AlgebraicGeometry.Scheme.Hom.stalkMap_congr_point`, `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`, `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk`, `AlgebraicGeometry.Scheme.stalkMap_congr_point_assoc`, `AlgebraicGeometry.stalkClosedPointIso`, `AlgebraicGeometry.Scheme.Hom.stalkMap`. No match: the signatures concern structure-sheaf stalks, arithmetic ring Frobenius or Witt-vector isocrystals; none states a pro-etale Weil-complex local-operator comparison.
- `loogle` query `"frobenius", "stalk"`: 0 hits. No match: the signatures concern structure-sheaf stalks, arithmetic ring Frobenius or Witt-vector isocrystals; none states a pro-etale Weil-complex local-operator comparison.
- `leanfinder` query `Geometric point Frobenius on an E Weil complex agrees with the rationalized integral trace formula stalk operator using canonical pullback composition comparisons`: 8 hits. Returned `arithFrobAt`, `IsArithFrobAt.arithFrobAt`, `AlgebraicGeometry.Scheme.residue_residueFieldMap`, `WittVector.StandardOneDimIsocrystal.frobenius_apply`, `AlgebraicGeometry.Scheme.residue_residueFieldMap_assoc`, `AlgHom.IsArithFrobAt.localize`, `AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, `AlgHom.IsArithFrobAt.localize_algebraMap`. No match: the signatures concern structure-sheaf stalks, arithmetic ring Frobenius or Witt-vector isocrystals; none states a pro-etale Weil-complex local-operator comparison.

## Current citation statement fingerprints

These SHA256 fingerprints record the statements read for this repair. The delivery tool revalidates the quotes and constructs the delivery against the fetched current DAG.

- `def-weil-coefficient-cohomology-modules`: `a7148403a7f0a4d53460dfbbb0b26a8da7cf01b939d64c580c038961c962c8d8`
- `def-weil-derived-pullback-tensor-hom`: `1d069b3a4dcd81c1fddcca2da33d0e0ea94bc53da7103e0b9c15c39ea7100786`
- `def-weil-finite-coefficient-point`: `8df9fe1baa5b9e114ba41dd8c1978989a46ec327038187646ad4f2ab538d1a50`
- `def-weil-local-frobenius-trace`: `5efbc967ff56c48fa5cfe2c02cf8657f8a3701575c2d9595fac0b59a778568a0`
- `lem-trf-integral-pullback-comparison-realization`: `c77e5a513d3505dfd4f047c6cb62a830c929c50023908c4b9c775f1ad97f4807`
- `lem-trf-local-frobenius-transport-normalization`: `db5f7ae578060c6c7594f43ad44e9bd8ad01a8ea07e76ddde7ba98874a198864`
- `prop-trf-rational-frobenius-integral-model`: `f6e4a2f305476eb2ec98687b74700cb7398bba5d01cc3543d36a6a2d11a072f3`
