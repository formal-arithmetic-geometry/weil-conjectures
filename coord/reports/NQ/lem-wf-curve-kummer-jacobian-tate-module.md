# Stage-1 report: lem-wf-curve-kummer-jacobian-tate-module

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-curve-kummer-jacobian-tate-module.json`: statement, seven proof steps, exact dependency lists, blueprint search result, and six actually executed Mathlib searches; status `split`.
- `citations.json`: one verbatim statement quotation for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` is the search command's original log; `write_split.py` is a sandbox-only preparation script.

No new nodes; no Mathlib leaves. No unit record changed: the item is a lemma within the definition unit `sk-d-real-jacobian`, whose `steps` list is empty, and is not its key definition node.

## Attachments

None for this item. A search of the entire read-only slopmaster2 `WeilConjectures/` for the id, Kummer, Jacobian, and Tate-module terminology found no declaration proving every clause. `AlgebraicGeometry.Scheme.EtaleTorsor.exists_picTorsionPairing`, `AlgebraicGeometry/FundamentalGroup/Frobenius.lean:260`, mentions this blueprint item in a docstring but its proof is `sorry`; its conclusion is a pairing, not this item. `AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper`, `AlgebraicGeometry/Curve/Kummer.lean:58`, supplies only the proper Kummer-to-cohomological-Picard group equivalence, without the Jacobian, canonical Galois action, or transition assertion. `JacobianTorsionDatum.nonempty_tateModuleEquiv` in `EtaleCohomology/Purity/RealSheaves/Jacobian.lean` handles the Picard-to-Jacobian half only. None is a whole-item attachment.

## WANTED

None. The item proof is agent-written, following the imported blueprint proof and the available Stacks sources. No SGA source is used.

## Corrections and scope

The original finite Kummer–Picard–Jacobian route is retained. The statement is clarified by explicitly quantifying the prime ell and n at least one, specifying the pro-etale coefficient and its canonical etale descent, naming both transition maps, and spelling out the cohomological Galois action. These are the conventions already used in the source proof. No hypothesis on the ground field was added, and the result is not restricted to finite fields.

The imported proof cited only exactness of Kummer for a long exact cohomology sequence; Step 2 now cites a node actually stating the exact sequence. It incorrectly called the H1(mu)-to-Pic arrow a connecting map; it is the map induced by inclusion of sheaves. The equality H1(Gm)=Pic alone did not state its pullback compatibility; Step 6 now cites `lem-sc-h1-gm-pic-pullback`. Canonicity alone was not a proof of equivariance. The proof now checks naturality of the inclusion and uses the explicit equivariant point comparison of the already reviewed `lem-wf-geometric-jacobian-galois-action`.

That neighboring node has already repaired the source's scheme-action variance. I use its current point action, not the old anti-action formula. For sigma, cohomology and Picard pullback use id times Spec(sigma), while the left semilinear scheme action on J covers Spec(sigma inverse); the point action is a_sigma composed with x composed with Spec(sigma). Thus both sides have the same left action.

I do not use `lem-sc-kummer-les`: its current statement assumes H2(Gm)=0, an unnecessary extra input here. Nor is existence of a Jacobian reconstructed: the statement already fixes one, and the current neighboring Galois-action node supplies its equivariant point comparison. The separately cited representability theorem in the imported proof is consequently redundant in this proof's dependency list.

## Searches and Not duplicates

The whole imported blueprint was searched with `tools/blueprint_refs.py search` for Kummer, Jacobian, roots of unity, long exact, and smooth connected. DAG statement searches additionally found the existing finite Tate site-descent node, cohomology comparison, pullback functoriality, and Picard pullback nodes. All are reused. No other blueprint node states the whole compatible equivariant comparison, so `blueprint.same_as=[]`.

## Not duplicates

There are no new nodes and therefore no new/existing-node pairs. In particular, a torsion-degree-zero node, a transition square node, and a separate equivariance clause would duplicate elementary steps or move clauses of this item into new nodes; none was created. `lem-amb-finite-tate-site-descent` already states the generic site comparison and is cited rather than duplicated.

The six original logged Mathlib searches were read. LeanFinder returned field Kummer, Selmer, Hilbert 90, and cyclotomic-character facts; the second phrasing returned ring Picard and elliptic-curve class-group facts. LeanSearch returned group H1 and cotangent H1; Loogle's Kummer name search returned field theory and Kummer–Dedekind. The full-source grep hit unrelated Kummer and analytic Jacobian material; the focused AlgebraicGeometry grep returned three Weierstrass Picard comments. None states this theorem or specializes to it in one line. All recorded queries are copied from `searches.jsonl`, with their actual results. All services answered.

## Review by NQ

I read the contract, worker brief, three blueprint levels, the chapter and unit records, the old master item including its four proof paragraphs, and the main-20261015 item. The current main item has the same statement and no appended proof; the master proof remains the concrete route. I also read delivery-errors B through E in full. There was no prior sandbox split, report, or search log to preserve.

For the sources, I read Stacks `etale-cohomology.tex`, Section 03PK, Lemma 03PL (`lemma-kummer-sequence`) and the displayed cohomology sequence immediately following it; `sites-cohomology.tex`, Lemma 040E (`lemma-h1-invertible`) and its torsor construction; `derived.tex`, Lemma 015B (`lemma-higher-derived-functors`); and `proetale.tex`, Lemma 099W (`lemma-compare-cohomology`) and the preceding relative-comparison proof. I read the degree definition and Jacobian representability blueprint sources as well as the current corrected geometric Galois-action node and its reviewed proof. There are no new nodes requiring additional source reports.

1. Step 1 uses precisely the canonical finite Tate descent in `lem-amb-finite-tate-site-descent` and the canonical cohomology pullback isomorphism in `lem-cbc-abelian-etale-proetale-cohomology-comparison`. The first statement explicitly permits every scheme with ell invertible and every finite coefficient field extension F/Q_ell; take F=Q_ell, uniformizer ell, residue exponent n, and annihilating exponent r=n. Its etale tensor is the tensor unit, with both directions written out. Its statement explicitly includes pullback and power-map compatibility. The second allows every abelian etale sheaf and hence mu at i=1. This repairs the silent change of sites without using an integral or rational comparison.

2. Step 2 uses the definition and exactness nodes for the Kummer short exact sequence. The exact-sequence clause of `lem-weil-pbc-pullback-cohomology-long-exact-ladder` applies to a short exact sequence on any scheme, so setting its u to the identity entails no smallness or base-change hypothesis. `lem-sc-h1-gm-pic` is an isomorphism of abelian groups, as needed for tensor powers; `def-weil-pbc-etale-cohomology` supplies the cochain model. The power map is m times identity, and the same scalar multiplication on resolutions induces m times identity on cohomology. The step records the actual inclusion map; it does not borrow a connecting map formula from a definition.

3. Step 3 uses exactly the smooth-proper-connected case explicitly included in `lem-sc-global-functions`. The geometric curve has these properties by the hypotheses, and is reduced because smooth over a field; the global-function node's reducedness proviso is satisfied. `def-sc-gm-torsor` actually defines Gm as units, and `lem-weil-pbc-cohomology-pullback-degree-zero` actually identifies H0 with sections. Algebraic closedness supplies a root of X^m-a and a nonzero root for nonzero a. The remaining kernel/image argument uses the exact segment already written in Step 2. Neither Brauer vanishing nor surjectivity of multiplication on the Jacobian is assumed.

4. Step 4 uses the degree homomorphism and kernel description actually stated in `def-sc-pic0`; cancellation of positive m in Z is elementary. The current `lem-wf-geometric-jacobian-galois-action` states J(K)=Pic0(C), equivariance, torsion restriction, and multiplication compatibility for exactly this geometric curve and every prime ell. Thus this step uses that statement, not an unstated construction inside its proof. Restricting the group isomorphism and composing it with beta is elementary, and the argument is written out rather than outsourced to a new clause-node.

5. Step 5 writes out all three vertical components between the two Kummer sequences: power ell on mu, power ell on the middle Gm, identity on the right Gm. Both squares are checked on sections. Cohomology functoriality then gives the displayed equality of maps induced by inclusions; no naturality of connecting homomorphisms is needed. The neighboring Galois-action node explicitly says its torsion comparisons commute with ell, which is the exact remaining input. This proves the transition assertion in the item itself.

6. Step 6 uses `lem-asd-etale-finite-twist-pullback` only for its actual roots-of-unity inverse-image isomorphism and compatibility with composition. Clause 3 of `lem-weil-pbc-cohomology-pullback-functorial` supplies naturality in the inclusion; clause 4 supplies composition. `lem-sc-h1-gm-pic-pullback` expressly allows morphisms of schemes between curves over possibly different algebraically closed fields, so a semilinear t_sigma is within its hypotheses and is not silently treated as K-linear. Its statement identifies the cohomological map with line-bundle pullback. The current neighboring node matches that Picard action with its point action. The two contravariances proving the left action law are recorded explicitly. None of these nodes is used merely as a name for a different notion.

7. Step 7 composes the same comparisons from Step 1 and the same inclusion-and-Picard pullback square from Step 6; it does not invoke a new unproved comparison. The multiplication-by-ell transition in `def-wf-abelian-tate-module` is exactly the finite system already constructed. Naturality is with respect to pullbacks compatible with the representing data, and follows from the displayed inclusion square, not from an arbitrary chosen abstract equivalence. No exchange of inverse limits, no cohomology of a Z_ell sheaf, and no rational coefficient claim is required to prove the finite-level statement.

I tested the conclusions on P1 (Pic=Z, Pic0=J=0, and Kummer gives H1(mu)=0) and on genus-one curves (torsion line bundles are exactly Jacobian torsion, with the same power transitions). The argument works in characteristic zero, in positive characteristic with ell different from it, and over imperfect k0 because it uses Aut(K/k0), the current neighboring action statement, and the algebraic closure K. It does not assume that K/k0 is separable or that k0 is perfect. The smallest index n=1 gives the same transition square, and the excluded n=0 would give trivial groups rather than an additional input. No new statement was introduced to test. Every proof step is below 2000 characters; the longest is the explicit equivariance argument, with each non-elementary input cited.

The off-unit statements are generic tools declared in `split_report.tool_uses`, preserving the unit's Kummer/Picard route. I checked that each cited file states the quoted conclusion; `citations.json` copies the statements verbatim. Definitions and elementary degree, image, and square arguments were kept in the item. No other node, unit, coordinator, launcher, or Lean file was changed.

## Unfinished work

None in the stage-1 split. The remaining dependencies retain their existing project states. The server split review passed, and the full delivery dry run passed preflight (first receipt e4d3a858b4). The final dry run and push use the corrected report line reference.
