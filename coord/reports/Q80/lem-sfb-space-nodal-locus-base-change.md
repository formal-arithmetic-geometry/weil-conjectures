# Stage-1 worker report: lem-sfb-space-nodal-locus-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-nodal-locus-base-change.json`: item, split into eight steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-syntomic-fixed-dimension-locus.json`: statement-only prerequisite; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-nodal-chart-locality.json`: statement-only prerequisite; no Mathlib match.
- `citations.json`: one verbatim statement certificate for every node used by every proof step.

## Attachments

None. Searched the entire live `lean/WeilConjectures` tree for the blueprint id and nodal terminology and read the algebraic-geometry syntomic search results. There is no declaration giving this item. The existing algebraic-geometry mentions of nodes are counterexamples in docstrings. The ring-theoretic syntomic-at-a-prime declarations give local affine presentations, rather than either new geometric assertion.

## WANTED

None. All sources used are present under `literature/stacks-project/`.

## Problems found and changes

The item had no proof. Its inherited statement contained doubled TeX backslashes; normalized those to single TeX commands, with no mathematical change. No statement dispute was needed. The inherited properness conventions are irrelevant but were retained. The existing `lem-trf-nodal-open-locus` cannot be applied directly: its statement assumes pure one-dimensional geometric fibres, whereas this item explicitly does not. The split now first constructs the syntomic fixed-dimension piece, applies that existing lemma there, and proves maximality among all nodal source opens. This preserves the scheme-to-space route of Stacks 0DSH.

The blueprint ancestor command returns None for the inherited created-node chain. I retained its null ancestor, full place, and via chain; the new nodes add this item to the via chain. Whole-blueprint searches for nodal, nodal local, syntomic, complete intersection, relative dimension and etale local produced no equivalent blueprint assertion. The existing nodal scheme source-locality result was read and retained as distinct: it has neither algebraic-space target charts nor arbitrary-space base change.

## Unfinished work

No unfinished part of the item's split. Both new prerequisite nodes are deliberately unsplit, carry only statements, and join the subsequent stage-1 queue. This delivery contains no Lean file and ran no compiler, Lake or build command.

## Review by Q80

I read the item against `spaces-more-morphisms.tex`, Tag 0DSH (`lemma-locus-where-nodal`), including the diagram, the open-image construction, the appeal to nodal locality and the last base-change sentence. I also read `curves.tex`, Tag 0DSC and the preceding definition and nodal-family equivalence. The source really assumes only flatness and local finite presentation; equidimensionality is imposed only after restricting the source. Thus I did not add properness, dimension bounds, connectedness or nonemptiness to the item.

For `lem-sfb-syntomic-fixed-dimension-locus`, I read Morphisms 02V3 (the complete-intersection fibre locus commutes with every base change), 02NM (the Cohen-Macaulay relative-dimension decomposition), the adjacent 02K1 syntomic local-constancy argument, 02NK (relative-dimension stability), and 01UF. Its closed-point reformulation uses the actual statements of `dpa.tex` 09Q1 and 09Q6, `algebra.tex` 00SG, `more-algebra.tex` 07NV, and `varieties.tex` 0A21(2). These say, respectively, completion detects complete intersections, a pointwise CI spreads to an affine neighbourhood, completion preserves dimension, and at a closed locally algebraic point ring dimension equals local topological dimension. Together with the open dimension decomposition this gives the stated criterion. The lemma is about syntomic geometry in every dimension, and has no nodal conclusion: a cusp belongs to its one-dimensional piece. It therefore does not repackage the item's nodal-locus clause. It also contains a universal fixed-dimension and completed-ring characterization absent from the existing dimension-only or CI-only nodes, rather than a two-line restatement of one existing statement.

For `lem-sfb-space-nodal-chart-locality`, I read 0DSG conditions (4)--(7), 0DSF, and the paragraph defining the algebraic-space property. I read the scheme source-locality, target etale postcomposition and target fpqc-locality arguments in `curves.tex` as well. This prerequisite is purely a permanence and chart criterion for a nodal morphism already defined; it asserts no largest open locus. Over an algebraically closed geometric residue field, etale charts preserve the completed local ring at closed points; smooth relative dimension one is likewise preserved and reflected. The pointwise clause records exactly that chart interpretation, without an equidimensionality assumption on unrelated fibre components.

For step 1 I opened `lem-trf-nodal-open-locus` and checked its full purity hypothesis before using it on L_1. For step 2 I opened `lem-trf-nodal-curve-lci-criterion`: implication (1) to (2) gives a fibre local complete intersection once every closed point is smooth or nodal. This is exactly the hypothesis obtained on a nodal source open, and the definition of syntomic in the new fixed-dimension node then applies. The same two universal open constructions prove the unrestricted scheme base-change assertion, with no unmentioned purity assumption.

For step 3 I read all four clauses of `lem-weil-pbc-power-series-field-cohen-regular-complete` and the source remark 032C in `algebra.tex`. It gives the domain property and dimensions in both one and two variables. I wrote out the prime-chain argument for the quotient by uv, instead of merely claiming it has dimension one, and used the explicit completed-ring criterion of the new node. The old scheme nodal-locus node explicitly supplies its pointwise fibre interpretation. This verifies both directions of the scheme fibre description, including smooth nonclosed points.

For step 4 I opened `def-trf-algebraic-space` (existence and representability of atlases), `lem-trf-space-fibre-products-etale-covers` (pullbacks are spaces and etale covers pull back), `lem-weil-pbc-etale-composition-cancellation` (composition on scheme charts), and `lem-a1-space-etale-open-image` (the image is an open subspace and the map onto that image is surjective etale). Thus the new nodal chart criterion applies to N -> T over V -> Y with precisely the required surjective source arrow; it is not being used as an open-locus theorem.

For step 5 the universal chart condition says the pullback of any nodal open is nodal over T; scheme maximality then contains that pullback in N. Surjectivity and the inclusion-preserving open-subspace correspondence give largestness and p^{-1}(V)=N. These are written arguments, not additional nodes.

For step 6 I checked the actual statements of `lem-weil-pbc-flat-morphism-base-change` and clause (3) of `lem-weil-pbc-qcqs-morphism-permanence`. They apply to h over the schemes T and Z; I did not apply a scheme theorem directly to an algebraic space. The fibre-product/cover node and etale composition rule supply the surjective chart U_Z -> X'. The universal properties identify U_Z with the displayed refined pullback. This makes the arbitrary-space base change reduction explicit.

For step 7, the two inverse images are both N x_T Z by earlier steps. This uses only associativity of the given fibre products, substitution of the saturation equality, and surjectivity of the atlas; its only external fact is the stated bijection between open subspaces and open subsets. It is therefore elementary. Step 8 uses the pointwise preservation and reflection part of the new chart node, and the already proved scheme fibre description. Nothing about the scheme representability of an entire geometric fibre is assumed.

I tested the empty source, a smooth affine line, a smooth affine plane, a nodal affine curve, a cusp, and a disjoint union of an affine line, a nodal curve and an affine plane. The one-dimensional syntomic piece removes the plane, retains the cusp until the nodal test, and retains both branches at a node. For the generic node test, primes containing uv contain u or v; its completed ring is one-dimensional in every characteristic, including characteristic 2. The definitions impose neither connectedness nor nonemptiness on a nodal family, so empty fibres and empty opens cause no failure. For the syntomic lemma at d=0, a double point is allowed as a complete intersection: it is not incorrectly forced to be smooth. Base change can be nonflat, non-Noetherian, or empty; none of the two locus results requires a flat base change.

I checked delivery-errors B through E against these statements and steps: the new nodes are self-contained statements only, their notions have definition references or inline definitions, source labels/tags were looked up, all searches were actually run and their hits read, and no candidate proves a complete new node in one line. The item retains the eight-step argument rather than moving its conclusion to a new node. All non-elementary steps name the statements they need; citations.json copies the actual statement text. No non-elementary step exceeds 2000 characters. Generic tools from other units are declared in split_report.tool_uses; these support the original 0DSH route and replace no unit step.

## Not duplicates

lem-sfb-syntomic-fixed-dimension-locus vs lem-per-excellent-normal-surface-local-data: the existing statement is about Local data at the singular points of an excellent normal surface; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-per-normal-surface-exceptional-curves: the existing statement is about Finite exceptional-curve data for a normal excellent surface modification; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-zl-affine-geometric-components-finite-extension: the existing statement is about Geometric components of an affine scheme descend to a finite constant extension; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-curve-base-change-relative-dimension-one: the existing statement is about Base changes of a smooth curve are smooth of relative dimension $1$; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-dimension-locally-algebraic: the existing statement is about Dimension of an irreducible locally algebraic scheme over a field; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-finite-type-nonclosed-closure-closed-points: the existing statement is about Nonclosed points in finite-type schemes have infinitely many closed specializations; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-integral-locally-algebraic-affine-opens-dimension: the existing statement is about Nonempty affine opens of an integral locally algebraic scheme have equal dimension; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-integral-locally-algebraic-opens-dimension: the existing statement is about Nonempty opens of an integral locally algebraic scheme have its dimension; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-positive-dimensional-locally-algebraic-closed-points: the existing statement is about Positive-dimensional locally algebraic closed subsets have infinitely many closed points; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-completion-dimension-eq: the existing node concerns Dimension equality for maximal-ideal completion; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-completion-dimension: the existing node concerns The completion of a Noetherian local ring has the same dimension; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-completion-regular-local: the existing node concerns A Noetherian local ring is regular iff its completion is; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-dense-open-dimension-comparison: the existing statement is about A dense open in a finite type scheme over a field has full dimension; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-fibre-of-base-change: the existing statement is about The fibres of a base change are the base changes of the fibres; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection: the existing node concerns Flat, finitely presented, complete-intersection fibre at q: locally a relative global complete intersection; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-weil-pbc-syntomic-equation-count-comparison: the existing node concerns Equation-count comparison quotient at a finitely presented syntomic prime; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-coef-left-cone-restriction-cocartesian: the existing statement is about Left-cone restriction is cocartesian, with apex detection after base change; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-cohen-macaulay-equidimensional-fibre-pieces: the existing node concerns Equidimensional fibre pieces of a fibre Cohen-Macaulay open under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-cohen-macaulay-fibre-dimension-decomposition: the existing node concerns Open dimension partition of a fibre Cohen-Macaulay open under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood: the existing node concerns Constant local fibre dimension near one Cohen-Macaulay fibre stalk under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-cohen-macaulay-flat-quasi-finite-chart: the existing node concerns Flat quasi-finite chart near a Cohen-Macaulay fibre point under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-equidimensional-open-local-dimension: the existing node concerns Local dimension of a pure-dimensional locally algebraic open under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk: the existing node concerns Constant fibre dimension near a zero-dimensional fibre stalk under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-flat-fibre-dimension-strata-core: the existing node concerns Fibrewise dense constant dimension opens under fibre Cohen-Macaulay or dimension assumptions; it does not construct the universal syntomic fixed-dimension open or give its completed-ring characterization.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sbc-smooth-relative-dimension-permanence: the existing node preserves an already assumed dimension or smoothness condition under base change; it does not produce the universal syntomic fixed-dimension locus in an arbitrary flat family.

lem-sfb-syntomic-fixed-dimension-locus vs lem-sc-closed-irreducible-dimension-trdeg: the existing statement is about Dimension of an irreducible closed subset from its generic residue field; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-ci-local-ring-principal-neighbourhood: the existing node concerns A complete-intersection local ring has a principal global-complete-intersection neighbourhood; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-complete-intersection-fibres-limit-descent: the existing statement is about Descent of flat families with local complete intersection geometric fibres; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-completion-local-complete-intersection: the existing node concerns Complete-intersection neighbourhoods detected by the completed local ring; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-completion-regular-kernel-preservation: the existing node concerns Regular sequences and the canonical completed quotient presentation; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-flat-dense-generic-fibre-pure-dimension: the existing statement is about Pure dimension of fibres of a flat family with dense pure-dimensional generic fibre; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-formal-monoid-ring-dimension: the existing statement is about Dimension of a formal monoid ring and a parameter hypersurface; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-pure-relative-dimension-finite-stage: the existing statement is about Pure relative dimension descends to a finite stage; it asserts neither a maximal syntomic source open of prescribed pure fibre dimension nor the closed-geometric-point completed-ring characterization. The common tag is an auxiliary source citation, not an equivalent statement.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-regular-quotient-completion-kernel-test: the existing node concerns Regular-sequence kernels compared with a regular presentation of the completed quotient; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-relative-dimension-base-change: the existing node preserves an already assumed dimension or smoothness condition under base change; it does not produce the universal syntomic fixed-dimension locus in an arbitrary flat family.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-syntomic-geometric-fibres-affine-criterion: the existing node concerns Affine-local characterization of flat families with geometric complete-intersection fibres; its local/affine algebra or CI criterion gives no largest source open of fixed pure relative dimension commuting with all base changes.

lem-sfb-syntomic-fixed-dimension-locus vs lem-trf-syntomic-locus-base-change: the existing node isolates the entire syntomic locus, with no fixed relative dimension and no completed-ring/dimension criterion; the new node isolates its universal d-dimensional piece and states its geometric and completed-ring characterizations.

Additional concept comparisons: the item uses `lem-trf-nodal-open-locus` after verifying its pure-dimension hypothesis; neither new node is a replacement generalization of that nodal theorem. `lem-trf-nodal-family-etale-source-locality` handles schemes and source covers only, whereas the new chart node supplies algebraic-space target charts and arbitrary-space base changes.

## Validation

The preliminary server review_split passed. The first full dry run flagged the wording "the item's hypotheses" in step 6; replaced it with the explicit assertion that the base-changed morphism is flat and locally of finite presentation.
