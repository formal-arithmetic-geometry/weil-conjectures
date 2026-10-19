# Stage 1 report

## Worker report

Files written:

- `dag/nodes/sec-purity-real-sheaves/thm-wf-rank-one-finite-geometric-image-curve.json`: repaired split of the existing item; five steps, no statement change, no new nodes and no new Mathlib leaves.
- `citations.json`: eleven entries quoting the full current statement of each node cited by each proof step.
- `searches.jsonl`: seven actual Mathlib searches recorded by `msearch.py` during this repair.
- `report.md`: retained findings and updated review below.

Attachments: none. The related declarations `AlgebraicGeometry.WeilGroup.exists_pow_eq_one_of_continuous` (`RankOne.lean:114`) and `AlgebraicGeometry.WeilGroup.finite_range_of_continuous` (`RankOne.lean:229`) use an abstract `WeilGroup p`, `PadicAlgCl` and additional smooth-curve/étale-quotient instances; they do not directly state every hypothesis and clause of this normal pure-dimensional curve statement with finite coefficient extension. `FundamentalGroup.lean:172` proves only the cohomological step. I reopened the tagged declarations and their surrounding hypotheses in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/EtaleCohomology/Purity/RealSheaves/`; no attachment was claimed.

WANTED: none.

The original delivery already expanded coordinate scaling, Frobenius invariance and the finite-roots conclusion. Those arguments and the original target statement are retained. The repair adds the exact current hypotheses, the missing coefficient-domain comparison, and existing supporting citations. Nothing remains unfinished in the split. No Lean was written or compiled.

## Returned delivery repaired

Return L concerns head `6542e35c04`: `lem-wf-additive-characters-h1` changed statement after the original review, so landing refused it. I compared the retained item with the current shared item and read the current statements of every retained dependency. The delivery tool rebases the sandbox changes onto the current server DAG; no git command was run in the shared repository.

The H¹ lemma now explicitly assumes a finite base field and a prime different from its characteristic, and explicitly specifies the valuation topology on the adic integers. Step 3 sets the field to the target's finite field, writes $q=p^b$ to derive $\ell\ne p$ from $\ell\nmid q$, checks the geometric hypotheses, and identifies the topology used in step 2 with the lemma's topology. It uses the unchanged inverse-conjugation formula, not a guessed Frobenius convention.

Reading the other current dependencies exposed an additional C4 issue: `lem-wf-compact-character-logarithm` guarantees that the powered values lie in $1+\ell^2\mathcal O_E$, but its statement does not guarantee the relationship of its auxiliary integer $r$ to the injectivity threshold. The retained step 2 took that relationship from the lemma's proof. The repaired step 4 instead chooses $r=2v_E(\ell)$ itself and proves $\ell^2\mathcal O_E=\mathfrak m_E^r$ from the existing DVR statement. The strict threshold holds even for $\ell=2$. This repairs the split itself; it is not an unchanged re-push.

The first dry run exited with a missing-`citations.json` error. That file was absent from the retained sandbox, despite being mentioned in the earlier report. I reconstructed all entries from the current cited statements. The earlier report also mentioned search logs absent from this retained sandbox; I ran and read fresh searches, now recorded in both the item and `searches.jsonl`, without inventing earlier records.

## New nodes

None. The continuity, compactness, exact-sequence and DVR facts were all found in the existing DAG. Therefore there are no new statement-only nodes, duplicate-tag pairs, new-node source obligations or new-node Mathlib searches to assess.

## Review by Q145

I read `coord/delivery-errors.md` B–E whole and checked this repair against each applicable point. The item source is the complete master node `literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-p-real-rankone/thm-wf-rank-one-finite-geometric-image-curve.md`. I reread the current `main-20261015` statement/proof and the chapter and unit records. The first source paragraph is now steps 1–3, the second is step 4, and the third is step 5. This keeps the additive-character/logarithm route of unit steps 3–4. I also read the current blueprint statements of the H¹, compact-logarithm, deep-logarithm and no-fixed-class dependencies, plus the current compact/deep logarithm proofs to locate the domain issue. No SGA source is used.

Step 1 uses the statement of `lem-wf-weil-group-exact-sequence`, which explicitly says the degree homomorphism is surjective, to choose the lift. The previous definition-only citation did not explicitly assert surjectivity. The target's geometrically connected, separated, finite-type scheme meets that lemma's hypotheses. The current statement of `lem-wf-compact-character-logarithm` supplies a continuous additive map, invariance under both conjugations and the domain $1+\ell^2\mathcal O_E$. The step takes exactly these clauses.

Step 2 uses `def-galois-fibre-functor` for the small skeleton, finite fibres and evaluation topology, and `lem-galois-aut-profinite` for profiniteness with those precise hypotheses; compactness follows from profiniteness. For the coordinates it cites the existing Mathlib leaf `lem-sfb-finite-dimensional-linear-map-continuous`, with scalar field $\mathbf Q_\ell$ and source $E$, rather than assuming coordinate continuity. Completeness and the nontrivial absolute value of the scalar field, finite dimension and the Hausdorff valuation topology of the source all hold here. `def-weil-l-adic-numbers` identifies the unit ball with $\mathbf Z_\ell$ and gives $|\ell^a|_\ell=\ell^{-a}$. The finite-subcover argument bounding all coordinate images is written explicitly, and continuity into the unit-ball subspace follows from continuity into the ambient field. Finite-dimensionality gives finitely many coordinates, so one exponent suffices.

Step 3 uses the entire isomorphism and the explicit Frobenius formula in the current `lem-wf-additive-characters-h1` statement. I checked its newly explicit characteristic hypothesis and topology as described above. The Frobenius-fixed family belongs to the ordinary inverse limit actually stated by `prop-wf-open-curve-h1-no-frobenius-fixed`; the target supplies its normality, pure dimension one, connectedness, separatedness, finite type and prime-to-$q$ condition. The inverse of the additive isomorphism, nonzero scalar cancellation and basis coordinates then give zero logarithm. No cohomology comparison or torsion-freeness lemma is silently introduced.

Step 4 cites `lem-weil-l-adic-extension-integers-dvr` for the uniformizer, its maximal ideal and the unit-times-uniformizer expression of $\ell$. Multiplying these principal ideals gives the displayed domain equality in a few lines; it is an elementary specialization of that existing statement, not a new lemma. `lem-wf-deep-principal-unit-log` explicitly makes log and exp inverse on this domain because $2e>e/(\ell-1)$. `lem-wf-compact-character-logarithm` explicitly supplies the same logarithm series and the powered values in that domain. Thus the conclusion follows from the statements, not the construction hidden in a dependency proof.

Step 5 is the elementary nonzero-polynomial root bound over a field and the exponent of a finite group. I checked $N\geq1$ (so the polynomial is nonzero), the trivial image (exponent $1$), $E=\mathbf Q_\ell$, ramified extensions (the parameter $e$ is retained) and $\ell=2$ (the threshold remains strict). Empty schemes cannot occur with the chosen geometric point and geometric connectedness convention. There is no excluded proper/open case in the no-fixed-class citation. Every step is shorter than 2000 characters. The non-elementary inputs are all explicit citations with verbatim current-statement quotes in `citations.json`.

The generic automorphism-group compactness and coefficient DVR inputs are declared in `split_report.tool_uses`: they support the existing unit argument and do not replace its route. Coordinate continuity is already a Mathlib leaf. No maintainer-owned `tool_uses` field or unit/chapter metadata was edited.

Mathlib searches were made only with `msearch.py`: LeanFinder and Loogle with two phrasings each, grep with two patterns, and LeanSearch. I read every result. Loogle and grep returned no hits; the semantic results concern cyclotomic characters, Galois groups, algebraic character spaces or function-field class groups and do not state the item. In particular `MulChar.finite` assumes finiteness of the source units and concerns the set of characters, while `PadicInt.continuousAddCharEquiv` has the adic integers as source and a multiplicative target; neither proves finite geometric monodromy. All seven exact queries, result summaries and no-match verdicts are in the item, with their command-generated log records. No new search was needed for an existing dependency.
