# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-torsionfree-rationalization-injective.json`: statement; split into four steps using existing localization and tensor-product nodes. No exact Mathlib leaf for the tensor-Q map was found; related localization injectivity APIs need the identification supplied in the proof.
- `citations.json`: one entry per cited node per proof step, with verbatim statement quotes.
- `report.md`: this report. `searches.jsonl` is the required search command's unchanged log.

No new nodes, definitions, Mathlib leaves, Lean files, or unit files were created.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, rationalization, torsion-free notions, and tensor-map injectivity found no declaration for arbitrary torsion-free abelian groups and tensoring over Z with Q. `AddCommGroup.rationalTateModule.injective_one_tmul` (GroupTheory/TateModule.lean:315) is a genuine, but different, theorem about Tate modules over Z_l and Q_l; it does not give this item under its hypotheses. Categorical rationalization-map injectivity is likewise a different statement.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 pp. 7–8, for lem-trf-torsionfree-rationalization-injective. The exact path in the node is absent locally. No document was downloaded. The split is instead an explicitly agent-written proof from the locally read Stacks algebra source, not a claim to have read Temkin.

## Findings and changes

The initial item has a true self-contained statement, one rational-rank definition dependency, and no proof. I kept its statement, chapter, unit, creator, and blueprint ancestry unchanged, and supplied the proof. The mathematical content is independent of finite generation, finite rational rank, an order, and divisibility. The retained statement dependency def-trf-rational-rank defines the rationalization mentioned in the statement; the proof uses no dimension inference.

The inherited four Mathlib records belong to the Q50 creation and remain intact. I ran the command-required LeanFinder, Loogle, grep, and LeanSearch queries and a second semantic phrasing, read their hits, and appended their actual log entries. One initial grep passed two directory names as one argument and returned no hits: its verdict explicitly says so and later searches inspect the actual localization directory/file. The usable Loogle query returns `IsLocalizedModule.injective_iff_isRegular` (LocalizedModule/Basic.lean:562); that statement requires a map already known to be a localization. The result does not by itself identify the tensor-Q map. `Algebra.TensorProduct.mk_one_injective_of_isScalarTower` (TensorProduct/Basic.lean:562) requires a compatible Q-module structure on G, which a general torsion-free group need not possess (Z is an example). `DivisibleHull.coe_injective` concerns another model whose comparison with the tensor is not definitional. These are not exact or one-line matches, so this is a split, not a new or relabelled leaf.

Whole-DAG searches for torsion-free rationalization injectivity, 00DK, 07JZ, and tensor-localization found the existing definitions and the existing Mathlib tensor-localization leaf used here. Whole-blueprint searches for “torsion-free rationalization injective”, “torsionfree”, “localization tensor”, and “rationalization” found no equivalent imported group statement. I also read lem-trf-rational-rank-zero-torsion: its conclusion only applies when the whole rationalization has dimension zero, and so cannot replace an argument about the kernel for arbitrary rational rank. Its localization route confirms that the relevant general dependency is already present. No new nodes were needed.

## Not duplicates

No new nodes; hence no new/existing node pairs. The item was already present, and the proof cites rather than recreates the existing tensor-localization statement.

## Review by Q30

I read the item, its rational-rank definition, the complete statements of all three proof dependencies, the chapter/unit records and the current main-20261015 lem-trf-local-term-locality statement and proof. The current locality proof is the contracting-correspondence/normal-cone route; this item is an inherited elementary algebra input farther down its existing ancestry, not a replacement of a unit step. All off-unit proof dependencies are existing definitions or Mathlib leaves, so there is no additional tool-use request.

For the mathematical source I read Stacks algebra.tex's module fraction construction immediately before Definition 07JZ (definition-localization-module), the localization map, Lemma 00CX (lemma-tensor-product) and its construction/universal property, Lemma 00DK (lemma-tensor-localization) including its explicit fraction formula and proof, and the bimodule associativity statement 00D2 behind the existing generalized comparison. I verified the tags against tags/tags. Temkin's named PDF is unavailable, as reported above; no new node needs a separate source check.

Step 1 cites def-weil-pbc-module-localization, whose statement gives exactly the fraction equality and arithmetic formulas used to identify S^{-1}Z with Q. The nonzero integers form a multiplicative subset because Z is a domain. Cancelling the nonzero integer in u(ta-sb)=0 is valid in Z; the same cancellation is not asserted in G. Surjectivity is the ordinary numerator/denominator representation of a rational. This is an explicit elementary fraction computation, not an uncited localization theorem.

Step 2 cites def-weil-pbc-module-tensor-product for its bilinear universal property and pure-tensor generation, and def-weil-pbc-module-localization for induced maps. I checked that the tensor node actually states both universal property and generation, and that the localization node actually states the formula m/s -> h(m)/s. The maps Z tensor G -> G and G -> Z tensor G are inverse by the written pure-tensor calculation; their localized maps are inverse on each fraction by the written formulas. This elementary unit calculation requires only the canonical Z-module structure of an abelian group.

Step 3 cites lem-weil-pbc-localization-tensor-over-base, whose statement is the isomorphism T^{-1}(M tensor_R N) -> T^{-1}M tensor_R N with exactly the formula used. I checked R=A=Z, T=S, M=Z, N=G against every hypothesis: rings are commutative, S is multiplicative by Step 1, and all modules are as required, with no finite presentation, flatness or torsion-free premise needed. This node is a Mathlib leaf, not merely a definition. The other citation is the tensor-product definition: the symmetry maps are well-defined by its universal property and are inverse on generating pure tensors. The composite isomorphism has the displayed formula g/s -> g tensor (1/s); thus it sends g/1 to the actual canonical map of the item, not an unspecified isomorphic embedding. This is the only non-elementary step and cites the comparison theorem explicitly.

Step 4 cites the module-localization definition, whose statement explicitly gives m/1=0 iff some element of S kills m, and the tensor-product definition for additivity. I checked the positive-integer hypothesis carefully: the localization annihilator s may be negative, so the step replaces it by -s in that case. The positive case applies the hypothesis directly. Applying this to g-h proves equality of the original elements, which is full injectivity and not merely a zero-kernel statement left unexplained.

I tested G=0, G=Z, G=Q and an infinite direct sum of copies of Z: no step assumes nontriviality, finite generation or a finite basis. As a negative check, for G=Z/2 the fraction construction makes its tensor with Q zero, but Step 4 fails exactly because the torsion-free hypothesis is false. Negative denominators and the element 0 cause no exception. No assertion about all abelian groups injecting into their rationalization was introduced. I checked the B–E failure modes: no new statement-only node hides a proof; no duplicate or self-clause is created; every non-elementary assertion has a cited statement that says it; no source proof is being mined for stronger unstated content; the three dependencies do not depend on the item; all TeX is encoded once; and every proof step is below 2000 characters. The correction made during self-check was to record the ineffective combined-directory grep honestly and follow it with searches of the real localization source. The statement itself needed no correction.

## Unfinished work

None for this split. The missing Temkin archive is documented; the self-contained proof does not depend on a claim taken from that unavailable source.
