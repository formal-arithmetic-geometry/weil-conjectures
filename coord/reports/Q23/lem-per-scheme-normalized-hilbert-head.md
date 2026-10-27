# Q23 stage-1 report: lem-per-scheme-normalized-hilbert-head

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-scheme-normalized-hilbert-head.json: item, statement, split in fourteen explicit steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-hilbert-specialization-component-persistence.json: statement-only specialization/component lemma, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-hilbert-test-component-retention.json: statement-only near-point/component lemma for nilpotent schemes and finite presentation tests, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node pair.
- searches.jsonl: actual msearch.py records, retained without editing.

No repository, launcher, Lean, unit or chapter files were written. There was no earlier sandbox node, proof or report to preserve. Additional scratch script write_split.py is only a sandbox generation aid.

## Attachments

None. Searched lean/WeilConjectures for the item tag, Hilbert--Samuel/hilbertSamuel and normalized Hilbert terminology, and for the proposed new ids. No project declaration states these results. In particular no sorry declaration was mistaken for a finished attachment.

## WANTED

WANTED: Bierstone--Milman--Temkin, Q-universal desingularization, arXiv:0905.3580v1, local archival PDF, sections 6.1--6.3 and Remark 6.2, for the item and both new nodes. The listed archival path is absent locally. Read the primary source online at https://arxiv.org/html/0905.3580v1 and https://arxiv.org/pdf/0905.3580 instead; no download was written to the read-only literature tree.

WANTED: detailed nonreduced near-point/equality-case proof behind the common-presentation assertion in BMT section 6.3 (BM2 Chapter III/BM4 section 7), for lem-per-hilbert-test-component-retention. BMT states the common-presentation assertion; it does not give a full independent proof of this extracted input. The item is consequently marked agent-written, not a transcription of a fully proved archival lemma. No SGA source was used.

## Source error / STATEMENT-DISPUTED

STATEMENT-DISPUTED: the imported words "least occurring regular head" can assert existence on every input, which is false. Take X = Spec(Q[e]/(e^2)). It has one point, q=0, c=1 and h=(1,2,2,...). Its unique local ring has dimension zero and embedding dimension one, hence no point is regular and the head (1,(1,1,...)) never occurs. The empty scheme is another edge case. Corrected only this wording to a universal lower bound, with equality exactly at regular points. This is what BMT's smooth/singular distinction and the upstream callers need. The full nilpotent scheme structure is retained throughout.

Also made the extended function explicit in the item statement as H_X(x)=Lambda^{trdeg_Q kappa(x)} h_x, and added its residue-field/transcendence-degree definition dependencies. This introduces no new hypothesis or changed convention.

## What was wrong / choices in the split

The item had no proof. Its reduced companion, lem-trf-hilbert-samuel-smooth-dimension-profile, supplies useful explicit algebraic arguments but cannot be applied as a theorem: the hypothesis "reduced" is missing here. In particular its proof uses the reduced closed union of selected components, which agrees with X near a point only under reducedness. That argument must not be copied for schemes with nilpotents. The new specialization node concerns the full scheme instead. A way to prove it is to take the scheme-theoretic closure of an open obtained by deleting components not passing through z; this agrees with X near z while retaining nilpotents. A lost component through x makes its kernel ideal nonzero at x. Krull intersection and length additivity give a strict colength drop, and extended upper semicontinuity for that closure gives the contradiction. This sketch is report material, not a proof placed inside the unsplit new node.

Similarly, lem-trf-hilbert-samuel-equality-component-rigidity explicitly assumes reducedness. The new near-point node removes that restriction and exposes the extra finite-test compatibility which is necessary for the actual presentation statement. It does not assert existence of a presentation or any normalized invariant. Merely using nonincrease of H without its equality-case component rigidity would leave a gap at blowup steps. Merely saying "same tests" without checking exceptional-intersection auxiliary tests would also leave a gap; that exact input is now queued in the new node.

Elementary telescoping, finite-set inclusion/cardinality and the infinite-subsequence argument are proof steps, not new nodes. The two new statements are structural component-retention facts with independently specified hypotheses; neither restates A_X, semicontinuity of A_X, a regularity criterion, or a normalized-head presentation. No resolution algorithm or assertion that a numerical maximum locus is regular is added.

## Not duplicates

lem-per-hilbert-specialization-component-persistence vs lem-trf-hilbert-samuel-smooth-dimension-profile: the existing theorem assumes reducedness and concludes properties of the corrected invariant; the new node allows nilpotents and concerns actual components through two specializing points with equal extended colength, without defining or asserting a corrected invariant.
lem-per-hilbert-specialization-component-persistence vs lem-trf-hilbert-samuel-equality-component-rigidity: specialization inside one possibly nonreduced scheme differs from the existing reduced-only equality statement for a point above a blowup center.
lem-per-hilbert-test-component-retention vs lem-trf-hilbert-samuel-equality-component-rigidity: the existing node assumes reducedness and treats one permissible blowup; the new node allows nilpotents and includes the retained component profile through the full presentation tests, including prescribed cartesian auxiliary tests.
lem-per-hilbert-test-component-retention vs lem-trf-hilbert-samuel-near-normal-cone: the existing normal-cone theorem has reducedness and a normal-flat center and describes near-point cones/linear directions; the new node states global component dimension retention for arbitrary nonreduced inputs under the stated locally H-constant tests.
lem-per-hilbert-test-component-retention vs lem-per-scheme-hilbert-samuel-test-presentations: the existing theorem supplies presentations, nonincrease and DCC of H but does not assert survival of the component dimension profile at near points; the new node is conditional on a supplied presentation/test sequence.
lem-per-hilbert-specialization-component-persistence vs lem-per-scheme-hilbert-samuel-test-presentations: the latter does not identify the components through comparable points with equal H; upper semicontinuity alone is insufficient.

Searched the entire DAG by Hilbert/Samuel, component/equality/specialization/retention, the near-normal-cone vocabulary, and the new ids. Ran blueprint_refs.py ancestor and searches for Hilbert, Hilbert Samuel, Hilbert--Samuel, equality component, and component persistence: the only broad Hilbert hits were unrelated blueprint Hilbert-polynomial/Hilbert-scheme/Hilbert-90 statements. Read the latest ancestor proof, not an older snapshot. The new ancestry places name its Step 3 regular-resolution branch and the BMT 6.3 subargument. All same_as fields remain empty.

## Review by Q23

I read the latest chapter/unit records and the latest blueprint ancestor lem-per-artin-gabber-affine-curve, especially Step 3. Its current text has no Hilbert--Samuel construction to identify with either new statement. The delivery stays below the existing regular-resolution branch. I read BMT sections 6.1 (definition of the extended function and four numerical properties), 6.2 (the actual tests, not just initial cosupport), and 6.3/Remark 6.2 (Gabber's component-count/minimum-dimension correction and the common-presentation/component-locus assertion). BMT defines a variety as an arbitrary finite-type scheme over a field; it does not impose reducedness. The all-points version uses local component dimensions and the residue-field transcendence correction, rather than treating a closed-point formula as valid unchanged at every point.

For the specialization node I checked its objects and the closure argument just described against the actual scheme-theoretic kernel, and against Stacks 00IV (algebra.tex, lemma-length-additive), Krull intersection, and the nonreduced presentation node's upper semicontinuity. It is a separate unsplit lemma because the scheme-theoretic component-persistence comparison is precisely the structural assertion the reduced proof did not give. For the near-point node I read the statements of the reduced equality-component and near-normal-cone nodes to rule out an illicit application. The required extension and auxiliary-test retention are stated explicitly, not attributed to a Stacks tag that only gives a dimension formula. Its source is BMT 6.3/Remark 6.2; it remains queued with no claimed proof.

Step 1: checked telescoping including index zero and first-difference preservation for arbitrary integer sequences. Thus negative entries after higher differences cause no order problem, and cancellation never drops initial entries.

Steps 2--3: opened lem-trf-smooth-local-tangent-cone-extension. Its statement allows nonreduced local Q-algebras and gives both the graded polynomial extension and the set of minimal-prime quotient dimensions. The maximal-ideal filtration and length additivity give the convolution/summation formula. The Spec/minimal-prime component node states the required identification. The fibre-local dimension s is used, not the global relative dimension; nontrivial residue-field extensions change no vector-space dimensions. No quasi-compactness of an arbitrary smooth source is assumed: the argument takes finite-type source neighbourhoods. The finite-type-over-Noetherian node supplies Noetherianity for X over Q.

Steps 4--5: the regular-local-domain statement supplies c=1 and q=d at a regular ring. The generator/regular-sequence node and the graded-polynomial node give the monomial bases, and length additivity computes h. Read Stacks 00LN (lemma-regular-quasi-regular) and the displayed polynomial graded description preceding it in algebra.tex. The converse uses only the exact cotangent-dimension inequality/equality criterion actually stated by lem-weil-pbc-regular-local-cotangent-dimension. If c=1 then every local component has dimension q, so d=q; entry 1 becomes 1+e-q. These arguments require no reducedness of a nonregular ring.

Step 6: read both cited dimension statements and Stacks 00P0/00P1 (algebra.tex, lemma-dimension-prime-polynomial-ring and lemma-dimension-at-a-point-finite-type-field). Applied to each reduced integral component, not to an allegedly reduced X, they give dim O_{Z,x}=dim Z-t_x. Thus q=min P-t_x and B_D=(|P|,Lambda^{D-min P}H). This also checks q<=D and nonnegative summation exponents.

Steps 7--8: step 7 cites exactly the new specialization statement, including actual components and nilpotents; step 8 is only inclusion of components under specialization. It does not use the new node's proposed proof as additional unstated data.

Step 9: the cited nonreduced presentation statement says finite image and closed upper level sets of H. The finite-components statement gives finitely many profiles P. In a neighbourhood of x all profiles are subsets of P(x); a smaller cardinality strictly lowers the first coordinate and equal cardinality forces the same minimum. This proves the claimed topology and finite image of B_D and hence A by the single common summation order isomorphism.

Step 10: the cited sober/finitely-many-components statements apply to the locally closed level sets with reduced induced structure, regardless of nilpotents in X. For comparable points equal H implies equal profile by step 7; equal B implies equal H by finite-set inclusion and cancellation. A generic-point comparison in both directions then identifies irreducible components of the two sorts of levels. I checked the direction of specialization and maximality in this argument.

Step 11: shrinking removes finitely many components of the H-level not meeting x; on each remaining component use its generic point, step 7 and specialization to x to keep P fixed. Hence the two retaining loci agree near x. The nonreduced presentation node supplies an actual presentation with full tests, not just an order locus. Smooth locally head-constant centers are locally H-constant there; no claim that a disconnected center has a single global H value is needed.

Step 12: the new test-component statement supplies precisely the profile inclusion and equality case at a permissible blowup, which the presentation statement alone lacks. The latter supplies H-nonincrease. Equal-cardinality inclusion of profiles is equality of finite sets, giving the required fixed summation exponent; equality of B is equivalent to equality of H. Surviving ordinary strict-transform components retain a dense open and hence function field, so the cited finite-type-domain dimension theorem gives the same finite initial dimension bound, including components removed entirely by a blowup.

Step 13: read the exact finite-test definition and the nonreduced presentation statement. The new test-component statement explicitly covers every prefix, the auxiliary tests with ordinary pullback, ordered histories and the possible needed neighbourhood restriction. It gives P_0+r on the retained level after r line products and the local inequalities used for the reverse equality implication. With D+r the modified sequence sums r times, while A remains unchanged. The same presentation ideal is used at every prefix, so center admissibility and controlled/prescribed transforms agree. Empty cosupport removes the maximum only after all its presentations are resolved; it is not a global algorithm claim.

Step 14: the presentation node states reachable DCC from a fixed finite-dimensional initial input, not merely a fixed-space finite-image result. After eventual constancy of the first coordinate and an infinite subsequence of constant minimum component dimension, cancellation turns strict head descent into strict descent of the reachable H values. I checked that plateaus and varying history lengths are allowed by that statement. Ordered earlier centers only restrict admissibility and do not change this computation.

I checked B--E of delivery-errors point by point: statements introduce all objects; new nodes contain no proof or proof-dependency list; definition dependencies name their notions; TeX uses single escapes after JSON decoding; all Mathlib searches were actually run and their result records retained; no result was identified with a search hit that only mentions a similar word. Loogle/grep had no Hilbert--Samuel result. LeanFinder and LeanSearch returned basic scheme topology, smoothness, graded-ideal extensionality, normalization, or Krull-dimension inequalities, whose signatures do not state either new assertion. The grep hit Geometrically/Reduced.lean:97 was read in context and is only specialization from generic points in a reducedness argument. The general algebra facts reused from other units are individually declared as tool uses in split_report, with reasons.

Small cases checked: empty X; a field (s=q=0); regular affine space at closed and generic points; dual numbers and dual numbers times affine space; residue-field extension with fibre-local dimension zero; unequal-dimensional components meeting at a point; disappeared components; zero-length histories and line products. In particular the dual-number head is greater than the regular head without replacing X by its reduction. Every non-elementary step has a cited node; citations.json copies each cited statement verbatim. No proof step exceeds 2000 characters, and none hides a standard comparison under a word like "transport".

## What could not be finished

No obstruction to this one-level stage-1 split. The two new independent component-retention statements are intentionally unsplit and remain future queue items. No Lean proof, compiler run or completed resolution algorithm is claimed.

## Validation

Server review_split passed. The required deliver.py --no-push server preflight passed and printed OK at 21d512eb982 (not pushed); this includes check_dag and review_split in the temporary delivery tree. The first dry run rejected grouped definition references in one new statement; these were rewritten as individual bracket references and citations.json was regenerated before the passing run. All child search processes and the dry run exited before any push. A final dry run of this report-complete snapshot precedes delivery.
