# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-reduced-eta-normal.json`: split, ten proof steps; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-normal-approximation-finite-eta-modification.json`: new statement-only supporting lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-points-smooth.json`: new statement-only supporting lemma, unsplit; no Mathlib match.
- `citations.json`: complete verbatim statement quotations for every step/node citation.

Attachments: none. Searches of `WeilConjectures/` in slopmaster2 for the item's tag, eta-normality, geometrically reduced families, approximation and generic smoothness found no sorry-free declaration stating this item or either new supporting lemma. The upstream master is reference material only.

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Proposition 3.5.2 (printed pp. 20–21), §3.1 and Remark 3.1.1 (printed pp. 14–15), and §1.2, for the item and the approximation lemma. The imported source path is absent in the repository literature. I consulted the public text at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf and record the expanded proof as agent-written, not as an archived-document proof.

No correction to the imported statement is needed. I retained its text, including all semistable multipointed definitions, and restored its original blueprint ancestry/place. The split keeps the Temkin reducedness/approximation/smoothness/depth/Hartogs route. It uses the OPEN isomorphism locus of the finite morphism rather than treating the generalization-closed set in the source as open. The generic fibre is in the isomorphism locus by the modification hypothesis; it is not asserted to be smooth. A constant nodal family shows why those distinctions matter.

I removed two proposed new nodes during self-review: reduced nonminimal points have positive depth by the existing reduced-ring Serre criterion, and open depth-two extension is exactly the existing Hartogs restriction lemma. Those facts belong to citations and steps, not new nodes. The remaining two lemmas neither state eta-normality nor any clause of its conclusion: one supplies a Noetherian model, the other supplies relative smoothness at fibre-component generic points.

Mathlib queries are logged in `searches.jsonl` and transcribed exactly into the new nodes with result summaries/digests. Earlier invalid Loogle syntax and incorrectly prefixed grep paths are explicitly marked invalid, not evidence of absence; corrected comma-separated Loogle queries and grep searches in `AlgebraicGeometry` ran. Both semantic services were also searched, with second phrasings and a further affine-model phrasing. I read the reduced-family and smooth-morphism Mathlib sources: the former proves total-space reducedness (including the finite-irreducible-components version, applicable to integral bases), not triviality of finite eta-modifications; smoothness interfaces and normalization universal maps do not give the two new lemmas. No new Mathlib leaves are claimed.

Nothing mathematical is left unfinished in the item's proof at stage 1; the two explicitly stated supporting lemmas remain unsplit as required. No Lean was written and no compiler or build tool was run.

## Review by Q56

I compared the item with Temkin Proposition 3.5.2 under the paper's integral qcqs base convention, and checked §1.2 for the curve/marking application. Normality, flatness, finite presentation, reduced geometric fibres, finiteness and generic isomorphism are retained. The approximation node is restricted to affine bases, which suffices because the argument is local over the base; its normal integral Noetherian affine model, preservation of flatness and geometric reducedness, and modification diagram are the inputs of the source's noetherian-reduction paragraph, §3.1, Remark 3.1.1(i), and its affine-base remark. It defines eta-modification and schematic density inline and cites its other notions. It does not assume the finite modification's source flat. The generic-smoothness node agrees with Stacks 056V (`lemma-geometrically-reduced-dense-smooth-open`) plus 01V9 (`lemma-smooth-at-point`, (1) iff (2)); I read both source statements and the dense-smooth-open proof. A dense open of a Noetherian fibre contains all component generic points; flatness gives relative smoothness there. This node asserts nothing about arbitrary points of the generic fibre.

Step 1 cites the flat-invertible-sections torsion-free statement for the trivial invertible sheaf, not merely the definition of flatness. On affine charts generic localization is injective, and an algebraic-closure extension is injective on vector spaces; nilpotents therefore vanish. The same calculation on an affine cover gives the sheaf restriction injection used later.

Step 2 uses exactly the normal approximation node's compatible base-change diagram. The existing finite-type-over-Noetherian statement applies after approximation to the finitely presented family and the finite modification. Taking the base change of an inverse is the elementary reason that an isomorphism of the model suffices. No flatness of the modification source is used.

Step 3 uses the finite-morphism definition's affine finite quasi-coherent algebra clause. I wrote the finite-module support argument: a finite list of generators vanishing in a stalk is killed on one principal neighbourhood. Thus the unit's kernel/cokernel define an open isomorphism locus containing every generic-fibre point. This step makes no unsupported openness assertion about the union of fibre generic points.

Step 4 uses the actual schematic-density definition on the source, together with Step 1 (and the cited torsion-free statement on the flat open V), to show that a section of the finite algebra vanishing generically is zero. This excludes a finite algebra with an additional vertical summand. It gives both inclusions needed for Hartogs; they do not follow from finiteness alone.

Step 5 uses the generic-smoothness node only at fibre-component generic points. The affine-smooth/ring-smooth equivalence explicitly bridges the smoothness conventions, and smooth-over-normal-ring-normal then applies because the base affine rings are normal at all primes. This proves normality on smooth open neighbourhoods, without assuming that the normal locus of an arbitrary Noetherian scheme is open.

Step 6 applies the existing normal-dense-open-integral-section statement to affine H in that normal neighbourhood and its dense intersection with the common isomorphism open V. The finite-algebra-is-integral statement supplies the needed monic relation. Density on the source makes the extended function equal to the original algebra section; Step 4 supplies injectivity. Thus every fibre-component generic point lies in W. I read both cited statements: the extension statement allows disconnected or empty affines and requires only locally Noetherian normality and a dense open, all present here.

Step 7 uses the exact reduced-ring S1 inequality of the Serre-criterion node and the flat-local-depth formula, not their definitions or proofs. The fibre local ring is Noetherian and reduced; its point is nonminimal since W contains fibre generic points. Its dimension is therefore at least one. The base point is nongeneric since W contains the generic fibre; a nonzero element of the maximal ideal of its local domain gives base depth at least one. The closed fibre of the flat local ring map is the local fibre ring used in the formula. I checked Stacks 031R (`lemma-criterion-reduced`) and 0337 (`lemma-apply-grothendieck`) in algebra.tex.

Step 8 invokes the exact open Hartogs statement with N=O_Z, which is finite on affine charts and at stalks. Noetherianity and depth at every complementary point were established. I checked Stacks 0E9I (`lemma-depth-2-hartog`) in divisors.tex. The inclusions from Step 4 then force the finite algebra to equal O_Z, and the affine Spec description makes f an isomorphism. This replaces only the source's generalized Z-closure notation by its already available open version, preserving the depth route.

Step 9 explicitly verifies reducedness at nodal points. The existing Krull-intersection-Jacobson statement gives injectivity of a Noetherian local ring into its maximal-ideal completion; I checked 00IQ (`lemma-intersection-powers-ideal-module`, part (2)). The two-axis injection proves reducedness of Omega[[u,v]]/(uv), including positive characteristic. The smooth-geometrically-reduced statement supplies reducedness on smooth opens. Step 10 uses the existing etale-smooth-zero-dimensional-fibres statement to bridge the marking's etale and smooth conventions, and again the smooth-geometrically-reduced statement. Flatness and finite presentation of both curve and marking are in the item's own multipointed definition.

I checked B1–B10: both new nodes are self-contained statements only, with empty proof/dependency-of-proof fields, actual searches, single TeX backslashes, source places and complete blueprint links; no new definition or unsupported attachment was introduced. C1–C8: all non-elementary facts are cited, every cited statement was opened, the verbatim quotations record the exact inputs, and off-unit tools are declared under split_report.tool_uses without changing the unit route. D1–D5: the item carries the finite-algebra argument, depth calculation and conclusion; neither new lemma relabels the conclusion. E1–E7: the checks above account for normality and Noetherian hypotheses at each application, distinguish fibre local rings from unlocalized fibre rings, and spell out density rather than saying an inclusion is clear. I checked all step lengths; none exceeds 2,000 characters.

Small cases checked: empty Z (vacuous conclusions and empty model), a base field (generic fibre equals Z, so a modification is already an isomorphism), an affine line over a normal domain (generic localization injection), and a constant nodal curve (its node need not be smooth, while the component generic points are smooth). A minimal fibre point is deliberately excluded from the depth-one argument. Empty marking and disconnected geometric fibres are allowed. The affine approximation lemma neither forces properness nor separatedness of the family; the generic-smoothness lemma neither assumes perfect residue fields nor asserts a whole fibre smooth. Removing flatness would invalidate the generic-injection calculation, and replacing schematic density by topological density would invalidate the finite-algebra inclusion, so neither hypothesis has been silently dropped.

## Not duplicates

The approximation source's arXiv number is mechanically read as tag 0707; the following comparisons distinguish the actual statements even though the common token is bibliographic.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-geometrically-reduced-eta-normal: the item concludes reducedness and triviality of finite generic modifications; the new node supplies a Noetherian diagram and asserts no triviality.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-birational-quasi-modification-common-cover: the existing node constructs common proper covers of valuation-covering quasi-modifications; it does not approximate a finite diagram over a normal affine base.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-marked-curve-finite-type-model: the existing node models a marked curve with smooth generic fibre; it neither handles arbitrary-dimensional geometrically reduced families nor descends a supplied finite modification.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-marked-nodal-dualizing-degrees: the existing node constructs dualizing line bundles and degree formulas, not Noetherian models.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-riemann-zariski-finite-refinement: the existing node gives valuation-space compactness and model refinements, not this finite-diagram approximation.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-semistable-marked-base-change: the existing node preserves marked semistability under supplied base changes; it does not construct a normal Noetherian model.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-stable-curve-diagram-noetherian-model: the existing approximation requires marked curves with smooth generic curve and semistable modification sources; the new node permits any relative dimension and arbitrary finite eta-modification sources, with no semistability or source flatness hypothesis.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-stable-modification-finite-presentation-spread: the existing node spreads proper pairs from valuation bases to quasi-models, assuming the source pairs flat and finitely presented; it does not approximate arbitrary finite modifications of arbitrary-dimensional families.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-stable-modification-spreading: the existing node spreads stable marked-curve modifications from valuations; it does not supply the general finite-diagram approximation here.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-stable-modification-stability-locus: the existing node spreads a supplied stable fibre condition in a marked-curve diagram over an existing model; it does not construct this general model.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-stable-modification-uniqueness-normal: the existing node identifies two stable curve modifications; the new node only models one finite modification and gives no uniqueness or isomorphism conclusion.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-horizontal-curve-models: the existing node gives flatness and generic closure properties for curves over finite-height valuation rings; the new node descends a diagram over an arbitrary normal integral affine base.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-semistable-dominates-stable: the existing node factors semistable curve modifications through stable ones over valuations; the new node gives a Noetherian model in arbitrary relative dimension.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-semistable-stable-contraction: the existing node contracts semistable curves to stable modifications over valuation rings; no such contraction is asserted by the new approximation node.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-strict-semistable-cofinality: the existing node refines modifications of strictly semistable valuation curves; the new node has no strict-semistability or refinement conclusion.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuative-domination-eta-normal: the existing node assumes eta-normality to globalize valuative factor maps; the new node assumes no eta-normality and gives only approximation.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-strict-semistable-local-uniformization: the existing node produces strictly semistable valuation-local quasi-modifications; the new node descends a finite morphism without uniformization.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-stable-reduction: the existing node constructs stable curve modifications over valuations; the new node neither constructs stability nor requires a valuation base.

- lem-trf-normal-approximation-finite-eta-modification vs lem-trf-valuation-marking-semistable-separation: the existing node separates markings by a semistable valuation-curve modification; the new node has no marking or separation construction.

- lem-trf-generic-fibre-points-smooth vs lem-pur-geometrically-reduced-dense-smooth-open: the existing node gives dense absolute smoothness over a field; the new node concludes relative smoothness over S at component generic points, using the pointwise flat-fibre criterion as well.

- lem-trf-generic-fibre-points-smooth vs lem-trf-smooth-at-point-differential-criterion: the existing node characterizes smoothness by differential-generator bounds; it does not derive those bounds from geometrically reduced fibres.

- lem-trf-generic-fibre-points-smooth vs sbc-lem-smooth-criterion: the existing node requires every whole fibre to be smooth to conclude global smoothness; the new node allows singular fibres and only concludes smoothness at their generic points.

- lem-trf-generic-fibre-points-smooth vs sk-thm-geo-generic-open: the existing node is constructibility and cohomological base change after shrinking an integral finite-type base, not smoothness at fibre-component generic points.
