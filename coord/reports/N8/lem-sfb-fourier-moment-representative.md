# Worker report: lem-sfb-fourier-moment-representative

Group N8, stage 1, 2026-10-24. Direct delivery; no second worker was started.

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-fourier-moment-representative.json`: item, statement unchanged, four proof steps, status split.
- `lem-sfb-bilinear-fourier-moment-regularity.json`: statement, Mathlib leaf `VectorFourier.contDiff_fourierIntegral`, FourierTransformDeriv.lean:507.
- `lem-sfb-l2-inverse-fourier-test-duality.json`: statement, Mathlib leaf `MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq`, LpSpace.lean:132, evaluated on a Schwartz test; inverse law from `MeasureTheory.Lp.instFourierPair`, same file:81.
- `lem-sfb-l1-bilinear-fourier-duality.json`: statement, Mathlib leaf `VectorFourier.integral_fourierIntegral_smul_eq_flip`, FourierTransform.lean:242.
- `lem-sfb-schwartz-test-inclusion-integrability.json`: statement, Mathlib leaves `HasCompactSupport.toSchwartzMap` and `SchwartzMap.integrable`, SchwartzSpace/Basic.lean:555,1131, one per clause.
- `lem-sfb-lp-local-integrability.json`: statement, Mathlib leaf `MeasureTheory.MemLp.locallyIntegrable`, LocallyIntegrable.lean:351.
- `lem-sfb-smooth-test-ae-uniqueness.json`: statement, Mathlib leaf `ae_eq_of_integral_contDiff_smul_eq`, AEEqOfIntegralContDiff.lean:195.

Also written: `citations.json` with all seven step/node pairs and verbatim statement quotations; `searches.jsonl` is the unmodified search-command log. `build_bundle.py` is a sandbox-only construction script, not part of the delivery. There are six new nodes, all six Mathlib leaves; none is a new unsplit obligation.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint id and for Fourier moments, representatives, Sobolev, Schwartz and Plancherel. The finite-field Fourier and Fourier–Deligne declarations have different objects and statements. No project declaration gives this analytic result. The six helpers are Mathlib leaves, not project attachments.

## Wanted literature

WANTED: Jean-Pierre Demailly, Complex Analytic and Differential Geometry, VI section 2, Sobolev lemma (2.1), original printed p.289, for lem-sfb-fourier-moment-representative. The PDF named by the inherited source field is absent locally. The official online URL timed out in this reading. Read the already-cited recomposed excerpt at https://totomityann.github.io/pdf/lua_agbook.pdf, PDF page 152 (zero-based page 151), including the preceding weak-derivative Sobolev definition and (2.1). This is context for the parent embedding, not a printed proof of the present Fourier lemma. No file was downloaded or written in literature/. The proof is marked agent-written and its actual analytic inputs are the Mathlib source statements read below.

## What needed correction or clarification

The item was an unsplit statement and the sandbox had no earlier node, proof, report or search log. Copied the item from the shared read-only repository, retaining all inherited searches and blueprint metadata. There is no statement dispute: the hypotheses include the zeroth moment, and that supplies the necessary L1 integrability of the Fourier representative.

The tempting pointwise inversion candidate `Integrable.fourierInv_fourier_eq`, Inversion.lean:165, assumes integrability and continuity of the original function at the evaluation point. The given original object is only an L2 class. I did not use that candidate. The actual proof compares the integral and the class against test functions and then applies ae uniqueness.

The ancestor command reports `blueprint.from.node = None` for this inherited long support chain. Retained that null and the existing detailed place; each helper adds its actual support input and prepends the item to `via`. No blueprint ancestor was fabricated. Searches of all imported blueprint nodes for Fourier, inverse Fourier, Schwartz, integrable, local integrability, continuous differentiability, test function and bilinear found no equivalent analytic node. The latest unit text in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` was read alongside the recorded chapter/unit. This supporting analytic lemma does not replace a unit step or change the inherited alteration/Hodge route.

## What could not be finished

No mathematical obligation remains in this split. The original Demailly PDF remains WANTED locally. No Lean file was written, and no compiler, Lake, build, or local forbidden checker was run. Delivery checks are performed by the required delivery command on the server.

## Not duplicates

No new helper cites a Stacks tag; there are no same-tag pairs to explain. Searched the whole DAG by concepts and by all proposed Mathlib declaration names, and read the matching statements.

- lem-sfb-lp-local-integrability vs lem-sfb-continuous-local-integrability: the former assumes Lp membership, with no continuity, whereas the latter assumes continuity on an open set. Reused the latter for g; the new node is only the Lp criterion for the representative of u.
- lem-sfb-smooth-test-ae-uniqueness vs lem-sfb-euclidean-sobolev-graph-mollification: the existing node's injectivity clause concerns two L2 functions and distributions with compact tests. The new statement assumes only local integrability; g is not known to be in L2 until after this step. It does not duplicate that weaker injectivity clause or use its proof.
- lem-sfb-smooth-test-ae-uniqueness vs lem-sfb-continuous-ae-pointwise: this new node derives ae equality from equal test integrals, whereas the existing node assumes ae equality of continuous functions and derives pointwise equality.
- lem-sfb-bilinear-fourier-moment-regularity vs lem-sfb-fourier-moment-representative: this is the general bilinear-phase Mathlib theorem, with no original L2 class or identification assertion. It is an existing library tool specialized by the proof, rather than a fresh unsplit restatement of the item.
- lem-sfb-l2-inverse-fourier-test-duality vs lem-sfb-fourier-moment-representative: the helper concerns arbitrary L2 transforms paired against Schwartz tests, with no L1 moments, no pointwise representative and no Cr assertion. It is the evaluation of a genuine Mathlib comparison theorem, not the item's ae identification in disguise.
- lem-sfb-l1-bilinear-fourier-duality vs lem-sfb-fourier-moment-representative: the new leaf is the general Fubini transposition identity for two L1 functions and a bilinear phase, not an L2 inversion assertion.
- lem-sfb-schwartz-test-inclusion-integrability vs lem-sfb-euclidean-sobolev-graph-mollification: the new leaf is the canonical inclusion and integrability of test functions, while the existing node asserts approximation of Sobolev functions in a graph norm.
- The grep matches in def-amb-vector-integration-charts, lem-asd-smooth-compact-dual-model and the scalar trace/duality nodes concern schemes and etale integration, not analytic functions on Euclidean space. They state none of these helper assertions.

## Review by N8

I read delivery-errors sections B through E in full and checked the actual node statements and source statements, not merely their titles. The six new nodes introduce every object and hypothesis, spell out the Fourier normalization, and give source declarations with the source lines read. Each is a direct Mathlib match or an evaluation/specialization with its exact reduction explained in `mathlib_match.how`. Each has the required real searches, with query texts copied from the log. None contains proof steps, proof dependencies, or a hidden proof sketch. The item retains its statement and every maintainer-owned field.

For step 1 I read FourierTransformDeriv.lean:498-524. `VectorFourier.contDiff_fourierIntegral` assumes precisely integrability of all norm-weighted moments up to the given order for a continuous bilinear phase. The new regularity node states that theorem, and step 1 supplies the phase minus the Euclidean inner product. Thus its negative exponent becomes the desired positive inverse exponent. The zeroth moment and the unit norm of the exponential establish absolute convergence independently of any convention for nonintegrable Bochner integrals. This step does not identify the integral with u.

For step 2 I read LocallyIntegrable.lean:351-358 and 552-569 and opened the full existing node lem-sfb-continuous-local-integrability. The new Lp node supplies local integrability of a measurable L2 representative with p=2 and locally finite Lebesgue measure. The existing node explicitly supplies local integrability for a function continuous on an open Euclidean subset; it applies with that subset equal to the entire space. It defines local integrability by finite integral on a neighborhood, which is the hypothesis used later. No global L1 assumption on u is introduced, and no L2 conclusion for g is used prematurely.

For step 3 I read SchwartzSpace/Basic.lean:555-567,1125-1133, FourierTransform.lean:175-248, LpSpace.lean:47-139, and TemperedDistribution.lean:169-177,506. The Schwartz node gives both facts the step takes: the complexification of the real compact smooth test is Schwartz, and it is integrable. The L1 transposition node requires integrability of both h and that test and gives the exact displayed bilinear, unconjugated identity, for the transposed phase. Here transpose preserves minus the inner product. The L2 test node states the second displayed identity for arbitrary measurable representatives and gives the inverse law needed to select u as that inverse class. Its Mathlib match follows by evaluating `fourierInv_toTemperedDistribution_eq` on the test and using the two evaluation formulas; this is a one-line specialization of a theorem, not a claim that distribution equality already means ae equality. I checked the source definitions of the L2 Fourier isometry and its inverse, which are the continuous extensions of the stated Schwartz conventions. Multiplication is commutative in C, so the two right-hand integrals coincide. This verifies all hypotheses and both signs without appealing to pointwise Fourier inversion or a missing comparison lemma.

For step 4 I read AEEqOfIntegralContDiff.lean:180-201. The uniqueness theorem is for finite-dimensional real domains, Banach-space values and REAL compact smooth tests, exactly as the new node states. Complex-valued f1,f2 are legitimate real Banach-space values. Steps 2 and 3 provide its local integrability and real-test equality hypotheses. Only after its ae conclusion do I infer that g is square integrable and has the specified class. Thus the cited theorem says precisely what this step uses.

I checked the edge cases r=0, h=0, arbitrary null-set changes of h or the chosen representative of u, arbitrary m>=1, and larger r. At r=0 the regularity leaf gives continuity and the rest of the argument is unchanged. Zero transforms give zero test integrals. Null-set changes preserve both moment integrals and every integral used in the proof. I checked the sign on the phase directly and kept bilinear testing throughout, so no conjugation is omitted. Each new helper remains valid with a degenerate or zero bilinear form and with zero tests; none relies on a nondegeneracy hypothesis that is missing from its statement.

The only elementary operations left inline are absolute convergence from equality of absolute values, complexification of a real test, recognizing the transposed phase, commuting complex factors and passing between ae equality and the L2 quotient. Every analytic theorem used is a cited node. All four proof steps are below 2000 characters, and their union of `uses` equals `proof_deps`. `citations.json` copies the complete cited statement for each of the seven pairs, so the quote cannot silently import a fact from a node's proof. The assembly creates no dependency on a descendant of this item.
