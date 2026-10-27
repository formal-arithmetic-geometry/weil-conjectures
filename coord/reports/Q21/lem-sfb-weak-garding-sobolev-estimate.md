# Worker report: lem-sfb-weak-garding-sobolev-estimate

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-weak-garding-sobolev-estimate.json: unchanged statement; four-step split of the weak estimate, including the distributional identity before any gain of regularity.
- dag/nodes/sec-six-functors-basics/def-sfb-symbol-pseudodifferential-operators.json: definition; no Mathlib match; statement only, unsplit. Defines integer-order matrix symbols, localized quantization, real distributional action, and smooth-kernel operators.
- dag/nodes/sec-six-functors-basics/lem-sfb-elliptic-distribution-parametrix.json: statement; no Mathlib match; unsplit. Gives a left inverse modulo a smooth kernel on all distributions, without a Sobolev conclusion.
- dag/nodes/sec-six-functors-basics/lem-sfb-symbol-operator-sobolev-boundedness.json: statement; no Mathlib match; unsplit. Gives Sobolev boundedness for arbitrary symbol operators, with no ellipticity assumption.

The sandbox also contains citations.json, searches.jsonl and the local write_split.py used to write the JSON. The delivery consists of the node files and this report, not a Lean module or a modified tool.

## Attachments

None. Searches of lean/WeilConjectures by the item id, the blueprint tag and the notions Garding, Gårding, parametrix, pseudodifferential, weak elliptic regularity and Sobolev found no exact declaration. The additional lean/Sheaf hits concern consumers of analytic lemmas, not a project proof of this item. No sorry declaration was treated as an attachment.

## WANTED

WANTED: Demailly, Complex Analytic and Differential Geometry, VI sections 1–2, especially (2.3), printed p.289, for lem-sfb-weak-garding-sobolev-estimate. Intended local path: literature/demailly-complex-analytic-differential-geometry.pdf. Read online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf ; the section was read from PDF pages 288–290 using a streamed in-memory pdftotext conversion. No document was downloaded into the repository or a substitute checkout.

WANTED: Demailly, L2 Hodge Theory and Vanishing Theorems, Part I, sections 3.A–3.B, printed pp.11–14, for all three new nodes and the proof. Intended local path: literature/demailly-hodge-ams.pdf. Read online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/hodge-ams.pdf ; PDF pages 23–26 were read by the same in-memory procedure. The text supplies symbol estimates (3.5), quantization (3.4), Theorem 3.6, the regular/smooth-kernel paragraph, the inverse construction following Definition 3.8 and the proof of Theorem 3.9. Because this source is absent locally, proof_origin.by is agent as required, with the online-read assembly identified explicitly.

These are analytic sources, not Stacks facts; no Stacks tag or SGA route is asserted for them.

## What needed repair or clarification

The original statement agrees with VI (2.3): its input is only L2, and finite-order Sobolev membership is a conclusion, not a hypothesis. No statement correction or dispute was needed. The source gives no proof at that location. Demailly's longer Hodge notes give the specific inverse-modulo-smoothing proof of the same weak estimate in 3.9. I supplied that argument instead of attempting to apply the smooth a priori estimate directly to an L2 input.

The definition node fixes the order class, the cutoff quantization convention and what the identity on distributions means. The boundedness node expressly identifies its Sobolev map with the distributional action, preventing an unjustified identification of two extensions. The parametrix node does not assert weak regularity or a norm estimate; the mapping node has no ellipticity assumption. They are independent inputs to the assembly, not clauses renamed from the item.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor lem-sfb-weak-garding-sobolev-estimate reports that a node created for it has blueprint.from.node = None. I retained that exact inherited ancestor and extended its via list, rather than inventing an imported ancestor. Its long inherited place records the analytic prerequisite descending from det-thm-sf-ctf-stability-direct-images proof (3). I read the current latest section and direct-images proof, including paragraph (3), and did not change the chapter or the unit route. Whole-blueprint searches for elliptic, Sobolev, pseudodifferential, parametrix, smooth kernel, symbol and symbol operator produced no statement matching these analytic inputs. The broad elliptic and symbol hits concern unrelated scheme/coefficient statements.

## Search evidence

Every new node has actual msearch.py results copied from searches.jsonl, including a semantic query, a second differently phrased semantic query, Loogle and grep. All services responded. The symbol definition queries found only Schwartz-map constructions, Fourier-transform operations and parser symbols. The parametrix queries found smooth approximation, inverse function theorems and Fourier inversion, not a variable-coefficient bundle parametrix. The mapping queries found Euclidean Bessel-potential membership and derivative operations, Schwartz-space maps and the Gagliardo–Nirenberg inequality.

I read the returned types and the source of Mathlib/Analysis/Distribution/Sobolev.lean, especially its definitions and stated main theorems, and Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean. Constant-coefficient Fourier multipliers on a vector space do not specialize in one line to variable-x symbol operators in bundle charts. The Gagliardo–Nirenberg results assume differentiability and do not prove this weak regularity conclusion. Neither candidate makes any of the three new nodes a Mathlib leaf. The item's searches were also rerun and appended while retaining its previous search records.

## Not duplicates

- lem-sfb-elliptic-distribution-parametrix vs lem-sfb-weak-garding-sobolev-estimate: the former supplies an operator identity modulo a smooth kernel, with no Sobolev assertion; the latter combines independent boundedness results to obtain regularity and a quantitative estimate.
- lem-sfb-symbol-operator-sobolev-boundedness vs lem-sfb-weak-garding-sobolev-estimate: the former has an arbitrary symbol operator as input and assumes input Sobolev membership; it does not infer regularity from an elliptic differential image.
- lem-sfb-elliptic-distribution-parametrix vs lem-sfb-elliptic-global-garding-estimate: the existing node is an a priori bound on already smooth sections, not an inverse identity on distributions.
- lem-sfb-symbol-operator-sobolev-boundedness vs lem-sfb-bundle-sobolev-rellich: the existing node describes realization, injectivity and compact inclusions; it gives no variable-symbol mapping theorem.
- lem-sfb-elliptic-distribution-parametrix vs lem-sfb-elliptic-adjoint-regularity: the existing statement concerns smooth right-hand sides only, and its proof already depends on this item, so it cannot supply an inverse here.
- def-sfb-symbol-pseudodifferential-operators vs lem-sfb-symbol-operator-sobolev-boundedness: the definition imposes symbol estimates and the operator representation, not a Sobolev norm estimate.

The DAG search was global, by exact proposed ids and by pseudodifferential, parametrix, symbol estimates, smooth integral kernel and oscillatory integral. I opened the nearby global Garding, adjoint regularity, bundle Sobolev/Rellich, compact-remainder and closed-range/decomposition statements to distinguish their scope. None states one of the new nodes. No equal-Stacks-tag pair exists, since these sources are analytic notes without Stacks tags.

## Review by Q21

I read Demailly VI (2.3) on printed p.289 against every hypothesis of the item: compact oriented boundaryless manifold, smooth volume and fibre metrics, smooth elliptic finite-order differential expression, an L2 distribution as input and an Hs right-hand side. The conclusion is the gain of d derivatives with an L2 remainder; the fixed chart norms alter the constant only. The statement remains unchanged. In Part I 3.A, printed pp.11–12, Demailly identifies integral Sobolev spaces with weak square-integrable derivatives and allows equivalent localized norms. In Part I 3.B, printed pp.12–14, I read the actual symbol bounds and inverse construction rather than citing the estimate again.

For the definition I compared (3.4)–(3.5) with the local matrix-symbol representation. The change from Demailly's Fourier convention exp(2 pi i x xi) to exp(i x xi) is the substitution of frequency by 2 pi times frequency and preserves the order estimates. On real inputs the real part of complex quantization is explicit; this supplies a real distribution operator and is not a new ellipticity assumption. Smooth real kernels and the empty local sum are admitted by definition, in every integer order. The definition has no proof or proof_deps and makes no hidden Sobolev boundedness claim.

For the parametrix node I checked the construction after 3.8: invert the principal symbol away from zero frequency, insert a low-frequency cutoff, and correct the negative-order composition error by asymptotic symbol summation, leaving a smooth kernel. This is a genuinely non-elementary prerequisite left as a statement-only node. It applies to equal-rank systems and to all distributions. For a real operator, complexify, take a complex left parametrix and then take its real part on real inputs: Re(A_C P u) = u + Re(R_C u). Thus a real parametrix and real smooth kernel give exactly the stated identity. No regularity conclusion is smuggled into this prerequisite.

For the mapping node I checked Theorem 3.6 together with 3.A and the paragraph allowing smooth-kernel remainders. Its input is an arbitrary operator of order r, its output index is t-r, and its hypotheses explicitly require both indices used here to be nonnegative. Compact cutoffs localize to finite Euclidean estimates. Real parts, finite sums and smooth-kernel remainders preserve the bounded map. Its last sentence fixes compatibility with the original distributional action, which the assembly needs. The new statement remains a lemma to be split later, with no proof sketch hidden in its statement.

Step 1 uses only the parametrix statement. The quoted sentence really gives existence of A, a smooth kernel and the identity for every distribution; it does not require the unknown H(s+d) membership. I verified equal rank by using C=B and verified the same differential expression and real cotangent ellipticity. In Fourier convention the top symbol is multiplied by i^d (or (2 pi i)^d); this nonzero scalar does not change invertibility.

Step 2 uses exactly the general mapping statement with r=-d and t=s. Its output index is s+d, both indices satisfy its hypotheses, and the original distributional f=Pv is its input. It gives the claimed constant independent of v, with no appeal to a proof inside that node.

Step 3 uses the definition's literal empty-sum smooth-kernel clause to place the same remainder in order -(s+d), then uses the same mapping statement at t=0. This supplies a bound from the actual L2 input, without assuming any positive regularity. It is marked non-elementary because the mapping theorem is the analytic input. The order-class inclusion itself is a direct instance of the definition, so it is not another new node.

Step 4 uses the existing bundle Sobolev/Rellich statement only for its explicit sentence that L2 embeds injectively in distributions. I opened that node and copied this sentence into citations.json. Its compactness assertion and its proof are not used. All its hypotheses hold for B and N, and s+d is at least one. The remaining argument is subtraction of weak derivatives, the triangle inequality and max(1,a_s,b_s), written out; that is why this final step is elementary. The distribution identity is established before either regularity application, avoiding a circular regularization argument.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 with the files open: objects and notions are introduced or have definition dependencies; new leaves contain statements only; every non-elementary input to the item is a cited node; every used clause appears verbatim in citations.json; no parent/citer is used as a prerequisite; no off-unit statement is used as a tool. No proof step is longer than 2000 characters, and the four-step assembly is under 3000 characters.

For small cases, on the circle the real derivative has d=1 and invertible nonzero-frequency symbol, while its constants form a kernel; the L2 remainder correctly controls that kernel. For 1 minus the Laplacian the parametrix has order -2, agreeing with the two-derivative gain. A smooth kernel is represented by the empty sum at every order, including the large negative order needed when s=0 or s increases. Zero sections, the zero-rank bundle and the empty manifold give the zero identity and admit a positive bound. Unequal ranks are permitted only in the general mapping lemma; the inverse lemma requires equal ranks. These cases revealed no statement error. No a priori H(s+d) assumption or smoothness of v was added.

## Unfinished work

No part of this stage-1 split is omitted. The three new nodes intentionally remain unsplit for subsequent stage-1 work. No Lean has been written or compiled. The required remote dry run and delivery are the remaining validation actions for this report.
