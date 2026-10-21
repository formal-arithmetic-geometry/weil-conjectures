## Worker report

Q70, 2026-10-21. Stage 1 only; no Lean was written, no compiler was run, no agent was started, and the shared repository was read only. All work is under the assigned sandbox.

Files written under `dag/nodes/sec-proper-base-change/`:

- `sk-thm-properbasechange.json`: statement unchanged, five-step assembly, 1741 characters of proof text.
- `lem-weil-pbc-derived-torsion-descent.json`: statement, unsplit, no Mathlib match. Abstract derived counit on the cohomological essential image, together with restriction to locally torsion complexes.
- `lem-weil-pbc-heart-test-bounded-below.json`: statement, unsplit, no Mathlib match. The finite Postnikov and degreewise tail argument for arbitrary lower-bound-preserving triangulated functors.
- `lem-weil-pbc-discrete-exchange-site-comparison.json`: statement, unsplit, no Mathlib match. Canonical comparison of etale and pro-etale exchange for arbitrary discrete commutative rings and qcqs vertical edges.

`citations.json` gives a verbatim statement quote for all 19 step citations. `searches.jsonl` is the actual msearch log. The node records use the exact query strings from that log; no imagined search is recorded. The grep against a nonexistent candidate directory `CategoryTheory/Triangulated/TStructure/Functor` was discarded as evidence and replaced by a search of the actual `CategoryTheory/Triangulated/TStructure` directory. All recorded successful queries were read, including their second phrasings.

Attachments: none. I searched the project by the blueprint tag, the notion and the proposed helper names. `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange` states the exact theorem with `sorry`. The sorry-free Etale proper-base-change declarations state the etale assertion, not the classical pro-etale assertion with its canonical ringed exchange and classical endpoints. The existing finite-filtration declarations concern finite filtered abelian objects. They are not attachments to this item or the new helpers.

WANTED: none. All sources used are available in the read clone.

The live node already includes today's Q03 repair: six short steps and the two helpers `lem-weil-pbc-exact-faithful-torsion` and `lem-weil-pbc-finite-postnikov-isomorphism`. I started from that current JSON rather than restoring its obsolete 10048-character proof. I preserved its statement, source, Lean record, review metadata and other maintainer fields. The additional helpers do not replace those two results by competing sheaf/finite-Postnikov results: the arguments below expressly reuse them. The third new helper extends a finite-coefficient transport statement; simply citing that existing statement for an arbitrary ring would be C4. The parent remains a short assembly instead of hiding the required work in prose.

Nothing mathematical was left unresolved at this level. The three new helpers are deliberately statement-only, with empty proof and proof_deps, for subsequent parallel stage-1 work. Their complete argument allocation is below, not embedded in their statement fields.

## Argument preservation and work allocation

The old nine-step proof is still visible in the Lean theorem's docstring. Reading it against the current six-step JSON gives the following allocation; no proof route is discarded.

| Original argument | Where the argument lives after this delivery |
| --- | --- |
| 1. Classical derived descent; 2. locally torsion descent | New derived-torsion-descent: generic derived counit on complexes whose cohomology lies in the sheaf essential image, followed by integer-kernel/filtered-colimit reflection. Reuses exact-faithful-torsion. Parent step 1 checks the site specialization hypotheses. |
| 3. Torsion sheaves | Existing lemma-weil-pbc-torsion-assembly, retaining the projective-line, prime-coefficient reduction and torsion-assembly route. Parent step 2 supplies it to the new heart test. |
| 4. Finite truncation induction | New heart-test-bounded-below, using existing finite-postnikov-isomorphism with the zero base case and every integer shift. |
| 5. Fixed-degree truncation comparison | New heart-test-bounded-below: the mapped tail triangle and its two adjacent vanishing groups, then the naturality square and cohomology detection. This is a generic tail proof, not an infinite Postnikov-limit claim. |
| 6. Forgetting coefficients | Existing exchange-forget-coefficients, unchanged. Parent step 3 uses all three comparison clauses and conservativity. |
| 7. Proper gives qcqs | Parent step 4, using proper-base-change and the actual finite-type/separated definitions and lemma-pc-separated-quasi-separated. |
| 8. Three canonical mate squares | New discrete-exchange-site-comparison. Its statement fixes the two vertex maps and the actual exchange equality, for arbitrary rings. The argument below retains all three factors. |
| 9. Naturality and the two classical endpoints | The endpoint comparisons are part of discrete-exchange-site-comparison. Parent step 5 explicitly conjugates along the counit and retains the inverse by fullness. |

These work units are strictly smaller than the theorem: the descent helper has no scheme square, properness or exchange; the heart test has no sites, coefficients, properness or torsion assumption; the site-comparison helper assumes neither properness nor torsion and asserts equality of specified maps without assuming either exchange invertible. In particular none states one of the item's proper-base-change conclusions as an unexplained new lemma.

The derived descent helper is not the two-line application of the existing sheaf torsion lemma: it proves the additional assertion that *cohomological* membership in a sheaf essential image implies invertibility of the *derived* counit for any ringed sites satisfying the unit hypothesis. That is a finite-truncation plus tail argument. The old pro-etale derived equivalence states only its particular site case. The heart test adds passage to an unbounded-above input to the existing finite-Postnikov lemma. The site comparison fixes actual mate normalization and composition coherence, beyond the existence of endpoint isomorphisms.

## Arguments for the new statement-only work units

### Derived torsion descent

Sources read: the current blueprint's opening paragraph; its classical-derived-equivalence detail in `sec-proetale-coefficients/sk-cor-pe-classical-derived/`; Stacks `derived.tex`, Tag 08J5, label `remark-truncation-distinguished-triangle`; `sites-modules.tex`, Tags 03DA (`lemma-abelian`) and 03DB (`lemma-limits-colimits`); and `categories.tex`, Tag 0038 (`lemma-adjoint-exact`). The generic statement is an agent-supplied formulation of that descent argument, not a claim that Stacks states the whole helper under one tag.

Use the canonical derived adjunction stipulated in the statement. The right adjoint B is additive and left exact, and RB preserves every lower cohomological bound by `lem-weil-pbc-derived-functor-negative-vanishing`; alternatively the abstract exact-derived-adjunction-bounds lemma gives that bound preservation. A_D preserves cohomology by `lem-weil-pbc-exact-functor-bounded-below`. Their composite is therefore triangulated and preserves lower bounds. The derived counit v is a shift-compatible transformation from A_D RB to the identity; this is the canonical derived adjunction transformation, not an arbitrarily chosen identification of functors.

For a module F, the derived unit at F[0] is invertible by hypothesis. The adjunction triangle identity says that v at A_D(F[0]) composed with A_D of this unit is the identity. Therefore v at A_D(F[0]) is the inverse of that invertible map. Exactness identifies A_D(F[0]) with (AF)[0]. For each cohomology object H^q(K) of an object K in E, choose its stipulated isomorphism to AF_q only to transport this assertion; the actual derived antecedent is the construction RBK. Thus v is invertible on every H^q(K)[0]. Apply the new heart test, or its finite-Postnikov and fixed-degree tail proof below, to v. This proves invertibility of v_K. The same argument shows the essential image of A_D is exactly E; the forward inclusion uses H^q(A_DL)=A H^q(L), and the backward inclusion is supplied by v_K. Invertibility of the unit gives full faithfulness of A_D, hence the stated derived equivalence.

For local torsion use the existing `lem-weil-pbc-exact-faithful-torsion`, not a new uniform-annihilator lemma. Its sheaf argument is retained here to make the work allocation complete: exact additivity gives A(F[n])=ker(n id_AF), and kernel uniqueness identifies the transition maps for n dividing m. Since A is a left adjoint, it preserves the colimit over the small filtered positive-divisibility poset. Thus it takes c_F to c_AF under those identifications. Full faithfulness reflects invertibility, so c_F is invertible iff c_AF is. Stacks 03DA and 03DB justify computing these kernels and colimits after forgetting modules. Apply this to every H^q(L) and use the exact-functor cohomology identification. For K in E the counit then gives torsion of H^q(RBK) from torsion of H^q(K). Units and counits restrict to the full torsion subcategories, proving the final equivalence. No arbitrary chosen object from a mere existence assertion defines RBK.

Small cases: A=id and B=id reduce to the identity equivalence; K=0 and zero ring sheaves cause no exception. A constant Q/Z on a point has no uniform annihilator but c_F is invertible, so it tests the local rather than uniformly killed formulation. A non-torsion constant Z has c_F=0 to Z and is correctly excluded from the torsion subcategory. Shifting K to any negative degree preserves the argument. The unit hypothesis is required; underived full faithfulness by itself has not been silently promoted to a derived-unit theorem.

### Bounded-below heart test

Sources read: the blueprint's entire bounded-below paragraph; Stacks 08J5's truncation triangles and 05TC (`lemma-negative-vanishing`), including the proof using a tail triangle; existing finite-postnikov-isomorphism, truncation-triangle, truncation-cohomology and derived-plus-iso-on-cohomology statements. The statement generalizes the source's same-bound argument to arbitrary triangulated Phi,Psi preserving lower bounds.

Choose a lower bound a of E. For m at least a-1, apply the existing finite-Postnikov helper with b=m. Its base b=a-1 is a zero object. In the induction from j-1 to j use the distinguished triangle tau_<=j-1 E to tau_<=j E to H^j(E)[-j] to (tau_<=j-1 E)[1]. Shift compatibility gives invertibility at the third object from the assumption at H^j(E)[0]; this includes negative j. Naturality and shift compatibility make the three components a morphism of distinguished triangles; triangle two-out-of-three makes the middle component invertible. When m is smaller than a-1, the truncation has every cohomology object zero by the actual truncation-cohomology formula, so cohomology detection identifies it with zero. Both triangulated functors preserve zero, completing this case.

For any m use the *other* canonical triangle tau_<=m E to E to tau_>=m+1 E to (tau_<=m E)[1]. The tail has cohomology zero below m+1. The lower-bound hypothesis puts both images of the tail in that same range. In each mapped triangle, the exact sequence H^(m-1)(image of tail) to H^m(image of truncation) to H^m(image of E) to H^m(image of tail) has zero outer groups. This proves both specified maps H^m(Phi c_m), H^m(Psi c_m) are isomorphisms. It is stronger than just knowing their sources and targets happen to be isomorphic. Naturality gives H^m(Psi c_m) H^m(eta_truncation)=H^m(eta_E) H^m(Phi c_m), yielding the displayed formula. Each factor is invertible, hence H^m(eta_E) is invertible for all m. The cohomology-detection theorem in the derived category proves eta_E is invertible. This is the precise finite plus degreewise argument; it never interchanges Phi or Psi with an infinite limit.

Small cases: an empty cohomological interval m=a-1; m<a-1; a single nonzero degree; E=0; a negative lower bound; Phi=Psi=id. An unbounded-above E has a different finite argument for each m and therefore imposes no missing boundedness or convergence assumption. The source's right-derived comparison and the existing sbc truncation criterion are useful special tools, but neither states this generic transformation test.

### Discrete exchange site comparison

Sources read: the current blueprint's full pro-etale paragraph, `sk-thm-pe-direct-image-comparison/_section.md`; Stacks `sites-cohomology.tex`, Tag 07A7, label `remark-base-change`; the statements of `lem-pe-direct-image-mate-compatibility`, `lem-weil-pbc-three-step-adjunction-comparison`, `lem-weil-pbc-exchange-mate-cube`, and `lem-weil-pbc-transport-identifies-exchange`. Mathlib `CategoryTheory/Adjunction/Mates.lean`, lines 123-158, gives the generic mate unit/counit equations, not this site comparison theorem.

Use the inverse comparison of the blueprint comparison theorem in the orientation a_u:A_U l_u to p_u A_V. Its canonical beta_u is b_u: A_V r_u to s_u A_U. The arbitrary-discrete-ring statement of `lem-pe-direct-image-mate-compatibility` supplies exactly these two identities (write its c as a_u inverse):

v^p_(A_U M) p_u(b_(u,M)) a_(u,r_u M) = A_U(v^e_M),

b_(u,l_u N) A_V(u^e_N) = s_u(a_(u,N)^(-1)) u^p_(A_V N).

Here u^e,u^p are units and v^e,v^p counits. The comparison theorem makes b_f and b_f' invertible using precisely the assumed qcqs hypotheses; g,g' need no such hypotheses because only inverse-image comparisons are used on them. Composition compatibility of a for the equality f g'=g f' makes the inverse-image cube commute. The coefficient identifications are the canonical ones on constant sheaves; both composite coefficient maps are induced by the same constant sections, so this is the ambient ringed composition comparison rather than an arbitrary square isomorphism.

Expand each canonical exchange as three arrows. In the etale row the vertices are l_g r_f L, r_f' l_f' l_g r_f L, r_f' l_g' l_f r_f L, and r_f' l_g' L. In the pro-etale row the vertices are p_g s_f A_X L, s_f' p_f' p_g s_f A_X L, s_f' p_g' p_f s_f A_X L, and s_f' p_g' A_X L. Apply A_Y' to the etale row. The first and last vertex comparisons are precisely S_L and T_L in the new statement. The two middle comparisons are formed by inserting b_f', a_f', a_g, b_f, respectively b_f', a_g', a_f, b_f. The unit identity above commutes the first square; the inverse-image cube and naturality commute the square-transport square; the counit identity above commutes the third square. This is the hypothesis and conclusion of the existing three-step-adjunction-comparison lemma, with no assumed invertibility of the exchanges. Composing the three equations cancels the two middle vertex maps and gives exactly T_L A_Y'(e_L)=e^p_(A_X L) S_L. The chosen orientation is important: the pro-etale exchange is T_L A(e_L) S_L inverse, not the inverse equation.

Naturality of a,b gives naturality of S,T. Their etale sources l_g r_f L and r_f' l_g' L are bounded below (right derived direct image and exact inverse image preserve lower bounds). Applying A_Y' keeps them bounded below by exact cohomology comparison and makes their cohomology sheaves classical by the sheaf equivalence; equivalently use the existing classical derived equivalence. S,T therefore put the two stated endpoints in the bounded-below classical subcategory. This conclusion uses no proper-base-change isomorphism and is valid even when e_L is not invertible.

Small cases: identity squares give the unit/counit identities with the comparisons, empty schemes give zero categories, L=0 and Lambda=0 are harmless. Lambda=Z or Q/Z-containing coefficient modules show why no finite-coefficient node suffices; a module sheaf of arbitrary rank is permitted. Nonproper qcqs vertical arrows still meet the helper's assumptions; the helper does not assert their base-change exchanges are invertible. No restrictions on g,g' have been imported from a direct-image comparison theorem.

## Review by Q70

I read the main-20261015 theorem and proof, both its chapter and unit records, the live Q03 node and its two helpers, the actual Lean module, every statement cited by the five parent steps, and the sources listed above for each new helper. The parent's statement is byte-for-byte unchanged against the copied live JSON and agrees with the current blueprint: arbitrary commutative Lambda, proper f, arbitrary g, bounded below and classical K, local torsion of every underlying abelian cohomology sheaf, the specified uncompleted exchange, and both endpoints in the classical full subcategory. There is no invertibility-of-orders, constructibility, Noetherianity or finite-coefficient restriction.

Step 1 uses derived-torsion-descent for the derived counit and torsion assertion. I checked its assumptions against det-pe-classical-sheaves-modules (the exact fully faithful underived adjoint pair), sk-prop-sf-comparison (the *derived* unit at every D+ object), and sk-def-pe-classical-definition together with the sheaf equivalence (each cohomology belongs to the sheaf image). These are statements, not results taken only from their proofs. Derived right direct image is the actual one used in the comparison adjunction. The abstract helper constructs L as RBK, so no existence-only choice produces the data.

Step 2 uses derived-inverse-image for the triangulated pullbacks, exact-functor-bounded-below for their cohomology and lower bounds, negative-vanishing for both right direct images, derived-direct-image-triangulated for distinguished triangles, and derived-exchange-triangulated for the fourth square and integer shift comparisons. I read each statement: negative-vanishing requires Grothendieck abelian categories and left exact additive direct image, which the sheaf setting supplies; it is not a bound for arbitrary functors. Torsion-assembly supplies exactly the specified *abelian* exchange on a torsion sheaf, for the proper f and arbitrary g here. The heart-test hypothesis is checked on each H^q(E), so local torsion rather than a global annihilator suffices.

Step 3 cites exchange-forget-coefficients, whose statement explicitly provides the cohomology identification, inverse-image comparison, derived direct-image comparison for both vertical edges, and equality of the canonical mates, followed by reflection of invertibility. This avoids treating exact forgetting alone as a theorem about derived pushforward.

Step 4 checks the new comparison helper's geometric hypotheses before using it. Proper-base-change gives proper f'; proper-morphism supplies finite type and separatedness; finite-type-morphism includes quasi-compactness; separated-quasi-separated supplies the other half. I checked the new helper's *displayed equality* against the formula used here, including S inverse on the right. Applying a functor to an isomorphism and composing with the two stated vertex isomorphisms is elementary after these citations. Both endpoint clauses are explicitly in the new statement.

Step 5 is marked elementary because it is the naturality square of the ambient-exchange *transformation*, followed by composition of isomorphisms and fullness: if F,G are the endpoint functors, the actual square is G(alpha) e_(A L)=e_K F(alpha). Hence e_K=G(alpha) e_(A L) F(alpha)^(-1), with both outer arrows invertible. Classicality is invariant under an isomorphism since cohomology carries it to module-sheaf isomorphisms and the definition's continuity maps are natural. Bounded-below membership is likewise invariant under cohomology isomorphism. The inverse lies in the full subcategory by the definition of full. There is no hidden proper or derived comparison lemma in this last step.

I checked B1-B9 for all three new files: complete objects and hypotheses; real sheaf/derived functors and canonical maps; no proof sketch in the statements; proof and proof_deps empty; source labels and tags as read; one TeX escaping layer (the raw JSON's doubled backslashes encode single mathematical slashes); all notions either inline or cited by their actual definitions; successful logged semantic, Loogle and source searches with second phrasings; blueprint.from.node=sk-thm-properbasechange, via empty, exact paragraph locations and same_as empty. In particular I corrected the new site helper's initial citation of def-weil-pbc-proetale-modules: that node assumes a *finite* ring. It now uses the arbitrary-ring module-category, constant-sheaf and general ringed-operations definitions instead. I also replaced the broad scheme-conventions collector by the two actual qcqs definition nodes. No target or existing helper was changed.

For C1-C4 every non-elementary parent fact has the node citation that states it; citations.json was produced from the opened statement fields. For C5 and B9 I searched the entire DAG, not just the current unit, by the helper notions and source tags, and used blueprint_refs searches for torsion descent/equivalence, derived unit/cohomological image, bounded below, Postnikov, natural transformation, exchange comparison and exchange; the closest candidates are distinguished below. C6 is checked by the server DAG check. C7-C8: the geometric route is still torsion-assembly below the projective-line/reduction units; the generic negative-vanishing tool is declared in split_report.tool_uses. Existing tool approvals were not edited. No SGA source was used.

For D1-D5, the generic setting and hypotheses of each new node differ substantially from the proper-base-change assertion, and the preserved work is itemized above. None is the whole theorem or an unexplained clause of it. The finite-induction base and successor, the fixed-degree tail, and all three mate squares are written out in the report. I checked E1-E7 using the small cases listed under each helper, particularly the absence of a uniform torsion bound, negative truncation degrees, arbitrary g/g', and the arbitrary-ring coefficient distinction. I found no statement dispute in the item; the coefficient-definition mismatch was in my initial dependency selection and was repaired before delivery. There are no parent steps longer than 2000 characters.

## Validation

The preliminary server `check_dag` exited successfully: `check_dag OK: no finding introduced by the sandbox or on its nodes`. Its route advisories concern the global baseline. The required packaged dry run exited 0 and printed `OK (not pushed) deliver/Q70/sk-thm-properbasechange at 1cb86e02868: preflight passed`. This includes the maintainer preflight, check_dag and review_split on the server. All three new nodes have empty proof/proof_deps; all 19 step citations have verbatim certificates; the parent statement is unchanged and its proof is 1741 characters. The final push command reruns preflight on its packaged commit.

## Not duplicates

The following pairwise checks cover every existing unmerged node with one of the source Stacks tags. Shared source tags alone do not identify statements. The especially close cases are discussed first.

lem-weil-pbc-derived-torsion-descent vs det-pe-classical-derived-equivalence: the latter is the etale/pro-etale site equivalence; the new node proves the cohomological essential-image criterion for arbitrary ringed sites under a derived-unit hypothesis and its restriction to locally torsion cohomology.
lem-weil-pbc-derived-torsion-descent vs lem-pe-classical-derived-counit: that Lean statement is the pro-etale specialization and has no abstract ringed-site or torsion-subcategory assertion.
lem-weil-pbc-derived-torsion-descent vs lem-pur-exact-derived-adjunction-bounds: the old counit clause assumes the input is already isomorphic to FD(X); the new input only has cohomology sheaves in the *underived* essential image and constructs the antecedent RBK.
lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-exact-faithful-torsion: the old node compares torsion of a single module sheaf with its exact image; it has no derived adjunction, counit or characterization of the cohomological essential image. It is reused for the final part.
lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-finite-postnikov-isomorphism: the old node controls a finite upper truncation; the new node treats the original bounded-below, possibly unbounded-above complex and specifies the degreewise naturality equation using preserved lower bounds.
lem-weil-pbc-heart-test-bounded-below vs sbc-lem-bounded-below-truncation-criterion: the old statement is about particular derived direct-image composites on scheme sites and allowable torsion; the new node concerns arbitrary triangulated transformations preserving lower bounds and includes propagation from cohomology objects.
lem-weil-pbc-heart-test-bounded-below vs lem-sf-generating-class-determination: the old node controls a thick envelope, closed under finite operations; a bounded-below object need not belong to the thick envelope of its infinitely many cohomology objects. The new tail argument supplies precisely the missing degreewise passage.
lem-weil-pbc-heart-test-bounded-below vs lem-pur-bounded-heart-amplitude: that result bounds the amplitude of one functor on bounded complexes, not isomorphy of a transformation on objects unbounded above.
lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-transport-identifies-exchange: the old node assumes Lambda finite, whereas the item and new helper permit every discrete commutative ring, with no scalar reduction available for a general ring.
lem-weil-pbc-discrete-exchange-site-comparison vs sk-thm-pe-direct-image-comparison: the old node gives single-edge inverse/direct-image comparisons and coherence; the new node states the resulting four-corner canonical exchange equality with specified S and T.
lem-weil-pbc-discrete-exchange-site-comparison vs lem-pe-direct-image-mate-compatibility: the old node gives unit and counit equations for a single edge with arbitrary coefficients; the new node assembles both vertical edges, both inverse-image edges and the square composition comparison.
lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-three-step-adjunction-comparison: the old node is a generic categorical result under supplied cube and adjunction identities, not their verification for the canonical scheme-site comparison maps or the classical endpoint assertion.

lem-weil-pbc-derived-torsion-descent vs lem-pe-left-module-comparison-vanishing-criterion: Existing statement concerns Objectwise derived evaluation detects comparison direct-image vanishing; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs prop-weil-pbc-integral-tstructure: Existing statement concerns The standard t-structure on the integral category; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs prop-weil-pbc-levelwise-truncations: Existing statement concerns Levelwise truncations of the adic tower; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs thm-weil-pbc-integral-truncations: Existing statement concerns Truncations of the integral category; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-envelope-tstructure: Existing statement concerns The envelope inherits the t-structure; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-weil-t-structure: Existing statement concerns t-structure; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-sbc-derived-scalar-truncation-continuity: Existing statement concerns Lower bounds for derived scalar extension from finite upper truncations; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs prop-weil-localized-tstructure: Existing statement concerns The rational t-structure; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-sbc-standard-tstructure-derived-category: Existing statement concerns The standard t-structure on the derived category of an abelian category; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-coef-module-flat-cotorsion-foundation: Existing statement concerns The module-level flat cotorsion pair on a small ringed site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-module-filtered-colimits-tensor-preserves: Existing statement concerns Preservation of filtered colimits by tensor totalization; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-module-filtered-colimits-tensor: Existing statement concerns Filtered colimits and tensor complexes of sheaves of modules; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-derived-lower-truncation-step-ses: Existing statement concerns Successive lower truncations have a two-term kernel quasi-isomorphic to one cohomology object; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-lower-truncation-transition-kernel: Existing statement concerns Kernel geometry and homology of a fixed successive lower truncation transition; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-natural-bounded-below-truncation-couples: Existing statement concerns Individual bounded-below truncation couples with natural comparisons; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pc-raw-truncation-couple-naturality: Existing statement concerns Naturality of raw truncation maps for one derived morphism; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-sfb-directed-ring-sheaf-module-colimit: Existing statement concerns Directed colimits of ring sheaves compute the underlying module colimit on a site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-diagram-site-module-equivalence: Existing statement concerns Product-site module sheaves are diagram modules; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: Existing statement concerns Actual coefficient limits, finite powers, and compatible finite-projective complex retracts; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-truncation-step-ses: Existing statement concerns The step tau_{<=q-1}K -> tau_{<=q}K of canonical truncations: short exact sequence and quasi-isomorphism of the cokernel to H^q(K)[-q]; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-weil-pbc-derived-normalization-arrows: Existing statement concerns Canonical derived coefficient normalization arrows; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-inverse-image-preserves-colimits: Existing statement concerns Inverse image of etale abelian sheaves commutes with colimits; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-module-sheaves-colimits-forgetful: Existing statement concerns Colimits of sheaves of modules and the forgetful functor to abelian sheaves; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-truncation-descends: Existing statement concerns Canonical truncations and H^q(-)[-q] descend to functors on D(A), with i_q, j_q natural; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-constant-module-sheaves-forget-colimits: Existing statement concerns Constant-module sheaves forget coefficients preserving colimits; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-sets-inverse-image-colimits-finite-products: Existing statement concerns Inverse image of sheaves of sets preserves colimits and finite products; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-left-adjoint-preserves-colimits: Existing statement concerns Left adjoints preserve colimits; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-proetale-ringed-filtered-colimits: Existing statement concerns Transfer closed filtered-colimit preservation to arbitrary module coefficients; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-upper-step-quotient-coordinates: Existing statement concerns Degreewise coordinates of the cokernel of successive upper truncations; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-constant-module-section-coefficients: Existing statement concerns The canonical coefficient equivalence intertwines constant-module transitions; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-closed-immersion-pushforward-cokernel: Existing statement concerns Closed pushforward preserves module cokernels; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-two-term-coimage-quasiiso: Existing statement concerns The cohomology projection of an arbitrary two-term coimage complex is a quasi-isomorphism; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-module-sheaves-enough-injectives: Existing statement concerns Sheaves of modules on the small etale site have enough injectives; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-adjunct-counit-identity: Existing statement concerns The adjunct of a morphism, composed with the counit, gives back the morphism; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-graded-realization-local-generators-epi: Existing statement concerns Local homogeneous generators give an explicit algebra-module epimorphism; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits: Existing statement concerns Exact colimit-preserving evaluation at an affine weakly contractible object; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-constant-module-pullback-section-comparison: Existing statement concerns Constant-module direct-image sections and abelian pullback global sections; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-module-sheaves-grothendieck-abelian: Existing statement concerns Sheaves of Lambda-modules on the small etale site form a Grothendieck abelian category; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-finite-postnikov-isomorphism: Existing statement concerns Finite Postnikov propagation of invertibility; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-module-sheaves-limits-sectionwise: Existing statement concerns Limits of sheaves of modules exist and are computed sectionwise; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-truncation-triangle: Existing statement concerns The truncation triangle tau_{<=q-1}K -> tau_{<=q}K -> H^q(K)[-q] is distinguished; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-restricted-cohomology-colimit: Existing statement concerns Canonical colimit cocone of restricted abelian cohomology; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-constant-module-transition-coefficients: Existing statement concerns Forgetting scalars commutes with the constant-sheaf adjoint transition; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-proetale-weakly-contractible-evaluation-exact: Existing statement concerns Exact module-sheaf evaluation at a weakly contractible pro-etale object; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-presheaf-modules-colimits-sectionwise: Existing statement concerns Colimits of presheaves of modules are computed sectionwise; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-weil-pbc-right-adjoint-preserves-limits: Existing statement concerns A right adjoint preserves limits; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-coefficient-level-ordinary-images: Existing statement concerns Ordinary geometric images at the constant quotient levels; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-ringed-site-grothendieck-coefficient-universe: Existing statement concerns Grothendieck module categories at the coefficient universe; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-derived-evaluation: Existing statement concerns Cohomology and joint detection by system evaluations; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-evaluation-kflat: Existing statement concerns Simultaneous componentwise K-flat representatives; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-tensor-coherence: Existing statement concerns Canonical tensor coherence for a scalar assignment; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-module-sheaf-coproduct-local-support: Existing statement concerns Coproduct module sheaves as locally finite-coordinate tuples; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-ringed-site-grothendieck-abelian: Existing statement concerns Sheaves of modules on a small ringed site are Grothendieck abelian; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-tate-inverse-limit-base-change: Existing statement concerns Base change of an ell-adic inverse-limit tower and of its finite reduction tensor; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-pur-cochain-coefficient-arrows: Existing statement concerns Canonical scalar-association and transition arrows on cochain sheaves; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-cbc-single-proper-open-finite-normalization: Existing statement concerns Finite etale normalization of the single-level intrinsic mate; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-sheaf-ring-coefficient-ordinary-adjunction: Existing statement concerns Exact restriction and normalized ordinary scalar-extension adjunction on a general ringed site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-sf-ring-sheaf-closed-localization: Existing statement concerns Closed localization for arbitrary pro-etale ring-sheaf module objects; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-pur-system-level-left-extension-basic: Existing statement concerns Strict systems and the unchanged left-extension interface; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-pur-cochain-tensor-coherence-data: Existing statement concerns Canonical cochain ringed-pullback and coherence data; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-scalar-generators: Existing statement concerns Unit tensor generators for scalar extension; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-exact-derived-coproducts: Existing statement concerns Coproduct preservation by exact derived functors; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-scalar-coherence: Existing statement concerns Canonical scalar tensor unit and associators; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-ordinary-single-extension: Existing statement concerns Ordinary singleton left extension; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-pur-cochain-coefficient-universe-transport: Existing statement concerns Canonical common-universe transport of ring and module sheaves; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-sf-derived-concentrated-single: Existing statement concerns A complex with cohomology in a single degree is that cohomology object shifted; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-ordinary-selected-extension: Existing statement concerns Ordinary subsequence left extension with actual transitions; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-coproducts: Existing statement concerns Coproducts and derived evaluation for strict systems; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-scalar-model: Existing statement concerns Normalized scalar models for arbitrary sheaf-ring maps; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-evaluation-topos: Existing statement concerns Evaluation as inverse image on the ringed sequence site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-bounded-heart-amplitude: Existing statement concerns Finite cohomological amplitude from bounds on cohomology objects; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-pur-sheaf-inverse-limit: Existing statement concerns Inverse limit of a sequence of sheaves of modules on a site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-module-sheaf-coproduct-local-generation: Existing statement concerns Local finite-sum normal form in a coproduct of module sheaves; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-grothendieck: Existing statement concerns Grothendieck abelian strict-system categories; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-pur-system-ringed-sequence-site: Existing statement concerns Strict systems as modules on one ringed sequence site; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs def-weil-sheaf-of-modules-category: Existing statement concerns Category of sheaves of modules over a sheaf of rings; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-sf-derived-truncation-triangle: Existing statement concerns Canonical truncation triangle in the derived category; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-derived-torsion-descent vs lem-galois-equivalence-preserves-limits: Existing statement concerns An equivalence of categories preserves limits and colimits; it does not characterize the cohomological essential image of an arbitrary exact fully faithful ringed-site embedding with a derived-unit hypothesis, together with its derived torsion equivalence.

lem-weil-pbc-discrete-exchange-site-comparison vs def-sbc-derived-localization-comparison-data: Existing statement concerns Canonical derived étale-localization comparisons; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sbc-restrict-scalars-pullback-square-comparison: Existing statement concerns Canonical coefficient comparisons preserve inverse-image square transport; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sbc-base-change-restrict-scalars-arrow: Existing statement concerns Étale base-change arrows commute with restriction of coefficients; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sbc-restrict-scalars-derived-adjunction-identities: Existing statement concerns Canonical coefficient comparisons preserve the derived adjunction; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sbc-restrict-scalars-derived-exchange: Existing statement concerns Canonical coefficient comparisons commute with derived exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sbc-base-change-restrict-scalars-comparison: Existing statement concerns Coefficient comparison isomorphisms for the base-change source and target; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-coef-semilinear-proper-open-mate: Existing statement concerns Canonical semilinear proper/open adjunction mate; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-coef-cartesian-section-adjoint-mates: Existing statement concerns Adjoint mates on cartesian derived sections; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-sf-semilinear-proper-open-comparisons: Existing statement concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-trf-bounded-below-derived-mate-model: Existing statement concerns Bounded-below derived mates are computed by underived mates and comparison units; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-trf-topos-derived-base-change-map: Existing statement concerns Derived base-change map for a commutative square of ringed topoi; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-pc-derived-base-change-map: Existing statement concerns Canonical derived base-change morphism; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-sfb-proetale-projection-exchange-maps: Existing statement concerns Canonical projection and exchange maps on internal pro-etale modules; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sfb-ringed-kunneth-factorizations: Existing statement concerns Two factorizations of the ringed-topos external product comparison; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sfb-etale-proetale-scalar-counit-transposes: Existing statement concerns Common counit transpose of the two site/scalar direct-image composites; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-a1-lisse-section-evaluation: Existing statement concerns Canonical evaluation of ordinary common-stage sections at a geometric point; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-a1-proper-sections-germ-and-moving-point: Existing statement concerns Canonical proper compact rational germs and semilinear moving points; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-weil-pbc-adjunction-mate: Existing statement concerns Mate of a transformation under two adjunctions; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: Existing statement concerns Slice pullback comparison is induced by the ringed localization square; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-exchange-mate-cube: Existing statement concerns Naturality of the adjunction mate across a cube; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-derived-exchange-module-termwise: Existing statement concerns K-injective representative of the module derived exchange mate; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-strict-tower-exchange-mate-normalization: Existing statement concerns Strict tower exchange agrees with the canonical mate; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-weil-pbc-four-arrows: Existing statement concerns Four finite-level arrows; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs prop-weil-pbc-derived-inverse-image-adjunction: Existing statement concerns Derived adjunction of inverse and direct image on D^+; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-module-abelian-underived-exchange: Existing statement concerns Coefficient forgetting respects underived exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-finite-level-rectangle: Existing statement concerns Finite-level exchange rectangle; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-module-abelian-stalk-exchange: Existing statement concerns Forgetting module coefficients in the stalk of derived exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-exchange-forget-coefficients: Existing statement concerns The derived exchange morphism commutes with forgetting the coefficient ring; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-weil-pbc-derived-square-iso: Existing statement concerns Square isomorphism on bounded below derived categories; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-derived-exchange-unbounded-transport: Existing statement concerns Transport of the exchange equation to arbitrary K-injective representatives; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-frobenius-exchange-restriction: Existing statement concerns Finite-level exchange is the restricted ambient exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: Existing statement concerns Canonical coefficient comparisons intertwine derived exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-etale-underived-exchange-restriction: Existing statement concerns Underived exchange along an etale morphism is the restriction identification; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-derived-exchange-bounded-comparison: Existing statement concerns The bounded below exchange comparison equation; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-weil-pbc-strict-tower-operations: Existing statement concerns Specified derived operations and mate on strict pro-etale module towers; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: Existing statement concerns Finite exchange rectangle for intrinsic coefficient reduction; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-pur-ringed-coefficient-projection-cocycle: Existing statement concerns Coefficient projection cocycle for ordinary derived ringed diagrams; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-pur-scalar-pullback-representative-data: Existing statement concerns Canonical scalar/pullback representative data; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-cbc-strict-tower-pullback-square-pasting: Existing statement concerns Pasting of normalized strict-tower inverse-image squares; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-kun-commutative-exchange-evaluation-compatibility: Existing statement concerns Raw class evaluation commutes with geometric chart pullback; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-kun-commutative-exchange-raw-pullback: Existing statement concerns Canonical transport of represented raw classes through a commutative square; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-cbc-strict-tower-direct-image-coherence: Existing statement concerns Coherence of canonical strict-tower direct image and its square mates; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-pur-ringed-coefficient-projection-data: Existing statement concerns Normalized coefficient projection interfaces; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-cbc-strict-tower-gamma-single-evaluation: Existing statement concerns Evaluation of the intrinsic proper mate; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-pur-etale-scalar-pullback-existence: Existing statement concerns Existence of normalized derived scalar/pullback comparison; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-cbc-finite-constant-coefficient-transport: Existing statement concerns Normalized finite scalar and etale-origin transport to constant coefficient modules; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-pur-etale-scalar-pullback-iso: Existing statement concerns Canonical derived scalar and pullback isomorphism; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-kun-derived-exchange-cube: Existing statement concerns Derived exchange commutes around a commutative cube; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-pur-scalar-tensor-pullback-normalization: Existing statement concerns Scalar/tensor pullback normalization on a K-flat representative; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-kun-commutative-derived-exchange: Existing statement concerns Derived exchange for an arbitrary commutative square of schemes; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-sp-proper-open-comparison-normalization: Existing statement concerns Structural normalization of explicit proper/open comparison; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-kun-commutative-exchange-class-compatibility: Existing statement concerns The exchange mate transports higher-image raw classes; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-pur-etale-scalar-pullback-uniqueness: Existing statement concerns Uniqueness of normalized derived scalar/pullback comparison; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-cbc-strict-tower-open-extension: Existing statement concerns Normalized exact open extension on strict constant-coefficient towers; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-cbc-strict-tower-proper-open-calculus: Existing statement concerns Normalized proper/open calculus on strict pro-etale towers; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-exc-support-scalar-projection-normalization: Existing statement concerns Normalization of support scalar mate as a projection arrow; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-kun-unbounded-abelian-exchange-comparison: Existing statement concerns Unbounded coefficient forgetting identifies canonical etale exchange; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-cbc-strict-constant-tower-operations: Existing statement concerns Strict constant-coefficient towers and normalized inverse/direct-image operations; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs def-cbc-strict-tower-proper-open-arrows: Existing statement concerns Unit-normalized proper and open arrows on strict towers; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-discrete-exchange-site-comparison vs lem-pod-frobenius-exchange-degree-zero: Existing statement concerns Degree-zero Frobenius exchange is the underived section-pullback mate; it does not give the canonical etale-to-pro-etale four-corner exchange equation with its qcqs direct-image comparisons for every discrete commutative ring and the classical endpoint assertion.

lem-weil-pbc-heart-test-bounded-below vs prop-weil-pbc-integral-tstructure: Existing statement concerns The standard t-structure on the integral category; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs prop-weil-pbc-levelwise-truncations: Existing statement concerns Levelwise truncations of the adic tower; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs thm-weil-pbc-integral-truncations: Existing statement concerns Truncations of the integral category; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-envelope-tstructure: Existing statement concerns The envelope inherits the t-structure; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs def-weil-t-structure: Existing statement concerns t-structure; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs prop-weil-localized-tstructure: Existing statement concerns The rational t-structure; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs def-sbc-standard-tstructure-derived-category: Existing statement concerns The standard t-structure on the derived category of an abelian category; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-coproduct-truncation-couple: Existing statement concerns Natural coproduct truncation exact-couple comparison; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-cycles-unit-naturality: Existing statement concerns Derived-unit naturality on the canonical cycle map; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sc-left-exact-upper-truncation-comparison: Existing statement concerns Raw and derived upper-truncation comparisons; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-single-shift-normalization: Existing statement concerns The actual unit on a single object normalized in every integer degree; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sc-derived-lower-truncation-cycle-formula: Existing statement concerns Canonical bottom derived comparison on cycle classes; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-def-pc-derived-bottom-comparison: Existing statement concerns Specified double-truncation bottom comparison; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-derived-lower-truncation-step-ses: Existing statement concerns Successive lower truncations have a two-term kernel quasi-isomorphic to one cohomology object; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-lower-truncation-transition-kernel: Existing statement concerns Kernel geometry and homology of a fixed successive lower truncation transition; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-bottom-cycle-transport: Existing statement concerns Canonical cycles transported through double truncation to the actual single-object unit; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-qcoh-sections-left-exact-bottom: Existing statement concerns Left exact bottom cohomology after lower truncation; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sc-affine-algebra-upper-truncation-edge: Existing statement concerns Canonical affine edge on upper truncation; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-natural-bounded-below-truncation-couples: Existing statement concerns Individual bounded-below truncation couples with natural comparisons; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-cycles-map-homology: Existing statement concerns Homology of the localized canonical cycle map; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-bottom-unit-normalization-formula: Existing statement concerns Canonical-cycle formula for the specified bottom comparison; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-lem-pc-derived-bottom-inclusion: Existing statement concerns Every morphism from a single object factors through the bottom-homology inclusion; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs new-affine-derived-sections-truncated-bottom: Existing statement concerns Lowest cohomology of truncated derived affine sections; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-raw-truncation-couple-naturality: Existing statement concerns Naturality of raw truncation maps for one derived morphism; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sc-derived-lower-truncation-unit-bridge: Existing statement concerns Bottom derived unit through good lower truncation; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pc-derived-bottom-unit-normalization: Existing statement concerns Bottom-cohomology comparison normalized by the actual right-derived unit; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sc-left-exact-truncation-cycle-formula: Existing statement concerns Underived left exact lower truncation on cycles; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-derived-functor-negative-vanishing: Existing statement concerns Right derived functors move to the right; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-truncation-step-ses: Existing statement concerns The step tau_{<=q-1}K -> tau_{<=q}K of canonical truncations: short exact sequence and quasi-isomorphism of the cokernel to H^q(K)[-q]; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-truncation-descends: Existing statement concerns Canonical truncations and H^q(-)[-q] descend to functors on D(A), with i_q, j_q natural; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-upper-step-quotient-coordinates: Existing statement concerns Degreewise coordinates of the cokernel of successive upper truncations; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-cohomology-pullback-degree-zero: Existing statement concerns Degree-zero cohomology and the degree-zero pullback map; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-two-term-coimage-quasiiso: Existing statement concerns The cohomology projection of an arbitrary two-term coimage complex is a quasi-isomorphism; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-derived-functor-truncation-iso: Existing statement concerns Low-degree cohomology of a right derived functor sees only low degrees; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-derived-functor-truncation-iso-epi: Existing statement concerns Low-degree derived cohomology map is epi; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-truncation-triangle: Existing statement concerns The truncation triangle tau_{<=q-1}K -> tau_{<=q}K -> H^q(K)[-q] is distinguished; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-weil-pbc-derived-functor-truncation-iso-mono: Existing statement concerns Low-degree derived cohomology map is mono; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-pur-exact-derived-adjunction-bounds: Existing statement concerns Exact derived adjunctions: lower bounds, reflection and counits; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sf-derived-concentrated-single: Existing statement concerns A complex with cohomology in a single degree is that cohomology object shifted; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.

lem-weil-pbc-heart-test-bounded-below vs lem-sf-derived-truncation-triangle: Existing statement concerns Canonical truncation triangle in the derived category; the new statement tests isomorphy of a shift-compatible transformation between two general lower-bound-preserving triangulated functors on a possibly unbounded-above complex, including its specified naturality formula.
