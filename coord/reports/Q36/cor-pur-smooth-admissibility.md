# cor-pur-smooth-admissibility — Q36 repair

## Files written

- `dag/nodes/sec-six-functors/cor-pur-smooth-admissibility.json`: existing statement, repaired stage-1 split into ten steps; statement and complete Lean record unchanged.
- `dag/nodes/sec-six-functors/lem-sf-etale-local-isomorphism-constructible.json`: one new statement-only node, not in Mathlib. It transfers a specified finite constructible stratification between etale-locally isomorphic module sheaves.
- `citations.json`: verbatim statement evidence for every citation of all ten item steps.
- `report.md`: this signed review. `searches.jsonl` retains the interrupted worker's actual searches and appends the searches for the new lemma. `repair_split.py` is sandbox-only preparation code.

One new node, zero Mathlib leaves. No unit record is edited: this item realizes the smooth case of the unit, not its whole statement.

## Attachments

None. The blueprint-id and smooth/admissibility searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration proving this complete item. I read `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension` at `SixFunctors/Etale/Derived/Stability/UpperShriek.lean:133` and `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension` at `UpperShriekConstructible.lean:63`. The former assumes finite Tor amplitude; the latter has no sharp interval assertion. Both use `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor` in `SmoothDuality.lean:62`, whose body is `sorry` at line 72. Neither is an attachment for the complete item. Searches for the new local-isomorphism/finite-stratification lemma found no exact project declaration to attach.

## Wanted sources

None for this repair. I read the physical retained master item and its Proof Step 1 at `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/cor-pur-smooth-admissibility.md`, the current statement in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/cor-pur-smooth-admissibility.md`, and the current `thm-asd-smooth-tensor.md` in `sec-six-functors-basics/sk-prop-cohsm`. I read the chapter and the current unit records. The new node's source is Stacks Tag 03RU, `etale-cohomology.tex`, label `definition-finite-locally-constant`, specifically the module-sheaf clause; the fixed-stratum cover-refinement is an author expansion of that definition, not a purported separately numbered Stacks theorem. I also read the adjacent 095G pullback statement and proof. No source was downloaded.

## Return and corrections

The human returned former step 5 (2,036 characters) because it concealed non-elementary arguments. There were no retained node/report files in the sandbox, only search logs; I recovered the complete returned proof and metadata from the shared node. This is a content repair of that proof, not an unchanged re-push.

Former step 5 is replaced by steps 5–7. Step 5 cites existing statements for forgetting constructible module structure, pullback constructibility, recovering module local constancy from finite underlying sheaves, and obtaining finite constant module values. Step 6 cites the exact-functor and shift formulas and the new fixed-stratification transfer lemma, extracting the original argument using covers of each stratum and their common refinement. Step 7 writes the elementary sheaf-uniqueness argument for zero cohomology on a covering and applies the existing constructible and comparison statements. All other arguments are retained, with only internal step numbers updated. The longest remaining step has 1,041 characters.

The statement and `lean` record are byte-for-byte equal as JSON values to the recovered base. The previous accepted finite-type typing clarification and coefficient-scope qualification remain intact; no new STATEMENT-DISPUTED correction is made. The old imported comparison mismatch stays repaired: compact-support base change is not used as an equivalence of coefficient categories. Only the bounded-class exceptional adjoint is asserted. No change to targets, chapter route, coefficient categories, or the prescribed smooth-purity route is made.

## Argument deferred to the new node

For `lem-sf-etale-local-isomorphism-constructible`, fix one given stratum i:Z→X, a cover W_t→Z making i⁻¹G constant with finite module values M_t, and the pulled-back cover Z×_XU_j→Z. The fibre products W_t×_XU_j form an etale covering of Z. Restrict the given module isomorphisms to these fibre products and pull back the constant-module trivializations: the restriction of i⁻¹F is the constant sheaf with value M_t. This uses inverse-image composition and constant-module pullback, not descent of a global isomorphism. The same finitely many strata therefore witness constructibility. The new node deliberately has no proof or proof dependencies; this paragraph records the future worker's argument. Its source definition and the existing exact inverse-image/constant-pullback infrastructure specify the intended meaning.

The extraction is explicitly required by the human's return: the covering comparison formerly carried inline in step 5 is now an independently quantified module-sheaf statement. It is smaller than either clause of the item: it involves no exceptional functor, smoothness, derived category, shift, Tor amplitude or pro-etale comparison. The other hidden arguments already have nodes and are cited instead of creating duplicates.

## Mathlib searches

The interrupted worker's four searches are retained and were read before using the recovered item's searches. For the new lemma I ran LeanFinder with the etale-local-isomorphism/constructibility phrasing, Loogle `"IsConstructibleSheaf"`, the full Mathlib grep `constructible.*(sheaf|Sheaf)|IsConstructibleSheaf`, and LeanSearch with the module-sheaf local-isomorphism phrasing. I then tried a second LeanFinder phrasing emphasizing the same finite stratification and a second grep for local constancy and covers under `CategoryTheory`. The exact strings and actual responses are in the command-generated log and the new node's `mathlib_searches`.

LeanFinder's first hits include `SheafOfModules.isFinitePresentation`, `SheafOfModules.IsFiniteType`, `SheafOfModules.IsFinitePresentation`, the etale site definitions, and `CategoryTheory.Sheaf.isConstant_congr`. The second phrasing returns condensed locally constant models and `CategoryTheory.Sheaf.isConstant_iff_of_equivalence`. I read `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean:88` and `:165`: isConstant_congr requires an actual global isomorphism and an already constant sheaf; the equivalence lemma requires an equivalence of entire sheaf categories. Neither states preservation of a prescribed constructible stratification from isomorphisms on a covering. LeanSearch's module-sheaf constructors and tilde sheaves likewise do not state it. Both grep queries and Loogle had zero hits. No candidate is an exact match or a one-line specialization. No service failure was treated as evidence of absence, and no unrun search is recorded.

## Not duplicates

The whole DAG and imported blueprint were searched for constructible locality, local isomorphism, locally constant, constructible pullback and Tag 03RU before creating the lemma. The existing global-isomorphism invariance node does not assert etale-local isomorphisms or preserve a specified stratum family under such a cover. Surjective constructible pullback requires a surjective qcqs scheme morphism and asserts global constructibility; it does not give this same-stratification conclusion for an arbitrary covering family. Their auxiliary reductions would add different arguments to the retained proof. The new lemma has `same_as: []` and blueprint ancestry directly at the item's Proof Step 1.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-abelian-zn-module-constructible: changes abelian coefficients to Z/n modules; it does not compare two module sheaves on an etale cover.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-module-finite-stalks: deduces finite stalks of one constructible sheaf; it has no second locally isomorphic sheaf or stratification-transfer assertion.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-finite-local-abelian-forget: compares abelian and set local constancy, with no constructible partition or pair of locally isomorphic module sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-module-underlying-sets: forgets module structure on one sheaf; it does not transfer a stratification between different sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-torsion-modules-agree: compares torsion abelian and Z/n-module structures on a curve, rather than arbitrary locally isomorphic module sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-field-finite-separable-constant: provides a finite separable trivializing extension over a field; it has no general scheme or fixed-stratification comparison.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-cyclic-module-constant-reflection: reflects constant abelian structure into cyclic module structure on one localized site, without a constructible partition.

lem-sf-etale-local-isomorphism-constructible vs def-weil-pbc-etale-constructible-sheaf: defines constructibility of a single module sheaf; it does not state transfer through local isomorphisms.

lem-sf-etale-local-isomorphism-constructible vs def-weil-pbc-constructible-abelian-sheaf: defines constructibility for abelian sheaves, rather than transferring a module-sheaf stratification.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-finite-constant-abelian-refinement: refines a finite underlying set cover into constant abelian sheaves; it has neither module comparison nor a finite stratification.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-finite-locally-constant-module-values: identifies finiteness formulations for one locally constant module sheaf, without transfer of a stratification from another sheaf.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-finite-constant-abelian-neighborhood: constructs constant abelian neighborhoods from one finite constant underlying set; it has no constructible stratification transfer.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-abelian-bounded-exponent: bounds the exponent of one constructible abelian sheaf on a quasi-compact scheme; it does not compare locally isomorphic module sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-finite-local-cyclic-module-forget: compares cyclic module and underlying abelian local constancy for one sheaf, rather than transferring a finite constructible partition.

lem-sf-etale-local-isomorphism-constructible vs lem-weil-pbc-constructible-etale-module-sheaf-comparison: identifies two constructibility predicates for the same sheaf; it gives no comparison between different locally isomorphic sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-galois-flc-set-stalk-finite: deduces finite stalks from finite constant values for a set sheaf; it has no module stratification transfer.

lem-sf-etale-local-isomorphism-constructible vs lem-galois-flc-set-is-finite-sheaf: deduces a finite-sheaf predicate for one sheaf of sets; it has no pair of locally isomorphic module sheaves.

lem-sf-etale-local-isomorphism-constructible vs lem-galois-flc-representable: represents finite locally constant set sheaves by finite etale schemes; it does not transfer a module constructible stratification.

## What remains unfinished

The new statement-only local-isomorphism lemma is intentionally left unsplit for its own stage-1 worker, and all existing cited nodes retain their own states. The item itself is fully split one level. No Lean was written and no compiler or build command was invoked. A local exploratory dependency traversal encountered the baseline missing id `def-weil-pbc-etale-morphism`; only the required server overlay checks decide the delivery's DAG validity, and no existing node or tool is altered to work around this baseline condition.

## Review by Q36

I read delivery-errors B–E and the actual statements cited by the repaired proof. I checked the original master proof and the current blueprint statement/update, the current unit's smooth case, and the physical Stacks 03RU module-sheaf definition used by the new node. The repair follows the retained local rank-one dualizing-line calculation. It does not replace the smooth-purity route with a different trace construction.

Steps 1–4 are retained verbatim. In step 1, finite type over the field gives Noetherian schemes via `lem-weil-pbc-finite-type-over-noetherian`, and `lem-weil-pbc-locally-noetherian-quasi-separated` plus quasi-compactness meets `thm-nagata-compactification`. The coefficient-extension definition and the DVR and finite-quotient lemmas give finite A. The written calculation ell in (varpi) implies ell^n in (varpi^n) gives an annihilating integer invertible on Y. These are precisely the hypotheses of `thm-asd-smooth-tensor`; smoothness and the pure relative dimension are hypotheses of the item. In step 2, I checked both constructible-origin equivalence clauses and the exact comparison cohomology formula, which supply G and reflect its vanishing interval. The exceptional-inverse-image definition explicitly states the formula on etale-origin inputs; its separate preservation discussion is not a premise. `cor-sf-ambient-adjoint-discharge` concerns only the bounded class here. In step 3, `thm-asd-smooth-tensor` states the rank-one local system and tensor formula for every ordinary etale complex. Step 4 uses monoidal inverse image, exact module pullback and tensor triangulatedness; the K-flat definition computes the unit constraint P tensor A = P. These statements support the local shifted-pullback formula without finite Tor amplitude.

Step 5 now names each coefficient-structure fact that the former long step handled inline. `lem-weil-pbc-constructible-module-underlying-sets` explicitly retains the same set stratification on forgetting module structure. `prop-constructible-pullback` gives constructibility of the underlying pullback; module inverse image has this underlying sheaf by `prop-weil-pbc-inverse-image-modules-exact`. The set-sheaf stratification has finite locally constant restrictions. On each such actual stratum, `lem-pod-module-local-constancy-of-finite-underlying` applies because A is finite; it gives module local constancy without requiring connectedness. `lem-weil-pbc-finite-locally-constant-module-values` then uses the already finite geometric stalks to give finite constant module values. Thus Q^r is constructible in the module sense, not just in the set sense. The exact-functor cohomology statement is available for arbitrary complexes and every integer, so its historical bounded-below name adds no unintended hypothesis. I corrected the old omission of explicit nodes for forgetting and restoring module structure.

In step 6 the exact-functor cohomology formula and `lem-sp-derived-cohomology-shift` give the actual module-sheaf isomorphisms u_i⁻¹F^r ≅ u_i⁻¹Q^r. I checked the new lemma's hypotheses one by one: X is a scheme, A finite commutative, the two objects are actual A_X-module sheaves, Q^r has a finite constructible stratification from step 5, and the same etale covering family supplies the module isomorphisms from step 4. Its conclusion is exactly that F^r has that same finite stratification. The fibre-product/refinement argument formerly inline is now the new node. The source definition allows arbitrary covering families and varying finite module values. No compatibility on overlaps is needed, because local constancy does not glue these isomorphisms to a global isomorphism.

In step 7 the shift sign is checked using H^r(C[2d])=H^(r+2d)(C). Zero on a pulled-back covering implies zero by sheaf uniqueness, with its section-level argument written. Constructibility of each cohomology sheaf comes from step 6, and `def-weil-pbc-constructible-complexes` gives precisely bounded constructibility once all degrees outside the shifted interval vanish. The origin equivalence and exact comparison statement then give the pro-etale assertion and the same interval; no comparison theorem about compact-support base change is substituted for these statements.

Steps 8–10 are the retained original steps 6–8, with cross-references renumbered. For step 8, comparison-Tor direction (ii) applies to the bounded constructible G (hence bounded below) and the assumed pro-etale Tor interval; the residue test is applied only to an ordinary etale bounded constructible complex over the DVR quotient A. In step 9, bounded constructibility of H has already been proved in steps 5–7. The monoidal inverse-image statement applies both to u and f, the constant-pullback statement identifies the residue field sheaves, and tensor triangulatedness and exact-functor cohomology produce the displayed residue-tensor shift. The input residue interval is step 8. For step 10, the residue criterion applies to that bounded constructible etale H, then comparison-Tor direction (i) gives Tor amplitude against all pro-etale degree-zero module sheaves. The finite-Tor and admissibility definitions give the claimed interpretation with signed constants -2d. This retains the independent constructible interval clause for inputs without finite Tor amplitude.

For the new node I checked the empty scheme and zero sheaves (vacuous finite-value assertions), the identity cover (ordinary isomorphism invariance), an infinite etale covering, different local module values on disconnected members, and a nontrivial locally constant twist of G. The lemma asserts constructibility and the same strata, not a false global isomorphism F≅G; that is why no overlap cocycle is required. The item at d=0 has no shift and at d=1 sends degree 0 to degree -2. At n=1 the coefficient ring is a field. At n>1 a constructible residue-field sheaf may have infinite Tor dimension, but steps 5–7 still apply since they never use the residue Tor test. Only steps 8–10 assume input finite Tor amplitude. Neither an empty source nor zero input needs a nonempty trivializing cover.

I checked that the new statement introduces all objects and cites definitions for its notions, carries no proof sketch or proof dependencies, and is strictly smaller than a preservation clause. It is extracted in compliance with the explicit human return, while existing coefficient-structure lemmas are reused. All mathematical uses in each step have a node citation, and `citations.json` copies the actual statements verbatim, including the new fixed-stratification conclusion. The item and new node have precise blueprint ancestry. Off-unit generic tools added by this repair are declared in `split_report.tool_uses`, with no change to the maintainer-owned accepted `tool_uses`. Mathlib candidates were read and rejected for concrete missing hypotheses/conclusions, not simply by name. No duplicate, elementary numerical shift lemma, entire-clause restatement or circular invocation of this item was introduced.

## Validation

The required server dry run is run after this signed report is written; its final result is appended below. Only one deliver.py invocation is active at a time.

First dry run exited with no push and reported only that the new node lacked chapter and unit fields. Added its inherited chapter sec-six-functors and unit sk-prop-sf-rf-shriek-preservation; no mathematical content changed. The next dry run checks this repaired metadata.

Final required dry run exited 0: `OK (not pushed) deliver/Q36/cor-pur-smooth-admissibility at 4383070280: preflight passed`. Server preflight, including check_dag and review_split, accepted the corrected overlay. The pending-node baseline issue noted during exploratory traversal did not block the server overlay. Delivery follows with the same mathematical node and citation files; this paragraph only records validation.
