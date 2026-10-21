## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-integral-ctf-triangulated.json`: existing statement, re-split; statement unchanged, assembly proof 2160 characters.
- `dag/nodes/sec-smooth-purity/lem-weil-proetale-tor-interval-shift.json`: statement, unsplit, no Mathlib match. Fixed-coefficient tensor/cohomology shift isomorphisms, the precise translated Tor interval, fixed-interval isomorphism invariance and zero.
- `dag/nodes/sec-smooth-purity/lem-weil-proetale-tor-interval-triangle.json`: statement, unsplit, no Mathlib match. Tensor cohomology exact segments and the middle-vertex Tor bound, for arbitrary ordinary constant coefficient rings and arbitrary derived vertices.
- `citations.json`: verbatim statements backing every step citation. `searches.jsonl` is the unedited msearch log. No Lean, unit, chapter, repository or launcher file was written.

## Attachments

None. The assigned theorem `WeilConjectures.integral_ctf_isTriangulated` in `lean/Sheaf/Paper/IntegralCtfTriangulated.lean` still ends in `sorry`. Its six-step docstring agrees with the argument being redistributed.

I also read `lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/Shift.lean`, especially `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn.shift`, and `LocalizationFiniteTor.lean`, especially the zero and first-vertex statements. These use the categorical coefficient-sheaf presentation; the new statements concern ordinary modules over the actual constant ring sheaf, with the K-flat tensor and Tor tests recorded by our definition. An identification between presentations is not assumed silently. The existing `lem-exc-intrinsic-tor-amplitude-transport` supplies such a comparison only for finite A. The new nodes quantify over arbitrary commutative A, so these are not exact attachments.

The already-proved `finite_ctf_isTriangulated` in `Sheaf/Paper/FiniteCtfTriangulated.lean` has quantitative clauses for arbitrary complexes, but only for the finite rings A_(E,n). Its private tensor_functor, tensor_homology_vanishes, amplitude_iso and amplitude_mono explain the proof mechanism; they do not give a public declaration stating either full new node for arbitrary A.

## WANTED

None. The necessary Stacks source and the current blueprint are present.

## What was wrong and what changed

This is the deliberate re-split requested on 2026-10-21, not a claim that the earlier mathematical argument was false or that its reviewed state was stale. I kept the item statement exactly, including its coefficient conventions and all closure clauses. There is no statement dispute.

The old proof carried two separate fixed-coefficient arguments inside an integral assembly: tensor/cohomology shift calculus and the long-exact-sequence argument for tensor images of triangles. They now have separate, self-contained statement-only nodes. Neither node asserts a subcategory theorem, deals with integral coefficients or reductions, quantifies over j, assumes constructibility, or asserts any clause of P for an integral object. They concern arbitrary ordinary coefficient rings and arbitrary derived complexes; the parent must still supply exact coefficient reduction, integral constructibility, simultaneous interval choices and the full-subcategory criterion. In particular no new lemma simply restates the item or its integral shift/extension clauses.

The existing finite-stage sibling is not used as a duplicate interface for these calculations: its finite-ring conclusion cannot state the arbitrary-ring results. The actual proof route is unchanged: exact reduction, tensor cohomology calculus, bounds uniform in j. The unit has no proof steps/realization entries to modify. I read both its recorded chapter/unit and the current relocated blueprint `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/def-weil-finite-tor-amplitude.md`. Below that integral paragraph these are supporting arguments, not a change to the chapter or unit route.

I removed only the transitive implementation entries from the item's stmt_deps: K-flat resolutions, change of rings, completeness and reduction-tower nodes are needed by its cited definitions, but are not separately introduced in its statement. The six nodes actually referenced in the statement remain. Source, Lean, reviewed and other maintainer fields were retained.

## Arguments assigned to future workers

These are explanations in this report, not proofs placed in the unsplit nodes.

For the shift node, construct the derived tensor by resolving a degree-zero test sheaf by a K-flat complex. The signed total tensor shift map descends to a natural isomorphism of derived objects; compose it with the cohomology shift identification to obtain H^i((K[m]) tensor N) = H^(i+m)(K tensor N). This proves the interval [a-m,b-m], and shifting back gives the converse. Tensor and cohomology are functors, so they take an isomorphism K to L to isomorphisms on every tensor cohomology test. Use the zero K-flat complex for zero, whose tensor and cohomology vanish. This packages the old fixed-coefficient isomorphism/zero/shift argument, including the comparison on which those vanishings depend; it does not create individual nodes for elementary isomorphism or zero facts.

For the triangle node, resolve the test module sheaf by a K-flat complex and use exactness of the descended tensor functor. Its image of the supplied distinguished triangle is distinguished, with its connecting map. Apply the ordinary long exact cohomology sequence and take its three equal-degree terms. For every i below both lower endpoints or above both upper endpoints, the outer terms vanish, so exactness forces the middle term to vanish. Universal quantification over all test sheaves gives the minimum/maximum Tor interval; equal input intervals give precisely [a,b]. This is the source's omitted argument in 08G2, not an appeal to constructibility or an inference from the definition of Tor amplitude alone. The parent retains the elementary enlargement to a common interval across every j; the new node owns the tensor-triangle exactness argument.

The old reduction-exactness argument remains supported by the existing exact reduction definition (which already states change of rings). The old uniform minimum/maximum calculation remains an explicit elementary parent step. The old full-subcategory assembly remains the final parent step. Thus no argument is discarded in order to meet the size limit.

## Searches

Before writing nodes I searched the whole DAG by title and statement for Tor amplitude, shifts, triangles and uniform intervals, and by source tags 08FZ and 08G2; I opened all same-tag statements. I ran blueprint_refs ancestor on the item and blueprint searches for `uniform`, `Tor amplitude`, `Tor amplitude in`, `tor-amplitude in`, `Tor interval`, `tensor cohomology`, `Tor interval shift` and `Tor interval triangle`. The closest imported entries concern finite coefficient constructibility, local/global Tor dimension, or comparison of sites; no blueprint entry states either new result. The new blueprint references name def-weil-finite-tor-amplitude, via this item, with the precise old argument served.

Each new node has its own two semantic phrasings, a Loogle substring query, a whole-Mathlib grep and a LeanSearch attempt, all executed with msearch.py and copied verbatim into mathlib_searches. For the shift node LeanSearch was rate-limited and is recorded unavailable. Both LeanFinder attempts worked: the first returned sheaf cohomology/Ext and representation Tor, the second cochain quasi-isomorphism shifts and t-structure shifts. These do not assert the all-module tensor tests of Tor amplitude. For the triangle node LeanSearch returned generic triangulated-subcategory and short-exact-sequence triangles; LeanFinder returned derived t-structure bounds, Ext connecting maps and a projective Tor-vanishing lemma. None supplies the module-sheaf tensor functor/predicate bridge and the Tor interval statement. Both Loogle substring queries and both whole-Mathlib Tor-amplitude greps returned zero hits. Neither new node is a Mathlib leaf.

## Not duplicates

lem-weil-proetale-tor-interval-shift vs def-weil-proetale-tor-amplitude: the latter defines the all-module-sheaf vanishing predicate; it does not prove tensor/cohomology shift comparisons, shifted interval equivalence or zero/isomorphism closure.

lem-weil-proetale-tor-interval-shift vs lem-exc-intrinsic-resolution-tensor-homology: the latter compares two coefficient presentations for finite A; it gives no shifted-object or interval conclusion for arbitrary A.

lem-weil-proetale-tor-interval-shift vs lem-exc-intrinsic-tor-amplitude-transport: the latter compares finite-A intrinsic and fixed-scalar presentations at one interval; it does not translate intervals under shifts or address arbitrary A.

lem-weil-proetale-tor-interval-shift vs lem-sfb-proetale-tor-local-global: the latter requires quasi-compact Y and compares local/global existence of finite Tor bounds; it does not give tensor shift isomorphisms or the quantitative shift formula on arbitrary Y.

lem-weil-proetale-tor-interval-shift vs lem-weil-finite-ctf-triangulated: the latter concerns the finite rings A_(E,n) and a constructible subcategory, with quantitative finite-ring clauses; the new result holds for arbitrary A and gives the actual tensor/cohomology isomorphisms for arbitrary complexes.

lem-weil-proetale-tor-interval-shift vs lem-weil-integral-ctf-triangulated: the item concerns simultaneous finite reductions of a derived-complete constructible integral object; the new result has a single arbitrary constant coefficient ring and no integral object, reduction, uniformity or subcategory assertion.

lem-weil-proetale-tor-interval-triangle vs lem-weil-finite-ctf-triangulated: the latter is a finite A_(E,n) constructible-subcategory theorem, even though its quantitative Lean clauses allow arbitrary complexes; the new node is valid for every commutative A and states the tensor cohomology exact segments and unequal endpoint bound without finite coefficients.

lem-weil-proetale-tor-interval-triangle vs lem-weil-integral-ctf-triangulated: the item concerns uniform finite-level Tor bounds within an integral constructible category; the new node concerns one triangle over one arbitrary constant ring, makes no completeness/constructibility claim and cannot provide the integral assembly.

lem-weil-proetale-tor-interval-triangle vs lem-kun-derived-tensor-triangulated: this existing lemma gives exactness of the tensor functor on the small etale site; it neither states the pro-etale tensor-cohomology segment nor the quantified Tor interval consequence.

## Review by Q18

I read 08FZ (definition-tor-amplitude), the exact tensor construction immediately before definition-derived-tor, 06YY (lemma-derived-base-change), and 08G2 (lemma-cone-tor-amplitude), including its omitted-proof hint. The new shift statement spells out the tensor and cohomology identifications required by the original argument, not just a qualitative finite-Tor statement; the triangle statement spells out the precise exact cohomology segment from the hint and keeps the same interval. Both statements introduce Y, A, the site, ordinary modules, derived category, tensor, cohomology, all vertices/test sheaves and integer parameters. Neither contains a proof sketch in its statement; proof and proof_deps are empty and status is unsplit.

For parent step 1 I opened def-weil-integral-derived-reduction and verified that its statement explicitly gives the exact functor L pi_j^* from completed integral coefficients to the constant finite ring category. It is not being cited merely as a name for a tensor object. I also opened def-weil-derived-complete-integral-detailed, whose statement actually requires every reduction to lie in finite bounded constructible complexes. The cohomological-support uniformity in that definition is retained; it is never mistaken for a Tor bound.

For step 2 I checked the integral constructible triangulation statement explicitly contains isomorphism closure and zero, while the new shift node explicitly contains fixed-interval isomorphism invariance and the zero tensor calculation. Reduction isomorphisms and zero come from step 1, not from an uncited comparison of coefficient categories.

For step 3 I verified that the same integral triangulation statement contains every integer shift, and that the new shift statement contains exactly [a-m,b-m] together with the isomorphism clause needed for the reduction comparison. The input prime, extension and scheme do not change with j. Both a-m and b-m are independent of j, remain ordered, and the converse really uses -m and isomorphism closure.

For step 4 I re-read the Tor definition: its universal vanishing outside an interval is precisely what permits enlarging to [min(a_K,a_M),max(b_K,b_M)]. I wrote the elementary containment argument rather than making it another node. For step 5 I checked the integral constructible triangulation statement really provides L and that the new triangle lemma really gives the middle-vertex common interval, including all degree-zero test sheaves. Step 1 provides a distinguished triangle in the correct finite-coefficient category, so no argument applies a theorem in an integral coefficient category to a finite reduction.

For step 6 I opened def-weil-triangulated-subcategory: its zero, integer shifts and middle-extension conditions are exactly those supplied above, and it states the inherited triangulation. All uses in all steps have verbatim statement quotations in citations.json. I did not use the proof of a cited node as though it were its statement, nor assume bounded constructibility alone implied finite Tor amplitude.

I tested the sign of the shift on A[0]: A[1] has support degree -1, which agrees with [0-1,0-1]. The inverse shift recovers [0,0]. I tested zero K, zero test sheaf, the empty scheme and the zero coefficient ring: all tensor cohomology vanishes and the ordered intervals remain legitimate. For triangle bounds, equal intervals give no spurious +/-1, and the split triangle U -> U direct-sum W -> W confirms the min/max endpoints; disjoint or negative input intervals also give an ordered enclosing interval. No nonempty scheme, nonzero ring, regular coefficient ring, finite Tor property of A, or constructibility hypothesis was added.

I checked the two new nodes are independent of the parent and each other, and retain no backward references in stmt_deps. I preserved the original statement and maintainer-owned fields and checked all parent steps are under 2000 characters and the aggregate proof is below 3000. No source error or open mathematical issue was found. The intended new proof tasks are the two fixed-coefficient tensor/cohomology arguments, and the parent remains a complete explicit assembly of their statements.

## What could not be finished

Nothing in the stage-1 split remains unfinished. The new nodes intentionally await independent splitting/proofs; no Lean proof is claimed here. Delivery checks follow this review.
