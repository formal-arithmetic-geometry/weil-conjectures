## Worker report

Files written: dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-normality-finite-inseparable-test.json (item, statement, split; no Mathlib match), citations.json, and this report. The required search command also wrote searches.jsonl.

## New nodes

None; 0 new nodes, 0 new Mathlib leaves. Existing DAG statements supply all non-elementary inputs.

## Attachments

None for the item. The project search for its blueprint tag and geometric-normality terminology found no exact declaration. Algebra.exists_finite_purelyInseparable_separable_extension in lean/WeilConjectures/FieldTheory/MakeSeparable.lean, lines 38–64, proves the refinement lemma already attached to lem-weil-pbc-make-separable; it proves only a supporting fact, not this item.

## WANTED

None. The proof follows the local Stacks algebra.tex, Tag 037Z, label lemma-geometrically-normal, specifically (3) implies (2), then (2) implies (1), with the converse obtained by restricting the universal quantifier. All sources used are present.

## Findings and changes

The input statement agrees with 037Z's equivalence of (3) and (1), including its lack of finite-type, Noetherian, domain, or nonzero assumptions. No statement correction was needed. The item had no proof. I supplied eight steps and their dependencies, retaining the original statement, source, blueprint provenance, original searches and other metadata. Five actual searches made for this delivery are appended to the existing search record. Loogle and grep had no hits. The two semantic phrasings returned normal field extensions and geometrically reduced algebras; none states the normal-ring criterion. I read the definition of Algebra.IsGeometricallyReduced in Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:54–56, which asserts reducedness, not integral closedness of prime localizations. This is not a Mathlib leaf.

## Blueprint and duplicate searches

I read the chapter and unit records, SETUP's three levels, the current latest unit text and the current latest lem-per-artin-gabber-affine-curve.proof.md. This algebraic item realizes the ancestor Step 3 completion subargument identified in its existing blueprint.from.place; it does not change any chapter or unit route. The latest ancestor proof does not spell out the normality criterion. blueprint_refs.py ancestor gives lem-per-artin-gabber-affine-curve, with the existing via chain retained. Whole-blueprint searches for "geometrically normal", "037Z", and "finite purely inseparable" returned no equivalent blueprint node, hence same_as remains empty.

Whole-DAG searches by 037Z, normality terminology, and each source label found lem-weil-pbc-geometrically-normal-perfect-closure-criterion and lem-weil-pbc-normality-perfect-closure-test. These assume a perfect purely inseparable overfield and do not state the finite-test hypothesis of the item. I did not cite them to restate the conclusion. I instead reused the DAG's exact statements for 030R, 037X, 00T4, 033C, 00DK, 033G, 037D and the tensor algebra universal property. The analogous proof already recorded under the perfect-closure criterion was useful cross-checking material, but this split follows 037Z directly. No new node was created, so there are no new/existing pairs to distinguish.

## Tool uses

The split_report.tool_uses declares each generic off-unit algebraic input. The sources are the exact inputs of the Stacks 037Z argument: make-separable; the smooth fraction-field model; smooth base change and normality ascent; localization base change; normality descent along a field extension; filtered-colimit normality; and the tensor pushout property. The perverse-sheaf unit does not supply replacements for these commutative algebra tools. Definitions and Mathlib leaves are also explicitly cited where needed. I did not write maintainer-owned tool_uses.

## Review by Q129

I read algebra.tex 46885–46951, the complete statement and proof of Tag 037Z, with the item open. Its (3) is exactly our (1), and its (1) is exactly our (2). The convention for a normal ring is primewise normal domains, rather than a global domain or merely an integrally closed ring. I read def-weil-pbc-normal-ring and all four other statement-dependency definitions. Finite purely inseparable includes the identity extension, and in characteristic zero it admits only that case. Nothing in the proof excludes either characteristic.

For Step 1 the implication is the restriction of a quantifier; no lemma is hidden. For Step 2 I opened lem-weil-pbc-make-separable and lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra and read their full statements against algebra.tex labels lemma-make-separable (030R, 10513–10525) and lemma-localization-smooth-separable (037X, 44512–44523). The former really supplies both finite purely inseparable extensions and a commuting square; the latter really supplies a smooth subalgebra with the required fraction field. Its finite-generation hypothesis on K_1/k_1 is checked explicitly using generators of K/k and a finite basis of K_1/K. Normality of C is an application of the hypothesis, not an unproved subsidiary lemma. I also read the existing sorry-free supporting Lean declaration; it is not an attachment for the item.

For Step 3 I opened lem-weil-pbc-smooth-ring-map-base-change-composition and lem-weil-pbc-smooth-over-normal-ring-normal, then read the source statements lemma-base-change-smooth (00T4, 37133–37140) and lemma-normal-goes-up (033C, 46563–46569). Clause (1) of the first gives the actual base-changed ring map C -> C tensor B. The second is explicitly for arbitrary normal rings. This avoids the invalid shortcut of applying a Noetherian-only ascent theorem to C.

For Step 4 I read lem-weil-pbc-localization-base-change, including its multiplicative set and zero criterion, and algebra.tex lemma-tensor-localization (00DK, 2087 and following). I also opened lem-weil-pbc-algebra-tensor-pushout-universal-property, whose clauses give algebra homomorphisms with the displayed pure-tensor formulas and uniqueness. Localization is applied over B to R, not to C over the wrong base. The intermediate R tensor_B K_1 and both cancellation equivalences are written out. They are ring maps by the multiplication formula, balancing gives well-definedness, and inverse identities on pure tensors give inverse maps on the generated algebra.

For Step 5 I again read def-weil-pbc-normal-ring. The localization assertion is proved inline with inverse maps between T_q and R_r. Primality and disjointness of the contracted prime follow immediately from inverse images and units. The denominator b/t outside q means b outside r; s and t are already outside r. Cross multiplication verifies the fraction relations. Thus this is a routine application of the definition with the required maps displayed, not a new lemma node, and it is marked elementary. In particular S's image in R is allowed to contain zero: then T has no primes and the assertion is vacuous. No injection B -> R is assumed.

For Step 6 I opened lem-weil-pbc-normal-ring-field-extension-descent, which says exactly that normality of D tensor_K K_1 implies normality of D for an arbitrary commutative K-algebra. I read its source, lemma-descent-normal (033G, 46684–46711). The tensor maps identify precisely that scalar extension with the ring proved normal in Step 5; the lemma does not require D to be a domain or K_1/K to be separable. The two field structures come from the commuting square in Step 2.

For Step 7 I used only the already-open tensor algebra universal property. I checked the whole colimit assertion rather than assuming that a module colimit is a ring colimit. The index consists of subfields of the fixed set E and is small, nonempty and directed; finite generating sets show all these assertions. The compatible ring maps glue on E because every pair and every ring operation lies in a common upper stage. Their common map on A equips the target H with its k-algebra structure, and the tensor universal property produces the unique ring map with the required pure-tensor values. This is an elementary universal-property argument, without an uncited flatness or forgetful-functor theorem.

For Step 8 I opened lem-weil-pbc-filtered-colimit-normal-ring and read algebra.tex lemma-colimit-normal-ring (037D, 8312–8330). The node explicitly accepts a small filtered category and imposes no restrictions on transition maps. Step 7 supplies precisely such a diagram and its colimit; Step 6 supplies normality at every stage. The definition node cited in this step justifies the stated zero-ring edge case, not the colimit theorem.

The per-step entries of citations.json copy the full statement actually read for each cited node verbatim, so no proof, definition-only node, or unrelated assertion is being used as a theorem. I checked dependency closures: none of the reused proof inputs reaches this item, so the split does not introduce a cycle. All non-elementary steps have cited nodes, and every step is shorter than 2000 characters. There is no long proof step hiding a separate lemma and no new statement-only node that restates the item or one of its clauses.

I tested the argument on A=0, A=k, a finite product of copies of k, positive-characteristic imperfect k, characteristic-zero k, K=k, a transcendental finitely generated K, and an infinitely generated E. The first two and the product case confirm that global-domain reasoning would be inappropriate; the proof uses only prime-local normality. For imperfect k a purely inseparable nontrivial field algebra A can fail the finite test because its scalar extension acquires nilpotents; the argument never assumes such a tensor product is a field. The identity cases are allowed by both refinement statements. The general E case uses the small set of its finitely generated intermediate fields, not a proper class of all field extensions.

I corrected two tempting gaps before delivery: explicitly established finite generation of K_1/k_1 before invoking the smooth-model lemma, and replaced a possible appeal to flatness and reflection of colimits by the direct tensor universal-property proof. No statement dispute or source error remains. Checks B–E therefore require no new nodes: self-contained existing statements supply the substantive lemmas, while the finite-generation, fraction, tensor-map, and gluing computations remain explicit steps.

## Unfinished work

None in this stage-1 split. Existing supporting nodes retain their own proof statuses; this delivery does not claim that the resulting Lean theorem is already formalized.
