# Q39: lem-sfb-space-inverse-module-polynomial-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-polynomial-model.json: item, statement, split; statement unchanged. Six source-following steps construct the finite-free polynomial model, its localizations and its A-K-flatness.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-perfect-tests.json: new statement-only node, unsplit, no Mathlib match. It states the perfectness assertion of Stacks 0CX6(1).
- citations.json: a verbatim statement excerpt for each citation in each numbered proof step.

## Attachments

None. The live WeilConjectures source has no declaration tagged with the item's id or a theorem asserting the full inverse-system polynomial-model statement. Searches by pseudo-coherence and polynomial models found other affine/Tor lemmas, not this result. No compiler was run and no Lean was written.

## WANTED

None: all the sources used are present in literature/stacks-project/.

## What was wrong or changed

The item was an unsplit, statement-only prerequisite created by Q47. Its mathematical statement is correct and was retained, including the chosen polynomial presentation, the D_QCoh homotopy limit and arbitrary principal localizations. The source route is Stacks 0CX7, not absolute pseudo-coherence of K: X/A need not be flat. I explicitly avoided applying the existing space-perfect-tests-pseudocoherence node, whose flatness hypothesis is absent here.

The imported blueprint ancestry ends in a null blueprint id. Running tools/blueprint_refs.py ancestor printed None; I retained that ancestry and filled the new node's exact place and via list as prescribed. I read the current latest blueprint sk-thm-sf-ctf-stability section and direct-images proof (3), not an old snapshot. This item is an inherited coherent-family effectivity tool below that proof, not the unit's key statement. No unit realization is changed.

In my draft self-review I removed an unjustified assertion that restricting a K-injective B-complex to P remains K-injective. The final affine comparison instead uses the actual statement of lem-pc-affine-pushforward-resolution-quasi-iso on a termwise quasi-coherent tilde complex. I also corrected the scheme affine relative-pseudo-coherence source tag to 09VF: 09UM is another lemma. These were draft proof/citation corrections, not statement changes.

## Searches

I searched the complete DAG by 0CX6, 0CX7, 0CSX, 09UU, inverse systems, perfect tests, relative pseudo-coherence, and affine localization. Whole-blueprint searches were run for pseudo-coherent, relative pseudo, finite free, inverse limit, affine localization, proper support, perfect tensor and infinitesimal perfect. None states the new 0CX6 perfect tensor-test assertion. The existing general test-detection, approximation, affine finite-free-model, localization, and K-flatness nodes are reused rather than duplicated. Their downstream dependency closures were checked to ensure they do not use this item.

All new-node Mathlib queries were actually run through msearch.py and read. Two distinct semantic phrasings for the new node gave condensed-module and ordinary sheaf-limit declarations, not the required perfectness of the tensor tests. LeanSearch likewise returned ordinary global-section/limit statements. Loogle's "Perfect", "limit" query returned zero hits, and grep for Rlim|rlim|inverseLimit|IsPerfect in Algebra/Homology found only CochainComplex.plus closure under limits. For the item, polynomial pseudo-coherence queries found K-projectivity, ordinary finite-presentation sheaves and scheme limits, none supplying the claimed model. Existing searches on the repository item were retained as history; new recorded searches are in this sandbox's searches.jsonl. No service failure was recorded as absence.

## Not duplicates

lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-flat-proper-support-inverse-effectivity: the shared tag 0CX4 is only the common inverse-system situation; the existing theorem constructs an algebraized finitely presented flat module with proper support, whereas the new lemma asserts perfectness of global derived tensor tests of the D_QCoh homotopy limit. The existing conclusion does not identify that homotopy limit with its module, and using its proof here would be circular.

lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-inverse-module-affine-base-change: the latter cites 0CX6 as background but states projection-induced base-change isomorphisms on arbitrary qcqs etale charts; it does not assert that global tensor tests against perfect E are perfect over A.
lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-inverse-modules-near-special-fibre: the latter cites 0CX6 in its proof route but states a degree-zero finitely presented model only on an open neighborhood of the special fibre; it does not state perfectness of the global tensor tests.
lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-inverse-module-derived-limit: the shared situation is 0CX4; this existing node constructs the limit and bounds its cohomology, without any perfect-test conclusion.
lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-perfect-to-pseudocoherent-tests: the existing node assumes pseudo-coherence of the perfect tensor tests and extends to pseudo-coherent tests; the new node establishes the stronger perfectness input for this particular infinitesimal system.
lem-sfb-space-inverse-module-perfect-tests vs lem-sfb-space-perfect-tests-pseudocoherence: the existing node detects absolute pseudo-coherence for a flat finitely presented source; our new node concerns perfectness of global tensor tests of an inverse system and does not assume X/A flat.

## Review by Q39

I read spaces-flat.tex Situation 0CX4 and Lemmas 0CX5 through 0CX9 in full, including the proof of 0CX6. The new node is exactly the first assertion of 0CX6(1), strictly below this item: it gives a global perfect tensor test, no polynomial presentation, localization, or K-flat conclusion. Its full statement repeats the inverse-system data and explicitly introduces perfect objects and derived tensor/global sections. The eventual split of this new node follows the source: apply the perfect RHom/proper-support base-change theorem at each finite level, use the perfect inverse-limit theorem, commute RHom from a perfect object with products, and dualize. I did not insert that future proof into the new statement or proof fields.

Step 1 uses the actual boundedness assertion in inverse-module-derived-limit, affine-scheme-qcqs, and fp-qcqs-source. No flatness of X is inferred. The new perfect-test conclusion supplies bounded finite-projective complexes; the existing finite-projective-complex-free-model supplies their bounded-above finite-free replacement, exactly the definition of ring pseudo-coherence. I read both cited statements, not their proofs.

Step 2 uses space-perfect-to-pseudocoherent-tests (0CWH), whose required qcqs source and upper bound were established in step 1. I read its source in spaces-perfect.tex and checked that it permits arbitrary qcqs spaces and no X/A flatness. Then space-pseudocoherent-tests-relative (0CTT) is applicable because X/A is separated and finitely presented. I read spaces-more-morphisms.tex lemma-characterize-pseudo-coherent. The two cited statements say exactly the implication used, including relative rather than absolute pseudo-coherence.

Step 3 reads the all-chart relative-pseudo-coherence meaning in space-relative-pseudocoherence-etale-locality: the chosen U need not be surjective because the definition quantifies over every chart. I read spaces-more-morphisms.tex 0CSX and the etale/Zariski comparison node. The latter intertwines the derived pullbacks and, for qcqs morphisms, direct images used here. The surjection P to B yields a closed immersion. Polynomial projection flatness is exactly the cited polynomial-projection-flat node; finite presentation follows directly from its finite polynomial generators and empty relations. I read 09UU in more-morphisms.tex: flat locally finitely presented ambient space suffices to turn relative pseudo-coherence into absolute pseudo-coherence of Ri_*K_U. There is no hidden Noetherian hypothesis.

Step 4 checks the particular P-action, not just an isomorphism in D(A). I read 09VF's proof, which identifies the closed pushforward with the affine sheaf associated to restriction of scalars. The existing tilde-sections node supplies the standard-open formula; the fraction identity and its restriction compatibility are written out in the step. The affine equivalence supplies a termwise tilde representative; affine-pushforward-resolution-quasi-iso applies to it because its terms are quasi-coherent and i is affine. Therefore the affine-pseudo-coherent-criterion actually applies to the same derived object. This avoids the invalid K-injective restriction shortcut noted above. Both affine lemmas' full statements were read. The comparison is P-linear and therefore A-linear.

Step 5 reads localization-module-exact and affine-derived-pullback-tensor-tilde, not a definition of localization or a mere cohomology-sheaf consequence. Exact localization preserves the derived isomorphism and computes tensor with P_f for an arbitrary representative; the formula c/f^j to c/bar(f)^j identifies B tensor_P P_f with B_bar(f). The affine equivalence identifies the resulting object with actual derived sections, and the previous etale comparison permits small-etale sections. This argument uses no false claim that Rlim commutes with localization. A-linearity is checked on fractions explicitly.

Step 6 uses the polynomial definition to exhibit an A-basis for each finite free P-term. Direct sums preserve exactness by checking finite-support elements, so these terms are A-flat without a new lemma. I read the statement of affine-flat-module-localization-preserves-flatness: it permits localization by elements of P even when they do not lie in A. It yields the required A-flat localized terms. I read more-algebra.tex 064K and 06Y6; boundedness is above, exactly the convention of module-bounded-flat-kflat. The final derived-change-of-rings node explicitly says K-flat representatives compute scalar extension. Its one-object-site specialization proves the arbitrary A-algebra R clause.

For edge cases I checked r=0, B=0/empty chart, M_n=0, a constant tower, f=1, f=0, and f whose image in B is nilpotent. The zero-ring localizations cause no problem: the localized derived object and finite-free model are zero. No nonzero-base, Noetherian, nilpotence exponent, flat-X or proper-X assumption is added. Proper support is used only by the new perfect-test lemma, in exactly the form of Situation 0CX4. Every new statement introduces all objects. There is only one new lemma, and it is neither an elementary step nor a reformulation of the polynomial-model conclusion. Every non-elementary step has cited statements with the exact needed hypotheses, and citations.json contains literal excerpts. All steps are below 2000 characters. I checked delivery-errors B through E against these files and the sources; no SGA source is used. Off-unit citations are generic affine/module tools and are declared in split_report.tool_uses.

## What could not be finished

Nothing remains in the requested one-level mathematical split. The new perfect-test lemma is intentionally unsplit, as required for a new node. Server dry run and delivery results are recorded by the delivery tool.
