# Stage-1 report: lem-sfb-stack-qcoh-flat-atlas-exactness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcoh-flat-atlas-exactness.json: item, split into nine proof steps. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- citations.json: one entry for each of the 22 step/node citations, with verbatim statement quotes.
- searches.jsonl: five actual msearch.py searches, retaining the command's own log.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, flat atlas, QCoh, Quasicoherent and related concepts found no declaration proving this whole item. The existing project scheme flat-cover reflection declaration addresses a proper prerequisite, not stack tensor closure, cokernels or the atlas epimorphism assertion, and its existing DAG node is reused.

## WANTED

None. All mathematical inputs used are present locally.

## What changed and why

The live item was statement-only. The resumed sandbox had only dispatcher marker files, no item copy, report, search log, or active delivery process. I copied the current item and kept its mathematical statement. Its five inherited Mathlib searches are retained; the new five searches were actually run with msearch.py, with a second semantic phrasing. The semantic results are abstract local-presentation predicates and scheme morphism descent theorems. The Loogle query returned no hits; grep returned the faithfully-flat stalk argument in Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:164. I read that passage and the local-presentation source. Neither supplies stack quasi-coherent tensor/cokernel closure or the faithful atlas functor; scheme-morphism descent is also a different kind of object from the module maps here.

The proof follows Stacks 06WN's reduction to scheme slices and 0GQF's common flat scheme refinements. Instead of importing the entire abelian groupoid presentation argument to prove faithfulness and epimorphism detection, it applies the proved isomorphism test to ambient quasi-coherent cokernels. This is the elementary assembly of the same atlas test and right-exactness statements, and does not change the unit route. No new lemma was needed: in particular the scheme flat-cover isomorphism reflection, the big-fppf comparison, and the small-etale exact comparison already have precise nodes.

Read the current latest blueprint unit and direct-images proof (3). This item's inherited place is a supporting adequate-moduli/curve-moduli prerequisite of that step, not a new assertion about derived finite-Tor operations. The inherited blueprint.from.node is null; blueprint_refs.py ancestor also returns None for the live chain. Its detailed place and via list are retained. Whole-blueprint searches for flat atlas, 06WV, flat covering, quasi-coherent modules, quasi-coherent and cokernels found no equivalent blueprint node. Searches of the whole DAG found and reused the scheme and site facts listed in the proof.

No target, definition, chapter or unit record was changed. No Lean was written and no compiler, Lake, build, local check_dag, local review_split or local preflight was run.

## Not duplicates

No new node is created. The scheme big-fppf equivalence, scheme small-etale exact comparison, scheme tensor and cokernel closure, general ringed-site forgetful theorem, and scheme flat-cover isomorphism reflection are cited under their existing ids. In particular the groupoid module-descent theorem is not duplicated or specialized into another stack node.

## Review by O2

I read stacks-sheaves.tex, lemma-characterize-quasi-coherent (06WI), lemma-quasi-coherent (06WK), lemma-qc-colimits (06WN), and lemma-quasi-coherent-algebraic-stack (06WV), including the warning that the big-fppf inclusion need not be left exact. I read stacks-cohomology.tex, lemma-quasi-coherent-check-exact (0GQF), including its common-refinement proof. I also read descent.tex, proposition-equivalence-quasi-coherent (03DX), lemma-equivalence-quasi-coherent-limits (06VE), especially the distinction between parts (5) and (6); sites-modules.tex, lemma-abelian (03DA), lemma-abelian-abelian (03CN), and lemma-exactness-pushforward-pullback; schemes.tex, lemma-kernel-cokernel-quasi-coherent (01IC); and stacks-properties.tex, section-properties-morphisms (04XB), for the representable-flat convention. There are no new-node sources to audit.

Step 1 uses def-trf-space-quasi-coherent-module's actual explicit local-presentation definition. The identity presentation proves the structure-module clause. The passage from every scheme slice back to the original site is the same covering and presentation at its terminal object; it is a direct definition check, not an uncited descent theorem.

Step 2 uses the full statement of lem-sfb-stack-quasi-coherent-scheme-restriction to identify both input slice modules; lem-sfb-localized-site-tensor-restriction gives the tensor comparison for arbitrary sheaves, so it does not assume that the output is already quasi-coherent. The big-fppf scheme equivalence identifies that tensor with the extension of the scheme tensor, and lem-weil-pbc-quasi-coherent-tensor-product-affine-sections explicitly gives scheme tensor closure. All schemes and modules are arbitrary; no finiteness enters.

Step 3 uses lem-sfb-fibred-fppf-ringed-inverse-image's explicit ambient-cokernel preservation for precomposition. The big-fppf comparison explicitly preserves ambient cokernels, and the scheme cokernel/image theorem explicitly makes that cokernel quasi-coherent. Together with the scheme-restriction statement, these supply the claimed slice formula for the actual ambient quotient map, not merely an abstract isomorphic object. The full-subcategory universal property gives the quasi-coherent cokernel without a kernel assertion.

Step 4 uses lem-trf-scheme-zariski-etale-quasi-coherent-equivalence for full faithfulness, and lem-sfb-scheme-etale-module-exact-finiteness-comparison for exactness into the ambient small-etale module category. That exactness statement is about short exact sequences, so I explicitly factor the map through its quasi-coherent image and use its quasi-coherent kernel, citing both scheme closure nodes. This verifies ambient-cokernel preservation without confusing an equivalence of full subcategories with exactness of an inclusion.

Step 5 uses lem-weil-pbc-module-sheaves-colimits-forgetful for the common underlying abelian cokernel and lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective for its local section lifts. These apply to the big fppf site and the small etale sites with the stipulated small-skeleton/universe convention. The remaining cancellation argument is written out: the ambient cokernel lies in the full quasi-coherent subcategory by step 3, and a zero cokernel projection that is epi forces its target to be zero. No categorical epi of rings is used.

Step 6 uses the algebraic-stack definition for representable diagonal; def-trf-scheme-algebraic-space lets the representable-diagonal theorem apply with scheme sources. I read that theorem's statement: it explicitly says that T times_X U_i is an algebraic space, and does not supply flatness or surjectivity. Those come from the item's hypotheses, with flatness interpreted on scheme-base-change charts as in 04XB. The definition of algebraic space supplies a representable surjective etale scheme atlas. The field-extension lift argument supplies joint surjectivity on the scheme T. Thus no lemma assuming an fpqc or fppf covering is applied to the arbitrary flat family. The final pullback identification is exactly the natural cartesian comparison in lem-sfb-stack-quasi-coherent-scheme-restriction; the isomorphism in the 2-fibre product is retained. The source 0GQF uses the letter V in this paragraph after naming its atlas U; the draft consistently fixes one test T and does not repeat that harmless variable slip.

Step 7 uses lem-sc-flat-cover-module-isomorphism-reflection exactly as stated: arbitrary scheme modules, a pointwise jointly surjective flat family, and isomorphisms after pullback. It has no quasi-compactness hypothesis. The other citation gives F(x)=Gamma(T,F_x) and natural cartesian comparisons. Once every scheme-test map is invertible, inverse components assemble by the original naturality equation, with no descent assertion left unstated.

Steps 8 and 9 are elementary consequences of the preceding proved steps. For faithfulness, a zero restriction makes each cokernel quotient an isomorphism; conservativity then cancels that quotient. For epimorphisms the same argument tests 0 to C. I checked both directions and distinguished sectionwise surjectivity from sheaf local surjectivity. Preservation of epimorphisms by the individual flat tests follows from the cokernel formula for every scheme test, so it does not require the family to be jointly surjective.

I checked all step citations against the actual existing statements and wrote the 22 verbatim quote records. I also followed their dependency lists and found no path back to the item. The off-unit uses are general site/scheme tools and are declared in split_report.tool_uses with their roles; they replace no unit step. Every step is shorter than 2000 characters (the longest is 1073), and the final two categorical arguments are written as steps rather than new nodes. There is no relabelled clause or proof moved into a new node.

Edge cases: a zero source or target and the identity map give the expected cokernels; an empty atlas can be jointly surjective only on an empty stack, where all tests and module sheaves are trivial. An individual empty flat test preserves epis but need not be faithful, and the proof asserts faithfulness only for the whole jointly surjective family. Infinite families and modules with infinitely many generators never introduce a finite-product or quasi-compactness condition. A nonflat test Spec(F_2) over Spec(Z) kills the injectivity of multiplication by 2 in the big-site comparison (06VE(6)); no step transports that kernel. I also checked a nonreduced affine base: the cokernel of multiplication by a nilpotent remains the ordinary quotient and the argument imposes no reducedness hypothesis.

Corrections during self-review: I added the scheme kernel theorem to justify the short-exact factorization in step 4 and corrected the abelian-sheaf source tag to 03CN. No statement repair or STATEMENT-DISPUTED issue was needed.

## Unfinished work

None in the split. The required server dry run passed; final direct delivery follows.

## Validation

The server review_split check passed with zero new nodes and the declared tool uses. Its informational note says that the inherited unit has no realization recorded; this item is not the unit's key node and does not modify the unit record.

Required deliver.py --no-push finished successfully: OK (not pushed), preflight passed, dry-run commit faf2a19dc98. The next invocation is the authorized direct push.
