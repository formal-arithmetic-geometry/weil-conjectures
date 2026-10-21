# Stage-1 re-split: lem-sfb-module-upper-star-kflat-quasi-iso

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-module-upper-star-kflat-quasi-iso.json: statement unchanged; four-step assembly, 1594 characters of proof text.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-homology-quasi-iso.json: new statement-only lemma; verified Mathlib leaf, with no proof steps or proof dependencies.
- citations.json: literal statement text for every citation of every item step.
- report.md and command-generated searches.jsonl: review and actual search evidence. write_split.py is sandbox scratch work only.

One new node, one Mathlib leaf. The new statement explicitly retains the kernel/cokernel comparison, its naturality, and the conjugation formula. The ambient abelian-category argument and the exactness argument remain in the assembly through existing nodes; none of their work is silently dropped.

## Attachments

None. I searched the live WeilConjectures source for the item tag and name and read UpperLowerStar.lean, including the module docstring and lines 166-186. AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar at line 183 has a sorry-free body, but it uses the sorried preservesKFlatComplexes_mapMod_upperStar instance at line 175 and sorried scalar-extension input. The node's current rests_on_sorry audit agrees. This is not a finished attachment. All exposed open declarations already have DAG nodes. The Lean and DAG statements agree about arbitrary scheme morphisms, arbitrary commutative condensed coefficients, and preservation of quasi-isomorphisms between K-flat complexes. The natural-language proof follows the blueprint's exactness route, which does not need preservation of K-flat objects themselves.

No new project declaration states the general local short-complex criterion. Project occurrences of PreservesLeftHomologyOf concern particular affine-section, evaluation, or module-comparison functors; none is the new lemma with its general additive functor and two local kernel/cokernel hypotheses.

## WANTED

None.

## What was wrong and what changed

This is the deliberate human re-split of 2026-10-21, not a claim that the already reviewed live item is stale. The live copy already contains Q41's four-step repair and has a shorter proof than the 3974-character proof named in the handoff. I used that live copy, retained its statement, prior searches, metadata, and source citations, and added a real separately stated node rather than just shortening its proof again.

The extracted argument was found in Mathlib. The standing rule to mark an exact verified match mathlib applies: leaving it unsplit would create fake unfinished proof work. The new node is therefore statement-only with status mathlib. Its scope is genuinely local: F need not be exact globally. Existing global exact-functor nodes do not state this result with these weaker hypotheses. This is neither a renamed clause about the scheme pullback nor a duplicate copy of its exactness proposition. The proof still uses the existing exactness proposition, so the unit's route is unchanged.

The former third and fourth steps' comparison/naturality/inversion argument appears explicitly in the new statement. The item's step 3 now checks its local hypotheses on the two degree-n short complexes and invokes it; step 4 makes the degreewise and K-flat restriction. The old first two steps are retained verbatim. No statement dispute and no change to the coefficient category, scheme hypotheses, or target.

The existing cohomology leaf lem-weil-pbc-exact-functor-complex-cohomology records CategoryTheory.Functor.homologyFunctorIso, whereas the actual declaration is CategoryTheory.ShortComplex.homologyFunctorIso at Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:777. Its mathematical statement is correct; I leave its maintainer-owned metadata alone. The new leaf records the actual ShortComplex namespace and exact pinned lines instead.

## Source and search record

I read GOAL.md; the fixed chapter record sec-six-functors-basics; the unit sk-def-sfb-module-derived-pushpull, including its single proof step; the current main-20261015 item statement and proof; and the exactness proposition's source proof (Setting, Transport, Extension of scalars, Conclusion). The current unit specifically uses exactness of module pullback, so I retain that route, including the existing generic lifted-exactness and coefficient-isomorphism arguments beneath det-prop-sfb-module-pullback-exact-main.

For the new node I read Stacks homology.tex Tag 010N, label lemma-exact-functor, and the kernel/cokernel part of its proof. The source's global exactness hypothesis supplies all these diagrams; the new local formulation is the precise refinement in Mathlib, not a claim that Stacks states the stronger formulation verbatim. I also read derived.tex Tag 015F, label lemma-right-derived-exact-functor: its proof omits the details of quasi-isomorphism preservation. Those details here are the new explicit comparison/naturality statement and its verified Mathlib implementations. For ambient sheaves I checked sites-modules.tex Tags 03DA/lemma-abelian, 03EI/lemma-sheafification-exact, and 03EO/lemma-internal-hom-adjoint-tensor, alongside the cited abstract internal-module abelianness statement. I used no SGA.

Before creating the new id I searched the whole DAG for the tag, local left-homology preservation, two short complexes, and quasi-isomorphism preservation under kernel/cokernel preservation; I opened the relevant statement hits listed below. blueprint_refs.py ancestor identifies the item itself as nearest blueprint ancestor. Whole-blueprint searches for 'quasi-isomorphisms', 'preserves homology', 'short complex', and 'left homology' found no blueprint node with the new local statement. The new node's from.place names the precise middle/final clauses of the blueprint proof, and same_as is empty. A direct search found no pre-existing node with its new id.

All ten searches were run with the required msearch.py command and their results read. Five item searches include two semantic phrasings, Loogle, LeanSearch and grep. The five new-node searches likewise include two semantic phrasings, Loogle, LeanSearch and grep; their exact query texts are in the node and searches.jsonl. All services answered. The source read confirms PreservesLeftHomologyOf.mk' at line 303 converts preservation of one chosen kernel/cokernel datum to the class, mapHomologyIso at 455 gives the comparison, mapHomologyIso_hom_naturality at 616 gives the square, and quasiIso_map_of_preservesLeftHomology at 811 gives invertibility. The hypothesis in IsPreservedBy at lines 69-79 is exactly preservation of the kernel of the outgoing map and the cokernel of the induced incoming map into that kernel. Additivity ensures F preserves zero maps. Each clause has its own matching declaration; no mathematical identification is left to a future unproved bridge.

## Not duplicates

lem-sfb-local-homology-quasi-iso vs lem-sfb-kernel-cokernel-finite-exactness: the existing statement upgrades preservation of every kernel or every cokernel to preservation of finite limits or colimits; the new statement assumes preservation only for two specified kernel and two specified cokernel diagrams and concludes naturality and invertibility on their homology.

lem-sfb-local-homology-quasi-iso vs lem-sfb-preserving-colimits-additive: the existing statement deduces additivity from finite-colimit preservation; the new statement assumes additivity but no global colimit preservation and concerns homology of two short complexes.

lem-sfb-local-homology-quasi-iso vs lem-pc-single-degree-exact-term-hom-quasi-iso: the existing statement concerns internal Hom from a complex concentrated in one degree in a module-sheaf category; the new statement allows any additive functor between abelian categories with only the specified local preservation hypotheses.

lem-sfb-local-homology-quasi-iso vs lem-sp-exact-functor-half-plane: the existing statement transports limiting cycles and filtration comparisons of exact couples under a globally exact functor, with convergence and normalization hypotheses; the new statement has none of that structure and proves a local short-complex comparison without global exactness.

lem-sfb-local-homology-quasi-iso vs lem-sp-exact-functor-preserves-homology: the existing statement assumes the functor preserves all short exact sequences and gives global image/subquotient/homology comparisons; the new statement requires only the four specified diagrams to be preserved, so that global theorem cannot be applied under its hypotheses.

lem-sfb-local-homology-quasi-iso vs lem-weil-pbc-exact-functor-complex-cohomology: the existing statement requires preservation of every finite limit and finite colimit; the new local criterion does not assume that, and applies to short complexes individually rather than assuming global exactness.

lem-sfb-local-homology-quasi-iso vs lem-weil-pbc-abelian-presheaves-evaluation-exact: the existing statement establishes global exactness of evaluation on abelian presheaves, while the new statement allows arbitrary additive functors and local preservation on only two short complexes.

lem-sfb-local-homology-quasi-iso vs lem-weil-cohomology-commutes-scalar-extension: the existing statement is extension of scalars between fields and its tower coherence; the new statement has no fields, tensor products or global exactness assumptions and describes local kernel/cokernel preservation for arbitrary additive functors.

lem-sfb-local-homology-quasi-iso vs lem-weil-pbc-exact-functor-derived-factorization: the latter's first conclusion assumes a globally exact functor and then constructs its triangulated derived functor; neither that assumption nor that conclusion is present in the new local short-complex criterion.

lem-sfb-local-homology-quasi-iso vs det-prop-sfb-module-pullback-exact-main: the existing proposition establishes exactness of the specific pro-etale condensed-module pullback; the new general lemma does not establish any geometric functor's exactness and instead supplies the homological argument applied after it.

## Review by Q82

I checked the item against its current blueprint statement and the source proof, not just the node title. The coefficients are internal modules over p_Z^*Lambda in abelian-valued sheaves on the pro-etale site. They are not ordinary structure-sheaf modules. The arbitrary morphism f and arbitrary commutative condensed Lambda are retained. The unit's exactness route is followed; no finite-coefficient purity or other route is imported.

For step 1 I opened def-weil-pbc-proetale-site, lem-weil-pbc-sheaf-tensor-closed, and lem-sfb-modobj-abelian. The first supplies the small skeleton required by the sheaf statement. The second states abelianness, additivity of the sheaf tensor and preservation of all colimits by tensoring. In particular Lambda_Z tensor - preserves finite colimits, exactly the extra hypothesis in the third node's internal-module abelianness criterion. I take no unstated theorem from its proof, and do not confuse its abelianness conclusion with an assertion about derived functors.

For step 2 I read the entire statement of det-prop-sfb-module-pullback-exact-main: it has the same condensed Lambda and arbitrary f and spells out the same composite Ext_alpha after mapMod(f^*_Ab). It explicitly asserts additivity and preservation of finite limits and colimits. This supplies all four local diagrams needed in step 3. I also read its proof source and supporting lifted-exactness, alpha-isomorphism, ring-homomorphism and extension-along-iso statements to ensure none of the earlier factor arguments is lost: they remain beneath this existing exactness node. Creating those arguments again would duplicate existing nodes.

For step 3 I verified the new leaf statement against each actual Mathlib declaration. Its u-bar really has source V-minus and target ker(v); q is its cokernel, rather than an arbitrary quotient. The chosen-kernel/cokernel hypothesis is converted by mk', which is important: preservation of some objectwise isomorphism alone would not give naturality. I checked the naturality direction against line 616 and solved it for H(Fa) by composing with c_T inverse on the left. In each degree of s:P->P', the short complexes have H(S)=H^n(P), H(T)=H^n(P') and H(a)=H^n(s), precisely as defined by def-weil-abstract-derived-category. The target homology exists because step 1 established abelianness. Exactness in step 2 preserves both the outgoing kernel forks and the cokernel coforks of the induced incoming maps. Thus the local hypotheses are verified, with no assumption that f is flat. The new lemma, rather than an uncited argument about inverses, supplies the comparison and invertibility.

For step 4 I reread the quasi-isomorphism definition in def-weil-abstract-derived-category. Applying it to invertibility in every integer degree is elementary, as is restricting the universal conclusion to K-flat source and target. Neither boundedness nor preservation of K-flat objects has been smuggled into the proof. All four steps are shorter than 2000 characters; the combined proof is below 3000 characters.

I tested the local statement with the identity and zero functors, zero short complexes, and a nonexact functor: F=- tensor_Z Z/2 on abelian groups preserves the required diagrams for short complexes 0->Z->0. It is not globally exact, as multiplication by 2 shows, so the weaker local hypotheses distinguish the new node from the existing global exactness statements. For the item I checked zero Lambda, empty source X, identity f, zero complexes and arbitrary unbounded complexes. All comparisons remain degreewise and no infinite totalization is used.

Against B-E, the new node is self-contained, has ordinary TeX, genuine recorded searches and exact source lines, empty proof/proof_deps, and valid blueprint ancestry. Its notions of short complex and the induced kernel/cokernel homology are defined inline. The parent statement is unchanged. Every non-elementary step cites the statement supplying its conclusion, and citations.json copies the literal statement for each use. There is no dependency from the new node back to the parent: blueprint ancestry is provenance only. I corrected the choice of an extracted global exact-functor lemma before writing: that would duplicate existing nodes; the delivered local criterion has strictly weaker hypotheses and a verified Mathlib match. No hypothetical searches, unverified attachments, proof sketches in unsplit nodes, or new axioms are used.

## What could not be finished

Nothing remains in the one-level split. The extracted local argument is already proved in Mathlib and is recorded accordingly; other existing dependencies retain their own states. No Lean was written and no compiler, Lake command or build was run. Required delivery validation follows below.
