# Stage-1 report: lem-trf-continuous-cocontinuous-derived-shriek

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-continuous-cocontinuous-derived-shriek.json`: item, statement unchanged, split into eight proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-partially-defined-module-adjoint.json`: statement; no Mathlib match for the epimorphic-generating-class extension criterion (Stacks 0793).
- `dag/nodes/sec-trace-formula/lem-trf-unbounded-left-derived-criterion.json`: statement; no Mathlib match for the five-hypothesis unbounded existence criterion (Stacks 0794).
- `dag/nodes/sec-trace-formula/lem-trf-module-pullback-injective-section-acyclic.json`: statement; no Mathlib match for pulled-back injective module acyclicity (Stacks 0D6X).
- `dag/nodes/sec-trace-formula/lem-trf-acyclic-coproduct-ext-orthogonal-hom.json`: statement; no Mathlib match for the bounded-above Hom-acyclicity consequence of the hyper-Ext spectral sequence (Stacks 07AA).

`citations.json` contains a verbatim statement quotation for each of the item's 21 step/node citations. The Mathlib queries and their actual digests are in `searches.jsonl`, with the complete printed answers in the twenty `*-search-*.txt` files. These supporting files and the sandbox-only writing script are not additional DAG nodes.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, cocontinuity, and derived lower shriek. The project has geometric open-immersion/compactification operations and ordinary site functors, but no declaration stating all clauses of this arbitrary-ringed-site unbounded theorem. The upstream master is reference material, not evidence of a finished proof.

## Literature wanted

WANTED: none. All source material used is available in the shared repository's Stacks sources.

## Findings and corrections

The item arrived unsplit and with no proof steps. Its statement correctly refines Stacks 07AC by specifying everywhere-definedness, triangulatedness and the normalized derived adjunction. I retained the statement, all original searches and source metadata, and its full blueprint ancestry. The item is a generic homological input below the derived-colimit/bar branch, not the key statement of the curve-zero unit; neither unit nor chapter records need editing.

Two tempting citations were insufficient. `lem-trf-site-pullback-injective-evaluation-acyclic` is about injectives of abelian sheaves, whereas the proof needs injectives in a module category over an arbitrary ring sheaf. The underlying abelian sheaf of such an injective need not be injective. I therefore created the module version instead of applying that node. Likewise `lem-pc-inverse-image-module-functor-exact` concerns topological spaces; it does not prove exactness for our site functor. Step 1 supplies the short local-lifting argument using cocontinuity and the existing general-site epimorphism criterion.

The bounded-above hyper-Ext node already present, `lem-per-bounded-above-rhom-hyperext`, concerns internal Hom sheaves and the cohomology sheaves of the second argument. The required calculation is instead ordinary global Hom, with Ext of the terms of the first argument. Its hypotheses and spectral sequence are different; I did not use it for this argument.

No statement dispute was found. No Lean was written or compiled. The four new nodes have statements only, empty proofs and empty proof dependencies; none restates the derived-shriek theorem or makes its proof a single application of a renamed clause.

## What remains

The assigned one-level split is complete. The four new prerequisites remain unsplit for their own stage-1 workers. Their proofs are not hidden inside their statements. The present delivery does not claim that the downstream DAG is finished.

## Not duplicates

lem-trf-module-pullback-injective-section-acyclic vs lem-trf-site-pullback-injective-evaluation-acyclic: the new statement applies to injective modules over any commutative ring sheaf and computes Ext against the corresponding free module sheaves; the existing statement only assumes an injective abelian sheaf. The latter cannot be applied to an arbitrary module injective after forgetting its coefficients.

lem-trf-acyclic-coproduct-ext-orthogonal-hom vs lem-per-bounded-above-rhom-hyperext: the new node concerns global Hom from an acyclic bounded-above complex of sums of objects whose positive Ext into one module vanishes; the existing node gives an internal-Hom sheaf spectral sequence from cohomology of a bounded-below second argument. It does not state the required termwise Ext calculation.

## Mathlib search assessment

For every new id I ran LeanFinder twice with different phrasings, Loogle, the required source grep, and LeanSearch through `msearch.py`. All twenty searches returned normally; no service failure was recorded as absence. I read the actual hits. I also checked the relevant source interfaces: `CategoryTheory/Adjunction/PartialAdjoint.lean` (the domain of a partial adjoint and closure under colimits), `CategoryTheory/Adjunction/Lifting/Left.lean` (two full adjunctions with a regular-epimorphic counit), `CategoryTheory/Functor/Derived/LeftDerived.lean` (universal construction assuming existence), `PointwiseLeftDerived.lean` (existence from supplied pointwise values or inversion), `Derived/Adjunction.lean` (extra composite-derived hypotheses), `CategoryTheory/Sites/PreservesLocallyBijective.lean` (ordinary local lifting), and `Algebra/Homology/HomotopyCategory/KInjective.lean` (orthogonality to all acyclic complexes).

These interfaces are relevant ingredients, but none is an exact match or a one-line specialization of a new statement. In particular, knowing how to assemble a partial adjoint after representability for every object is established does not itself extend representability from an epimorphic generating class; and a K-injective condition is stronger than the termwise Ext-orthogonality assumption. No new Mathlib leaf is claimed. The item retains its previously recorded searches; its site-specific unbounded assertion is not supplied by ordinary sheaf adjunctions.

## Review by Q69

I read Stacks `sites-cohomology.tex`, lemma-existence-derived-lower-shriek (07AC), in full, including the warning that the inverse image of an injective need not be injective. I read `sites-modules.tex`, lemma-lower-shriek-modules (0797), and its representing-Hom calculation. For the new nodes I read `homology.tex`, lemma-partially-defined-adjoint (0793), `derived.tex`, proposition-left-derived-exists (0794), `sites-cohomology.tex`, lemma-pullback-injective-pre-limp (0D6X), and example-hom-complex-into-sheaf (07AA). I checked the tags against `stacks-project/tags/tags`. For the final clauses I read derived.tex Proposition 05SE and Lemmas 0FND, 0DVC and 09T5. I also read the unit and chapter records, the current blueprint ancestor, and the retained created-item ancestry before writing the proof.

In step 1 the module-category statement explicitly identifies kernels sectionwise and cokernels by abelian sheafification. This lets the cited abelian-sheaf local-epimorphism theorem be used on the underlying sheaves. I wrote the actual cover refinement and restriction of a lift, so the exactness claim does not assume that direct precomposition always preserves epimorphisms. The identity ring map is essential for identifying module pullback with inverse image.

In step 2 I checked that the free-presheaf Yoneda node supplies the evaluation bijection with its actual basis-vector formula, and that module sheafification supplies the factorization into a sheaf. The ringed-site K-injective existence node explicitly states the Grothendieck property and all small colimits, which is the only part of it used here. The epimorphism from the sum indexed by sections is written out, including its indexing universe; no finite-generation or point assumption is made.

Step 3 applies 0793 to the whole class of small sums, not just single free generators. The representing object is the corresponding sum on the target, so every hypothesis of the new partial-adjoint node is met. The cited left-adjoint theorem explicitly supplies preservation of every small colimit, including finite and sequential ones. Right exactness is finite-colimit preservation. Additivity follows from the stated Hom bijections and additivity of the right adjoint; it is not assumed without argument.

Step 4 uses exactly the new module-injective node's positive Ext assertion, with its ring and free representing object matching those from step 2. Step 5 uses exactly the Hom-acyclicity conclusion of the new Ext-orthogonal-sums node, checking bounded-aboveness, acyclicity and the form of every term. The adjunction intertwines the Hom differentials by naturality, not just the degreewise groups. I expanded detection of acyclicity by injectives: the Grothendieck and enough-injectives nodes supply an embedding of a nonzero cohomology object, and the definition of injectivity extends it over the indicated quotient. This gives a nonzero Hom cohomology class, a contradiction. Thus no unmentioned derived-Hom comparison is needed.

Step 6 checks all five hypotheses of 0794 separately. The acyclicity test remains bounded above, whereas its conclusion is genuinely unbounded; I did not interchange these two assertions. The assembly node states that pointwise essentially constant systems assemble into the derived functor and canonical comparison, precisely what is taken from it. Step 7 uses the two homotopy/localization statements for the actual abelian module categories, writes the cone matrix calculation, and applies the exactness theorem only after establishing Situation 05S8 and everywhere-definedness.

For step 8 I checked the full statement of `lem-pc-pre-derived-adjoint-functors-general`. It includes the representative formula, not just existence of some adjunction. Exactness of inverse image gives the right-derived ind-cocone with invertible legs; the identity denominator has identity cocone map. Taking both denominators to be identities in the cited formula gives the required image of Q(f) composed with the left-derived comparison, in the correct direction. The ordinary adjunction's transpose is f-flat, as required by the item. This proves the normalization for every chain map, without assuming it is a quasi-isomorphism.

I checked the B--E return categories against the actual files. Each new statement introduces all its objects and defines Ext/Hom in the convention it uses. Every step citation has a verbatim quote in `citations.json`; sources have tags and labels. The new prerequisites are strictly smaller inputs, and elementary generator/local-lifting arguments stay in the item. Generic off-unit statements are declared in `split_report.tool_uses`, rather than replacing the unit route. Small-case checks include the zero module and empty coproduct, an empty site, identity site functors, a point site with a non-field ring, bounded-above complexes with arbitrarily long left tails, and the distinction between the finite-diagonal bounded-above test and the final unbounded theorem. No step needs enough projectives, exactness of g-shriek, points, constant coefficients, or injectivity of the pulled-back module. All steps are below 2000 characters; the auxiliary Hom comparison has its own node instead of being hidden in a long step.

On resumption on 2026-10-19, I retained the earlier split and search records and first ran the required delivery dry run; it passed at 6d607c9bff. I compared every sandbox node with the current shared DAG: the item is still unsplit there, its statement and statement dependencies are unchanged, and all four child ids are still new. I reread 07AC, 0797, 0793, 0794, 0D6X, 07AA and the derived-adjunction sources above, and checked the cited statements against the current DAG. All 21 quotations still occur verbatim and cover exactly all step citations; the longest step is 1149 characters. A fresh whole-DAG tag scan found only the existing abelian-sheaf specialization for 0D6X, already distinguished under Not duplicates. The saved Mathlib results and the partial-adjoint, adjoint-lifting, pointwise-derived and K-injective source interfaces still support the recorded no-match assessments. I found no mathematical repair necessary. This resumption changed only this report and preserved all searches and proof steps.
