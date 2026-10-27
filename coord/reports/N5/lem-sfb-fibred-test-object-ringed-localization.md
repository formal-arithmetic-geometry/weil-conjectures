# Stage-1 delivery: lem-sfb-fibred-test-object-ringed-localization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibred-test-object-ringed-localization.json: item, statement; seven elementary proof steps, status split; no Mathlib match.
- citations.json: twelve verbatim statement excerpts, one per cited node per step.
- report.md: this report. searches.jsonl is the unmodified search-command log. write_split.py is a sandbox-only preparation script, not a project change.

New nodes: 0. New Mathlib leaves: 0. The universal property needed for the categorical argument is already written explicitly in the existing definition of a category fibred in groupoids. Turning its immediate consequences into fresh lemmas would violate the elementary-node rule.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, fibred/fibered and localization notions. The ringed-space K-flat direct-image localization declarations concern derived adjunctions on ringed spaces and do not state this result. No exact completed project declaration was found.

## WANTED

None. All sources used are available locally.

## Corrections and scope

The item had no proof. Its statement, statement dependencies, existing searches, creation record, chapter, unit, and blueprint lineage are retained. No statement dispute or additional hypothesis was necessary. In particular this is an equivalence with the BIG site of U, not the small etale site; the module is arbitrary and need not be quasi-coherent or cartesian.

Read the chapter/unit records and the current literature/blueprint/latest chapter, sk-thm-sf-ctf-stability and its sk-thm-sf-ctf-stability-direct-images.proof.md (blueprint id det-thm-sf-ctf-stability-direct-images), especially (3). This is the local ringed-site supporting input to the already specified stack cohomology route, not a replacement of a unit-level argument. The ancestor command returns None on this inherited lineage; the null from.node is retained and the inherited from.place remains specific. No unit record is changed because this is not its key node.

Blueprint searches for fibred, ringed site and localizing, and DAG searches for Tags 06W0, 06W9 and the localizing label, found no replacement for the whole item. The existing lem-sfb-fibred-big-etale-restriction-calculus concerns restriction to the SMALL etale site and tensor-pullback comparisons, and lem-sfb-stack-quasi-coherent-scheme-restriction concerns quasi-coherent Zariski realizations. Neither is a substitute here, and neither is used in this proof.

## Not duplicates

No new nodes, hence no new/existing pairs. Existing tag hits were read: the item itself, its parent lem-sfb-stack-lqc-lfp-topology-comparison, the small-etale restriction calculus and quasi-coherent scheme restriction described above.

## Mathlib searches

Retained the item's six inherited search records. Ran and read six further searches through the required msearch.py command, recorded verbatim from its searches.jsonl: leanfinder in two phrasings; loogle for "Fibered", "Over"; leansearch for the slice equivalence of a groupoid fibration; and two grep queries in FiberedCategory. All six services/commands returned successfully. Read Mathlib/CategoryTheory/FiberedCategory/Fibered.lean (definitions and pullback lifts) and HasFibers.lean (chosen fibre equivalence). HasFibers.instIsEquivalenceFibFiberInducedFunctor identifies a chosen fibre with the standard fibre over one base object. Over.iteratedSliceEquiv identifies an iterated ordinary slice with a slice in the same category. Neither states the groupoid-fibration slice equivalence or its ringed-site and module conclusions. The other hits concern equifibered natural transformations, ordinary scheme modules, or ordinary site localization. Thus the entire item is not a one-line Mathlib specialization. No unavailable service was recorded as absence.

## Review by N5

I read Stacks stacks-sheaves.tex, Tag 06W0 (lemma-localizing), its following definition-pullback, Tag 06W9 (lemma-localizing-structure-sheaf), and the following module-restriction paragraph. Tag 06W0 refers to stacks.tex Tag 0CN0 (lemma-localizing), whose proof uses precisely the fibred-groupoid definition and inherited coverings. I read that proof too. Tag 06W9 identifies the structure sheaves directly from their construction. The item's two topologies are among those allowed by both tags. Neither source needs a stack, representability, flatness of the module, or quasi-coherence. The proof expands these definition-level verifications rather than introducing a lemma restating one of the item's conclusions.

Step 1 cites def-sfb-stable-pointed-moduli-groupoids. I checked its actual statement: beyond its moduli examples, it explicitly defines a GENERAL category fibred in groupoids by lift existence and the unique c with ac=b over a given v. Apply that clause with the target arrow w -> x to obtain exactly the Hom bijection needed. Applying it twice over an identity base map gives inverse isomorphisms of two lifts; this does not assume the fibre groupoid has trivial automorphisms before slicing.

Step 2 uses that same universal property, plus def-weil-size-convention for small choices. Lifts give the object assignment of Q_x. Identity, composition, the counit and its naturality all follow from the uniqueness just checked. I wrote these checks out, including the normalization at id_U. This is an explicit inverse, not an uncited invocation of an equivalence theorem.

Step 3 cites def-pur-localized-ringed-site, whose statement says a family over x covers iff it covers in the original category. Combined with the topology GIVEN in the item, this is precisely the scheme covering condition on either side. This works over every slice object, so the argument is not confined to covers of the terminal object. The functor Q_x keeps the underlying scheme maps. No separate etale/fppf comparison theorem is used.

Step 4 cites def-pur-localized-ringed-site and def-sfb-stack-quasi-coherent-algebra. The former gives the restricted ring sheaf sectionwise, and the latter explicitly says the value over T is Gamma(T,O_T) with regular-function pullback along the underlying map. These are exactly the asserted rings AND their restrictions. The identity comparison is a ring isomorphism without any flatness requirement.

Step 5 cites the localized-site and module definitions. I checked that the first gives N(z -> x)=M(z) with its original action, while the second says restriction is semilinear over the ring restriction. Thus precomposition by Q_x has exactly the claimed sections, maps and actions. This also matches definition-pullback in the source; it is not the generally different tensor pullback on a small etale site.

Step 6 cites def-weil-pbc-sites-and-cohomology for the sheaf equalizer criterion and def-weil-sheaf-of-modules-category for the module category and its morphisms. The overlap comparison is justified in the step by the Hom bijections and the defining universal property of fibre products, so no finite-limit-preservation theorem is concealed. The equalizer diagram is the diagram of N on the lifted cover. The reverse construction and inverse module isomorphisms are the same explicit precompositions and the counit from step 2. This uses the statements of the cited definitions, not a theorem hidden in their proofs.

Step 7 cites the localized-site definition for the composition functor and relocalization, and the fibred-groupoid definition for the unique comparison between the two lifts. I checked the directions: h goes from u^*x' to (fu)^*x, so contravariance gives M(h): M((fu)^*x) -> M(u^*x'). Both h and its inverse lie over id_T, hence the maps are Gamma(T,O_T)-linear. Naturality and the cocycle condition reduce to equality of two arrows with the same base and same composite into x; exactly the uniqueness already cited proves them. This is compatibility with further BIG-site restriction for arbitrary a, not an assertion that a small-etale tensor comparison is always invertible.

For small cases, p=id on schemes gives ordinary relocalization; at the terminal slice object the normalization gives exactly id_x and id_U. On the empty scheme the ring is the zero ring and all formulas still make sense, including an empty covering when allowed. For the constant groupoid fibration with a nontrivial automorphism group G, arrows from (T,g) to (T,h) over id_T in the slice are uniquely h^{-1}g: the automorphisms of an object of C do not contradict full faithfulness of p_x. An arbitrary noncartesian module is evaluated with its own restriction maps; no map between values on two DIFFERENT schemes is inverted. Only maps induced by slice isomorphisms over the SAME scheme are inverted. Identity and composable restrictions were checked by uniqueness as above.

B1-B9: no new nodes, no hidden proof sketches in new statements, no unrun searches, and no claimed Mathlib leaf. C1-C4: each use is from the cited statement and the only arguments left inline are the explicit universal-property and sectionwise calculations just described. C5-C8: existing DAG/blueprint/tag searches were read; no new edges through another theorem, no cycle or off-unit proof tool. D1-D5: no renamed clauses and no content moved to a new node; the proof itself constructs the equivalence and the comparisons. E1-E6: no extra geometric or module hypotheses, both topologies are in the source, the base scheme and ring maps are the actual ones, and the restriction compatibility is written explicitly. All steps are shorter than 1000 characters, so no long-step hidden-lemma issue arises. I corrected an initial citation excerpt at a line break to an exact substring and separately quoted the covering/relocalization clauses where those are used; all twelve entries in citations.json now match verbatim.

## Unfinished work

No mathematical part remains in this one-level split. There are no new unsplit nodes. Independent maintainer review remains part of the normal delivery process.
