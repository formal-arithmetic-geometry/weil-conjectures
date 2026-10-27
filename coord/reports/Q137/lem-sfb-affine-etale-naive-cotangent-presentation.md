# Stage-1 delivery: lem-sfb-affine-etale-naive-cotangent-presentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-etale-naive-cotangent-presentation.json: item, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-naive-cotangent-etale-comparison.json: statement-only unsplit lemma, Stacks 0D0X; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-zariski-naive-cotangent-affine-comparison.json: statement-only unsplit lemma, Stacks 0D0I on whole affines and the canonical ring presentation; no Mathlib match.
- citations.json: every item-step use has a verbatim statement quote.
- searches.jsonl and research-results.json: actual logged searches and full returned results. research.py and write_split.py are sandbox-only working scripts.

Two new nodes, zero Mathlib leaves. The new nodes contain no proof or hidden proof sketch. The assembly proof has 1822 characters, with individual steps of 728, 629 and 465 characters.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for naive cotangent, NL, etale cotangent and presentation terminology. The hits in ring-theory localization modules and algebraic-geometry smoothness modules do not supply a derived small-etale sheaf comparison. A Mathlib ring cotangent map is not an attachment.

## Wanted literature

None. All sources used were available under literature/stacks-project/ and read locally.

## Corrections and scope

The item statement, its hypotheses and all maintainer-owned metadata are unchanged. There was no earlier sandbox split or report, and no repair-note file for this item. The empty proof was replaced by the three-step assembly, retaining the original Mathlib searches and adding the new actual Q137 searches. No Lean files, compiler, build tool, shared-repository writes or git commands were used.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor explicitly returns None. Its precise from.place and full via chain are retained. New nodes extend that chain with this item. I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the unit and chapter records. This comparison remains a supporting deformation-theory input to that inherited route. Searches across the whole blueprint for cotangent, naive, affine cotangent, polynomial, Zariski and the source tags found no equivalent blueprint node.

The printed 0D0I statement writes Spec(R) = V subset S after introducing f:X to Y; this is a harmless naming typo. The new node specializes to X=Spec B and Y=Spec R and introduces every object explicitly. No disputed mathematical assertion or change to the item is needed.

## Mathlib searches and inspected candidates

For each of the item and both proposed nodes I ran msearch.py with two distinct LeanFinder phrasings, Loogle, source grep and LeanSearch. All returned successfully; the exact query strings and full outputs are in each node's mathlib_searches and research-results.json, and the official script logged them to searches.jsonl. I read all hits, then inspected Mathlib/RingTheory/Extension/Cotangent/Basic.lean (cotangentComplex is a module map and its H1 is a kernel, not either sheaf comparison) and Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean (ordinary presheaf differentials). Other hits were algebra localization equivalences, formally etale differentials, topology refinement, or sheafification functors. None is an exact match or a one-line specialization for a derived naive cotangent object on a scheme site.

## Not duplicates

lem-sfb-scheme-naive-cotangent-etale-comparison vs lem-sfb-affine-etale-naive-cotangent-presentation: the new node compares two topologies for every scheme morphism; it neither chooses an affine presentation nor identifies the result with a ring presentation complex. The item additionally assembles the ring-presentation and affine-sheaf comparisons.

lem-sfb-zariski-naive-cotangent-affine-comparison vs lem-sfb-affine-etale-naive-cotangent-presentation: the new node is only the standard ring-to-Zariski-sheaf quasi-isomorphism on affine schemes; it has no etale comparison and no arbitrary-presentation conclusion.

lem-sfb-zariski-naive-cotangent-affine-comparison vs lem-sfb-noetherian-scheme-cotangent-truncation: the existing node requires locally finitely presented maps between locally Noetherian schemes and concerns the full cotangent truncation, coherence and Ext; it does not imply the arbitrary-ring affine comparison.

lem-sfb-zariski-naive-cotangent-affine-comparison vs lem-sfb-scheme-square-zero-lift-torsor: the existing node classifies marked square-zero scheme lifts and their automorphisms; its source mentions the affine comparison but its statement does not state it.

The full-DAG searches also found lem-weil-pbc-nl-presentations-homotopy-equivalent (00S1), which is reused; lem-trf-lci-naive-cotangent-model and its comparison data (full ring cotangent truncation), which do not compare sheaf sites; and lem-sfb-sheaf-polynomial-cotangent-comparison (presentations of fixed sheaf rings on one site), which does not identify an affine ring complex with the scheme-site complex. The existing lem-sfb-derived-etale-zariski-equivalence gives exactness of topology change, not compatibility with naive cotangent objects. It is reused for exactly that exactness. No elementary claim was made into a node, and neither new node is a clause or restatement of the item.

## Review by Q137

I read Stacks spaces-more-morphisms.tex lemma-NL-compare-spaces-schemes (0D0X) and its proof, more-morphisms.tex lemma-NL-affine (0D0I) and definition-netherlander, algebra.tex section-netherlander and lemma-NL-homotopy (00S1), descent.tex proposition-equivalence-quasi-coherent (03DX), and spaces-perfect.tex lemma-epsilon-flat (08H8). These are the sources for the item and the two new nodes. The two new statements assert derived isomorphisms, not just per-degree identifications. Their Zariski complexes are defined inline using the existing general sheaf polynomial-comparison node: A=f inverse O and B=O; this introduces the actual objects without creating another definition node or hiding construction data.

In step 1, the existing presentation-homotopy node explicitly gives chain maps and both homotopies for arbitrary polynomial sets over the same R and quotient B. Apply it to P and R[x_b]. The maps induced on cohomology are inverse because dh+hd is a boundary on a cycle; this elementary calculation is written in the step. The cited affine-realization node explicitly says a_B is exact and induces a functor on the derived category. Thus its application to this quasi-isomorphism is justified. No formal smoothness or finite-presentation hypothesis was borrowed from the Mathlib hits.

In step 2, the new 0D0I node supplies exactly the whole-affine Zariski quasi-isomorphism with the canonical ring presentation, with the same degrees and differential as step 1. The existing derived-etale-Zariski-equivalence statement explicitly says epsilon tensor pullback is exact on all modules, so it applies to this complex without requiring its conormal module to be flat. The existing scheme-Zariski-etale-quasi-coherent-equivalence statement identifies its forward functor with that tensor pullback and gives its formula F_et. Associated module sheaves are quasi-coherent by the definition used in the item. The naturality in module maps identifies the differential, not merely the two terms. These cited statements were opened and read; the full statements in citations.json make the particular clauses inspectable.

In step 3, the new 0D0X node applies to the schemes U and V over the S already in the item. It compares their representable-space naive complex with the pullback of precisely the Zariski complex used in step 2. Inverting the three already obtained isomorphisms gives the stated direction NL to the associated arbitrary-presentation complex. This step assumes neither a cartesian chart square nor etaleness of U to V, nor finite generation of T or I. The base S is explicit in the new comparison statement.

I checked zero rings/empty spectra (all relevant sheaves then vanish), the empty-variable presentation R to R (both terms zero), a surjection R to R/J with no variables (the model is [J/J² to 0]), polynomial B over R with I=0, and B=k[e]/(e²). In characteristic two the last differential sends [e²] to 2e de=0, so negative cohomology survives; the proof never replaces NL by differentials alone. Infinite T is allowed by 00S1 and by the canonical ring presentation on all elements of B. For the new general scheme comparison, identity morphisms give zero, and nonaffine/nonseparated schemes require no extra hypothesis in 0D0X. Each fact with content in the assembly is a cited node, and its statement gives what is taken from it. Every step is below 2000 characters; no long comparison is proved inline.

Two off-unit generic tool uses are declared in split_report.tool_uses: the existing ring homotopy equivalence and the existing module-level Zariski-etale equivalence. They are foundations used by this route; they do not replace any unit step. The same-unit exactness and affine-realization nodes are also reused. No SGA source is cited.

## Unfinished work

The two new prerequisites are intentionally statement-only unsplit nodes for later stage-1 work. Nothing in the assigned one-level split remains unfinished. Required server dry run and push are performed after writing this report.
