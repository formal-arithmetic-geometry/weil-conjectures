## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-field-kernel-relation-immersion-closed.json: item, split into five steps; statement and statement dependencies unchanged.
- lem-sfb-field-groupoid-perfect-restriction.json: statement, unsplit; no exact Mathlib match. Perfect field replacement and restriction of the two groupoids, with homeomorphisms on arrows.
- lem-sfb-perfect-field-groupoid-image-closure.json: statement, unsplit; no exact Mathlib match. The reduced image closure over a perfect field is a groupoid; its inclusion preserves all operations.
- lem-sfb-field-groupoid-open-image-closed.json: statement, unsplit; no exact Mathlib match. The open-image lemma 04Q6, without assuming perfection or finite type.

citations.json gives a verbatim quotation for every step-use pair. research-results.json retains the actual search responses; searches.jsonl is the search command's own log.

Attachments: none. I searched the live WeilConjectures library by the exact blueprint tag and the groupoid/locally-closed-image notions. The small set of groupoid-related project files deals with descent orbits, invariant affine neighbourhoods, and constant group schemes, rather than 04Q9 or its three inputs. No exact sorry-free project declaration was found. Mathlib's ordinary CategoryTheory.Subgroupoid is not an internal groupoid in schemes.

WANTED: none.

## Sources and corrections

I read more-groupoids.tex, Situation 04Q5 (situation-morphism-groupoids-on-field), Lemma 04Q6 (lemma-open-image-is-closed), 04Q7 (lemma-map-groupoids-on-field-image), 04Q8 (lemma-map-groupoids-on-perfect-field-image), and both proof paragraphs of 04Q9 (lemma-locally-closed-image-is-closed). I also read 04LQ (lemma-restrict-groupoid-on-field), schemes.tex 0356 (lemma-map-into-reduction), and schemes.tex 01IQ (lemma-immersion-when-closed). No SGA source is used.

The original item is true as stated: absolute groupoids are groupoids over Spec Z, which is an allowed choice of S in 04Q5. The base V is identical in both groupoids and a is identity on objects; no hypothesis that s=t, or that the arrows are schemes over k in a single common way, has been added. The immersion consequence is an application of 01IQ.

### Source error

The final paragraph of the local Stacks 04Q9 proof says to apply the identity morphism on R1 to obtain (R2)_red and then writes a restriction from (R2)_red to Z. This has the wrong source: a has domain R1, so a map from (R2)_red to Z is not defined. For example take the trivial groupoid on Spec k mapping by the unit into the additive group scheme over k: R1=Spec k, R2=A1_k and Z={0}. Restricting a to R2-red is ill-typed. The intended source is (R1)_red. Step 2 explicitly applies 04Q8 to id_R1 and factors a composed with R1-red -> R1 through Z by 0356. The statement of the item is unchanged; this is a proof correction, not a weakened theorem.

## Blueprint and duplicate searches

I read the chapter and unit records, SETUP's three levels, and the current latest blueprint direct-images proof, paragraph (3). The inherited prerequisite chain reaches 088J's first paragraph through the alteration/moduli inputs; this item supplies exactly its cited 04Q9 input. No chapter or unit route is changed.

I searched the whole DAG by 04Q6, 04Q8, 04LQ, 01IQ, perfect closure, reduced-source factorization, locally closed images, and groupoid restriction/closure terminology. The existing 0356 factorization node and existing 01IQ Mathlib leaf are reused. The keyword hits concerning open restrictions of a groupoid restrict the OBJECT open subset; they do not assert that an open arrow image is closed or that a perfect-field reduced image closure is a groupoid. blueprint_refs.py search was run for groupoid, perfect, open image, 04Q6, 04Q8, 04LQ, and locally closed image. There is no same-statement blueprint node for any new input or for the item.

blueprint_refs.py ancestor returns None for the item. The inherited created.item chain ends at an upstream Lean-module-created node not represented as a DAG id. I preserve this computed null ancestor and the detailed existing blueprint.from.place, with the item prepended to via for new nodes. The report and split_report explicitly name the actual latest proof paragraph and source subargument; I did not fabricate a blueprint id or edit the ancestor's record.

## Mathlib searches

For each of the three new nodes, and afresh for the item, I ran the required msearch command with LeanFinder in two different phrasings, Loogle, grep, and LeanSearch. All responses in this run were available. All exact queries and returned text are in the delivered node records and the sandbox's research-results.json; the search command recorded them in searches.jsonl. The source was read for the potentially relevant hits: Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean:65 gives the affine spectrum homeomorphism after a purely inseparable scalar extension, not the construction/restriction of an internal scheme groupoid with two base maps. PerfectClosure and its PerfectField instance give only the field input. Combining these with construction of the restricted arrow groupoids requires genuine work; the perfect-restriction node is unsplit, not falsely marked a Mathlib leaf. CategoryTheory.Subgroupoid.{map,im,ker,comap} concerns ordinary groupoids; the manifold StructureGroupoid hits are unrelated. For the item, Scheme.Hom.isLocallyClosed_range and IsClosedImmersion.iff_isPreimmersion only give the immersion end of the argument; they do not prove 04Q9. I also read Immersion.lean:45-50 and the already-recorded 01IQ leaf. No new Mathlib leaf was created.

## Not duplicates

lem-sfb-field-groupoid-perfect-restriction vs lem-sfb-field-kernel-relation-immersion-closed: field restriction and homeomorphisms on arrows supply the reduction step; they do not assume or conclude closedness of the arrow image.
lem-sfb-perfect-field-groupoid-image-closure vs lem-sfb-field-kernel-relation-immersion-closed: over a perfect field, it constructs the reduced closure subgroupoid for an arbitrary image, with no locally-closed-image hypothesis and no claim that image equals closure.
lem-sfb-field-groupoid-open-image-closed vs lem-sfb-field-kernel-relation-immersion-closed: 04Q6 is the strictly more specialized open-image input; it gives no result for an arbitrary locally closed image. The item's argument forms a different target groupoid Z and a reduced source before it can invoke this input. This is the two-lemma proof of 04Q9, not moving its conclusion into a renamed node.

## Review by Q74

I reviewed the statement and all five proof steps with the cited node statements open, and checked B--E of delivery-errors.md in full. The new nodes contain only propositions, with empty proof/proof_deps and null proof_origin; they have their own introduced field, object scheme, arrow schemes, groupoid structures and morphism. Fields, spectrum, fibre products, field extension, closed immersion, reducedness and reduction cite the corresponding existing definitions. Perfectness and the reduced induced structure are defined inline, so the reader is not sent to a tag to recover a notion's meaning. TeX is stored with one mathematical backslash after JSON decoding. Each source has its Stacks tag and tex label.

For step 1 I checked the entire perfect-restriction statement, including the induced morphism and the equality q2 a'=a q1. Homeomorphisms q1 and q2, rather than mere continuity, are exactly what makes a'(R1')=q2^-1(I) follow. Since q1 is surjective the two images agree under q2, and since q2 is bijective their inverse-image equality follows. Closedness descends across this homeomorphism, and local closedness pulls back. No unproved theorem about the topological image commuting with arbitrary base change is used.

For step 2 the 04Q8 node actually asserts restricted operations and a groupoid inclusion for the closure, not just set-theoretic stability of composition. Applied to id_R1 it also gives the groupoid on A=(R1)_red. I verified this application uses R1, not the source's mistyped R2. The reduction definition states the identity on underlying sets, so a r has image I. The existing factorization node states exactly that a map from a reduced scheme factors through a closed subscheme when its image lies there; A is reduced, j is closed, and I lies in its closure. It is a generic tool from another unit, declared in split_report.tool_uses rather than in the maintainer's top-level tool_uses field.

For step 3 the definition of groupoid scheme gives the precise operation equations, and the closed-immersion definition includes the affine quotient description. Cancelling a closed immersion is elementary from that description: on each target affine open, the quotient ring surjection makes two lifts equal, and equality of local morphisms glues. After composition with j the unit, inverse and composition equations are already those for a,r,j. The source/target equations follow by composing with s2 and t2. This verifies b is a groupoid morphism, a hypothesis required by step 4, instead of treating a set-theoretic factorization as automatically equivariant. This step is marked elementary, with the algebraic cancellation argument written out.

For step 4 the cited 04Q6 node says an OPEN image of a morphism of field groupoids is closed, with no perfection or finite-type hypothesis hidden. The proof explicitly shows openness in the actual target Z: if I=O intersect C and C is closed, closure(I) lies in C, so I=O intersect closure(I). Thus b qualifies. Density and closedness imply I=|Z| directly by the definition of closure. This is the argument for the item's conclusion, not a new node restating it.

For step 5 the immersion definition explicitly supplies a closed-into-open factorization; its image is closed in that open and hence locally closed in R2. The first clause gives its closedness. The existing 01IQ node states precisely the equivalence between closed image and closed immersion for an immersion, with no properness hypothesis. Both of its statement clauses and the supplied immersion hypothesis were checked. The new nodes do not isolate this last clause as another theorem.

I tested the new statements on the identity groupoid morphism (the closure node becomes the usual reduced arrow groupoid), the unit inclusion into a group scheme, a constant finite groupoid over a field (the open-image lemma permits proper clopen images), and nonreduced arrows such as alpha_p (closure and source reduction are intentionally reduced while the original theorem need not assume reducedness). For imperfect k of characteristic p, the restriction uses both source and target base changes; it does not replace a groupoid by a single k-base-change or assume its two k-structures coincide. For characteristic zero or already perfect k the perfect-restriction construction may use k'=k. An empty arrow scheme is excluded by the unit from the nonempty field spectrum, so there is no vacuous groupoid edge case being dropped. Neither the new statements nor the applications assume finite type, algebraic closure, finite-dimensionality, separatedness, or quasi-compactness.

All proof steps are below 2000 characters and no long step hides another standard comparison. The three new statements are the genuinely non-elementary source lemmas used by the argument; the topological manipulations and equivariance cancellation remain explicit steps. The correction made during this reading was the R1-red source repair and the explicit verification that the factorized map is a groupoid morphism. The final required server dry run and push are recorded by the delivery tool.
