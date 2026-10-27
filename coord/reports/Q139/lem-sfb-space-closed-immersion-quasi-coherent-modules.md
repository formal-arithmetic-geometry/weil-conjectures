# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-immersion-quasi-coherent-modules.json: item split into six complete proof steps; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-pushforward-geometric-stalks.json: one new statement-only auxiliary lemma, unsplit; Mathlib no match, zero Mathlib leaves.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report. searches.jsonl contains the actual msearch.py outputs' query/result digests.

## Attachments

None. Searched WeilConjectures for the exact blueprint id, AlgebraicSpace/algebraic space, and the closed-immersion/quasi-coherent notions. The relevant project material is scheme-specific; it does not state the algebraic-space item. No attachment is claimed from a partial theorem or a sorry declaration.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Corrections and scope

The item's mathematical statement is unchanged. I added a citation for the existing canonical module functors to specify the adjunction used in the proof. I retained the inherited chapter, unit, blueprint ancestry and all other metadata. The latest blueprint's det-thm-sf-ctf-stability-direct-images proof (3) concerns direct-image stability via compactification; this auxiliary supports the inherited first-order-thickening chain beneath that proof. No chapter or unit route is replaced and this is not the unit key node.

No new node restates a clause of the item. The new lemma is about geometric stalks of arbitrary abelian sheaf direct images; it makes no quasi-coherence, ideal, equivalence or exactness assertion. The six item steps retain the actual algebra and functor arguments.

During self-review I removed a provisional geometric-stalk exactness node: the existing lem-sfb-space-stalk-ideal-pullback already states exactness and joint detection of isomorphisms. Although phrased in a square-zero diagram, identity thickenings have zero square-zero ideals and specialize that clause to every algebraic space. Step 3 explicitly gives this specialization, so no hypothesis of square-zero is added to the present closed immersion. Step 6 explicitly reflects exactness by applying these exact conservative stalks to each kernel modulo image. The unused searches for the discarded provisional node remain in searches.jsonl as an honest record.

## Source error

Stacks Tag 0DK1, spaces-morphisms.tex lemma-stalk-push-closed, transposes its displayed subscripts: for an abelian sheaf A on Z, (i_*A) must have its stalk at the image point bar x of X, and A must have its stalk at bar z of Z. Written literally, the displayed source formula takes stalks on the wrong sites. The source proof immediately computes the direct image at bar x and reduces to the correctly typed scheme formula. The new lemma uses (i_*A)_{bar x} = A_{bar z}, with its canonical restriction comparison, and documents the correction in its source field. Tag 04FX in etale-cohomology.tex gives the scheme formula, including zero off Z; Tag 04E5(2) gives closed support for abelian sheaves on algebraic spaces. This is a source notation repair, not a dispute with the item.

I also noticed that Tag 04K5's exactness sentence says geometric points of S where it must mean geometric points of X; the preceding assertions and the proof use points of X. I did not create a new node for this theorem because the existing ideal-pullback node already supplies the exact-conservative module-stalk clause needed here.

## Searches and new node

For the item and the proposed closed-stalk lemma I ran LeanFinder twice with distinct phrasings, Loogle, LeanSearch, and grep through msearch.py, then read the returned types. All services returned answers. For the item the hits are scheme closed-immersion/ideal constructions, scheme Zariski module functors, and local quasi-coherent presentation data. For the new lemma the hits are scheme Zariski stalk/restriction maps, ringed-space stalk maps and definitions of scheme etale objects, not an arbitrary algebraic-space small-etale closed direct-image stalk theorem. Read the relevant Mathlib ClosedImmersion.lean source and Modules/Sheaf.lean restriction-stalk declaration: these require schemes and ordinary topological stalks. No hit is a one-line specialization to the new lemma. The records use the exact command queries and real logged result digests.

Before creating the new lemma I searched all DAG nodes for 0DK1, 04E5, 04FX and stalk-push-closed, and the full imported blueprint with blueprint_refs.py search for stalk-push-closed, closed-immersion-push-pull, closed pushforward and geometric stalks. I also searched quasi-coherent modules for the item. The inherited blueprint.from.node is null, as confirmed by blueprint_refs.py ancestor; the new node retains that ancestry with the item prepended to via and the precise supporting step appended to place. same_as is empty because no blueprint node states this algebraic-space arbitrary-abelian-sheaf formula.

## Not duplicates

lem-sfb-space-closed-pushforward-geometric-stalks vs lem-sfb-space-closed-coherent-modules: the existing node assumes a Noetherian ambient space and states coherence and equality of supports for coherent modules; the new node computes canonical stalk isomorphisms for every abelian sheaf, with no Noetherian hypothesis.

lem-sfb-space-closed-pushforward-geometric-stalks vs lem-sfb-space-stalk-ideal-pullback: the existing node computes structure-ring and ideal pullback stalks in square-zero thickening diagrams and includes exact-conservative stalk functors; it does not compute direct-image stalks of arbitrary abelian sheaves along a general closed immersion. We reuse its exact-conservative clause rather than duplicate it.

lem-sfb-space-closed-pushforward-geometric-stalks vs lem-sf-etale-immersion-shriek-normalization: the existing node normalizes compact-support functors of separated finite-type immersions of Noetherian schemes with finite constant coefficients; it does not state the arbitrary abelian sheaf geometric-stalk comparison for algebraic spaces.

lem-sfb-space-closed-pushforward-geometric-stalks vs lem-weil-pbc-open-closed-short-exact: the existing node gives the open/closed unit-counit short exact sequence for an ambient sheaf on a scheme; it does not give this stalk formula for every abelian sheaf on a closed algebraic subspace.

## Tool uses

The existing trace-formula nodes lem-trf-space-qc-separated-etale-local, lem-trf-space-qc-separated-quasi-coherent-pushforward and lem-trf-space-etale-module-pushforward-restriction are generic tools. Their statements supply respectively the chartwise morphism properties, the general quasi-coherent pushforward theorem and the canonical etale restriction comparison. The unit has no substitute for these generic tools; their use does not replace any unit proof route. They are declared in split_report.tool_uses, not in maintainer-owned tool_uses.

## Review by Q139

I read spaces-morphisms.tex Tags 03MB and 04CJ, including their proofs, against every clause of the item. I also read the closed-push-pull and closed-stalk lemmas 04E5 and 0DK1; etale-cohomology.tex Tag 04FX, including its scheme neighbourhood description; and spaces-properties.tex 04K5 and 03M1 and sites-modules.tex 04EQ and 05V5 for the exactness and tensor identifications. The new node's statement follows the closed-stalk source, corrected as above, and the complement is zero by 04E5(2). It contains no proof or hidden quasi-coherence assertion.

For step 1 I opened the exact statements of def-weil-closed-immersion, lem-trf-space-qc-separated-etale-local, lem-trf-space-qc-separated-quasi-coherent-pushforward and def-trf-space-quasi-coherent-module. The closed immersion is representable, so each affine test is Spec(R/J). This verifies quasi-compactness directly; quotient-ring uniqueness gives a monomorphism and its diagonal is an isomorphism, hence separated. Only after verifying these hypotheses do I apply the existing general pushforward statement. O_Z has its one-generator presentation. The step proves these verifications explicitly rather than assuming an uncited closed-immersion finiteness theorem.

For step 2 I opened lem-trf-space-etale-module-pushforward-restriction and lem-sfb-space-qcoh-kernels-colimits. The former states the canonical module comparison and its section formula, exactly what identifies the structure map on affine tests. The latter states quasi-coherence of kernels for arbitrary algebraic spaces, with no Noetherian condition. Surjectivity is local lifting on affine etale tests, where the map is R to R/J; I do not claim global section surjectivity on nonaffine objects. The kernel is an ideal because the structure map is multiplicative.

For step 3 I checked the new closed-stalk node and reread the entire statement of lem-sfb-space-stalk-ideal-pullback. Its exact-conservative clause applies via the identity-thickening square, not via a claim that the current i is square-zero. The new comparison is the restriction of section germs, so its ring compatibility follows from the actual ring operations on those sections. Exactness then identifies B with A/I at a point on Z and I with A off Z.

For step 4 I opened def-trf-space-etale-module-functors and lem-sfb-space-geometric-stalk-tensor-calculus. The former specifies the canonical adjunction and local tensor normalization; the latter states an ordinary-complex pullback stalk formula in addition to a derived formula. Taking f=id_X, g=i and a complex concentrated in degree zero gives exactly the ordinary tensor formula needed; no flatness or derived comparison is assumed. The quotient A to B is surjective by step 3. The written multiplication map and its m to m tensor 1 inverse prove the counit stalk isomorphism. I wrote the inverse on Hom sets and its adjunction justification, so full faithfulness is not inferred merely from an unspecified left inverse.

For step 5 I checked that lem-sfb-space-module-pullback-quasicoherent states preservation of quasi-coherence for every morphism of algebraic spaces, with no flatness condition. Its output is the actual i^*F used here. The scalar action kills I on every i_*G by definition. Conversely the unit is the canonical map on tensors from the specified adjunction. The inverse m tensor a-bar to am is well-defined precisely because IF=0. Off Z, I=A gives F=0. These verifications use the stalk statements actually quoted, and preserve all objects and maps of the item.

For step 6 the new closed-stalk comparison is natural in sheaf morphisms, so it identifies the entire pushed-forward sequence on stalks, not only its three objects. The exact-conservative clause of the existing ideal-pullback node detects the vanishing of the kernel/image obstruction. The existing quasi-coherent kernel/cokernel statement makes exactness in module sheaves equal to exactness in the full quasi-coherent category. This supplies the exactness clause that the text of 04CJ does not spell out separately.

I tested i=id, Z empty, the zero module, and affine quotient maps R to R/J for J=0 and J=R. The functor is respectively the identity or the zero-source embedding; the essential image is respectively all modules or just zero. Also tested R=k[e]/(e^2), J=(e), and a non-finitely-generated ideal in an infinitely generated polynomial ring: the tensor inverses and stalk arguments require neither nilpotence nor finite generation nor Noetherianity. The new abelian stalk formula needs no module presentation. All six steps are below 2000 characters and none hides an extra comparison lemma. Every citation has a literal statement substring in citations.json. B-E were checked against the files: self-contained statement-only new node, exact Stacks tags, actual recorded searches, no duplicate, no circular edge, no clause relabelling, and every non-elementary input named by the statement that supplies it.

## Unfinished work

The new closed-stalk node remains statement-only, as stage 1 requires for an auxiliary created in this split. No Lean was written, no compiler or Lake was run, and no repository or launcher file was changed. Server review_split passed before the delivery dry run; final delivery status is recorded by the delivery command.
