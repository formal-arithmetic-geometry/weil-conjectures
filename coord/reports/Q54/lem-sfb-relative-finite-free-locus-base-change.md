# Stage-1 report: lem-sfb-relative-finite-free-locus-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-finite-free-locus-base-change.json: item, split; statement and statement dependencies unchanged; four proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-module-flat-locus-base-change.json: new statement-only prerequisite, unsplit; not a Mathlib leaf. This is Stacks 05VJ for an arbitrary quasi-coherent finitely presented module, not its structure-sheaf specialization.
- citations.json: verbatim statements for every citation of every parent step.
- searches.jsonl: searches actually run through msearch.py; item searches supplement the existing creator's records, which were retained.

## Attachments

None. Searched the exact blueprint tag and the notions finite-free locus, freeLocus, locally-free locus, relative flat locus and 05VJ in the live read-only WeilConjectures source. The similarly named FiniteFreeResidueLocusOpen theorem concerns residue cohomology of a bounded complex; FiniteFreeConstantLocalLift concerns lifting maps along epimorphisms. Neither states this item. Mathlib is not attachment evidence.

## WANTED

None. All source arguments used here are in literature/stacks-project/.

## Problems found and changes

The item was unsplit and had no sandbox attempt. Its statement faithfully matches more-morphisms.tex, Tag 0CZR, lemma-finite-free-open (lines 4823-4846); there is no statement dispute or correction. Openness is immediate from the definition of W, but arbitrary base change requires reflecting local freeness, not just preserving it. The creator's Mathlib hits do not supply that reflection.

The existing lem-sfb-relative-flat-locus-base-change is the structure-sheaf assertion (05VK), requiring the source scheme to be flat over the parameter scheme. It cannot be applied to a general module F, and flatness of p is explicitly absent in our item. Similarly lem-sfb-fibrewise-flatness-criterion, lem-sfb-relative-flat-fibre-test, and lem-sfb-pointwise-flatness-base-change have morphism/structure-sheaf statements. I did not treat them as module theorems. The new node is the general module assertion 05VJ actually invoked in the final sentence of 0CZR.

The parent retains the substantial identification of finite freeness with stalk flatness: finite presentation passes to the stalk, a finite flat module over the local ring is free, finite generation makes a basis finite, and the basis spreads to a free neighbourhood. The new prerequisite does not assert that identification or any finite-free locus. The parent also gives the two maps that pull back a finite free trivialization. Thus this is not a relabelling of the item's clause or a transfer of its whole proof to one child.

The 080Q node lem-trf-flat-fibre-free-neighbourhood assumes finite presentation of the morphism, stronger than the item's local finite presentation. Rather than silently apply it globally, I used the existing ringed-space finite-presentation-stalk and basis-spreading statements. This even proves the free/flat identification without a relative morphism hypothesis.

## Blueprint and searches

Read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md and sk-thm-sf-ctf-stability/_section.md, alongside the DAG chapter and unit records. The assigned item has no imported blueprint identity and its recorded nearest blueprint ancestor is null; blueprint_refs.py ancestor confirms this. Retained its full Picard-stack/invertible-open provenance and specified the final sentence of 0CZR where the new node is used. No chapter or unit file is changed. The latest unit is phrased differently from the old direct-images provenance, but this assigned source-local prerequisite is not used to change any higher route.

Whole-DAG searches used 0CZR, 0CZT, finite-free-open, 05VJ, base-change-criterion-flatness-fibre, flat-locus and fibre-flatness keywords. Whole-blueprint searches used finite free, flat locus, flat sheaf, flat at, module flat, relative flat and 05VJ; none states the new module theorem. Nearby module pullback, stalk-presentation, local flat freeness and basis-spreading nodes were reused. The new id did not exist before writing it.

For the new node I ran leanfinder with both its general-module/family formulation and a second flat-locus formulation, leansearch, loogle (Module.Flat, Module.FinitePresentation), and full-Mathlib grep (flatLocus|flat_locus|locus.*flat|flatness.*fib). For the item I reran all four services, including two semantic phrasings. Every query is in searches.jsonl and the node records reproduce those actual records. No service was unavailable.

Read FreeLocus.lean:49-174, Flat/Stability.lean (trans and isBaseChange), LocalRing/Module.lean:304-309, and UniversallyOpen.lean. The hits give openness of free loci, preservation of flatness under extension of scalars, and openness of maps already flat. They do not reflect module flatness after a nonflat change of the parameter scheme. The Loogle projective_of_finitePresentation hit assumes flatness over the total module ring; it does not solve that relative reflection. Consequently there is one new unsplit node and zero new Mathlib leaves.

## Not duplicates

lem-sfb-relative-module-flat-locus-base-change vs lem-sfb-flat-residue-fibre-square: the latter supplies the cartesian residue-fibre square and flatness of its horizontal maps, with no module or flat-locus conclusion; the new node states the general module flat-locus theorem of 05VJ.

lem-sfb-relative-module-flat-locus-base-change vs lem-sfb-relative-flat-fibre-test: the latter treats flatness of a morphism with source scheme flat over S, not flatness of an arbitrary module whose source need not be flat; it also does not state the general module locus theorem.

lem-sfb-relative-module-flat-locus-base-change vs lem-sfb-relative-flat-affine-charts: the latter provides affine ring charts and openness for the structure-sheaf flat locus; it does not state parameter base-change compatibility for arbitrary modules.

lem-sfb-relative-module-flat-locus-base-change vs lem-sfb-relative-flat-locus-base-change: the latter is the structure-sheaf specialization, requires p flat, and says nothing about an arbitrary relatively flat module on a nonflat X. Both are useful statements and the earlier one does not specialize to the new one.

lem-sfb-relative-module-flat-locus-base-change vs lem-sfb-relative-finite-free-locus-base-change: the child concerns flatness of arbitrary modules relative to a second family Z, with an independent map X to Z. It asserts no finite free neighbourhoods; the parent proves the flat/free correspondence using separate existing statements and then specializes to the identity map.

## Review by Q54

I read 0CZR's statement and complete proof in more-morphisms.tex and 05VJ's statement and complete proof (lines 4702-4756). I also checked the adjacent 080Q statement and proof, Modules 0B8J (lemma-finite-presentation-stalk-free, lines 1537-1555), and Algebra 00NZ (lemma-finite-flat-local) and 00NX (lemma-finite-projective). The tag/label correspondences were checked against tags/tags. The new statement keeps all four hypotheses of 05VJ: X locally finitely presented over S, M finitely presented, M flat over S, and Z locally of finite type over S. M is quasi-coherent as in the source. In particular it adds no flatness assumption on the scheme X or on the base-change map.

Step 1 is only the union-of-open-neighbourhoods argument. It introduces the total stalk-flat locus and makes no unstated base-change assertion.

In step 2, I opened all four cited nodes. lem-sc-affine-standard-cover-finite-free-local-fp-flat states that a module with a finite basis is flat (and finitely presented). lem-weil-pbc-finite-presentation-source-stalk states a finite presentation of the stalk with a surjective generator map. lem-weil-pbc-finite-flat-local-free states freeness of a finitely generated flat module over a local ring. lem-trf-finite-presentation-stalk-basis-spread explicitly supplies a neighbourhood isomorphism for any specified finite basis of a finitely presented sheaf's stalk, including rank zero. These are exactly the facts used. Finite generation follows from the stated surjection; finiteness of the resulting basis is proved by the finite union of supports, not assumed. The structure-sheaf stalk at a scheme point is a local ring. The basis-spreading node needs no Noetherian or morphism finiteness hypotheses. I declared the two off-unit unfinished ringed-space facts as generic tools in split_report.tool_uses; the other two are Mathlib leaves.

Step 3 cites the new statement, which explicitly gives the equality of module flat loci under any parameter change. The substitution is S=T, X=Z=Y, a=p, f=id, M=F. The identity is over T. The given local finite presentation of p gives the needed local finite type of a by forgetting the finite relations of the same affine presentation. F's finite presentation, quasi-coherence, and relative flatness are the item's hypotheses. The induced map after base change is again the identity, so the coefficient-ring stalk in the child's formula is exactly the total local ring on Y_1. This checks both the object and every hypothesis, rather than using the structure-sheaf-only node for the missing module claim.

Step 4 again uses the finite-free-module-flat statement for a free stalk upstairs; step 3 reflects its flatness downstairs and step 2 turns that into a free neighbourhood. For the converse, I opened def-pc-module-pullback and checked that it gives the tensor formula, rather than expecting it to state a flatness theorem. The two explicit coordinate maps give the finite free pullback isomorphism and commute with restrictions, so that part is an elementary computation from the definition. We never need to assume flatness of v or to invoke a new unstated theorem saying q^*F is relatively flat or finitely presented.

Small cases checked for the item and child: F=0/M=0 (rank zero and U equal to the whole space), empty source or empty changed base, identity base change, finite free modules of variable rank on disjoint open pieces, and a nonflat p with F=0. For the general module child, the closed point Spec(k) into A^1_k has M=O_X flat over k but nowhere flat over the target; its flat locus is empty, consistently after any extension of the parameter field. A necessary-hypothesis test is p=id on Spec(k[t]) and F=O/(t): F is not flat over the parameter scheme, the original free locus is D(t), but its pullback to t=0 is free of rank one. Thus arbitrary base change must not be inferred for all finitely presented sheaves; the child's relative flatness hypothesis is essential. This also explains the failed tempting use of the Mathlib ascent-only hits.

Against delivery-errors B-E I checked: self-contained statement-only child, its definition dependencies, actual logged searches, correct tag and label, exact quotation for every citation, no use of a cited proof instead of its statement, no source/target confusion in the identity substitution, no added global finite-presentation/Noetherian/flat-p assumption, and no clause-restating child. Every parent step is shorter than 2000 characters (196, 689, 517, 557 at the initial write); no long step hides an auxiliary lemma. No SGA source is used. The only corrections while developing the split were avoiding the 080Q global finite-presentation hypothesis and distinguishing the module theorem from the existing morphism theorem.

## Unfinished work

The new 05VJ node is deliberately statement-only and joins the stage-1 queue. Its successor should follow the proof in more-morphisms.tex: openness of module flatness, the module fibrewise criterion (including zero stalks), then the cartesian residue-field fibre square and flat ascent/reflection for module sheaves. The existing morphism-only nodes must not be cited as if they state those module versions. Nothing needed to split the assigned item is left unfinished.
