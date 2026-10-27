# Stage-1 delivery: lem-sfb-space-first-order-ringed-description

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-first-order-ringed-description.json — item, statement; split, no Mathlib match. The original statement and inherited provenance/searches are retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-immersion-quasi-coherent-modules.json — new statement-only node; unsplit, no Mathlib match. It states the quasi-coherent ideal and annihilated-module direct-image theorem for an arbitrary closed immersion of algebraic spaces, not the first-order realization theorem.
- citations.json — verbatim statement excerpts for every proof-step citation, including both parts of the new module theorem used in step 1.
- searches.jsonl — actual msearch.py records; item and new-node searches used two semantic phrasings, Loogle and source grep. All services were available.
- report.md — this report and signed review.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, first-order thickenings, and algebraic-space/ring-sheaf terminology found no declaration stating every clause. Scheme universal thickenings and dual-number constructions are different results. No Lean file was written or compiled.

## WANTED

None. All source statements used here were read in the local Stacks checkout.

## Findings and corrections

The imported statement is correct and unchanged. Its realization and maps are already stated, more generally, by lem-sfb-space-square-zero-ringed-realization, which I read in full and cite rather than duplicating. The present item additionally asserts that the ideal of an arbitrary given first-order thickening is quasi-coherent over the closed space; that claim is not in the existing realization node. Thus the proof is an assembly using that existing general theorem plus the closed-immersion module theorem, not a second construction of the same realization nodes.

I read spaces-more-morphisms.tex, section-thickenings, including Tags 05ZN, 05ZS and 05ZT and their proofs. Their general realization proof works by affine sections, scheme thickenings, an etale relation quotient, and descent, and its general form is already the statement of the existing node. I also read spaces-morphisms.tex Tag 03MB (lemma-closed-immersion-ideals) and Tag 04CJ (lemma-i-star-equivalence), including the proof of part (3). Those are the source of the new module lemma. Its generality matters: it has no nilpotence assumption and describes all modules annihilated by the defining ideal, while the item uses it with the ideal itself.

I searched the whole DAG for Tags 03MB and 04CJ, closed-immersion/quasi-coherent/annihilation terminology, and the proposed new id; I also ran blueprint_refs.py searches for thickening, square-zero, annihilated, 03MB, 04CJ and quasi-coherent module. No blueprint node states the new algebraic-space theorem. The 04CJ nodes found below are scheme-only or formal-functions specializations; none suffices for algebraic spaces.

The inherited blueprint chain has no remaining blueprint ancestor: tools/blueprint_refs.py ancestor prints None. Its existing from.node = null and full place/via provenance are retained, with the item prefixed to the new node's via. I read the current literature/blueprint/latest/ direct-image proof (3) and unit statement. The historical chain recorded in from.place passes through the proper-space deformation prerequisite; I changed no unit/chapter route or realized fields. The latest blueprint does not independently state either this item or the new module theorem.

Mathlib search hits were read: IsClosedImmersion.overEquivIdealSheafData (Morphisms/ClosedImmersion.lean, line 180) concerns closed subschemes of a Scheme; Scheme.IdealSheafData and subschemeObjIso are scheme data; Algebra.Extension and TrivSqZeroExt are ordinary ring constructions; Scheme.Etale describes schemes etale over a scheme. SheafOfModules.QuasicoherentData fields only describe presentations. None supplies the algebraic-space theorem or its direct-image essential image. The JSON records use exactly the query texts and actual logged results; no unavailable service is treated as absence.

## Not duplicates

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-closed-immersion-unit-quotient: the existing statement concerns schemes and the unit quotient of an arbitrary module; it does not assert the quasi-coherent ideal or the essential image for closed immersions of algebraic spaces.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-closed-immersion-unit-kernel: the existing statement concerns schemes and a kernel fork for the module adjunction; it gives neither algebraic-space quasi-coherence nor the essential-image theorem.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-formal-functions-finite-sheaf-quotient-iso: the existing statement identifies a formal-functions finite-fibre quotient with a pushforward; it is not the arbitrary-closed-immersion ideal/module theorem for algebraic spaces.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-formal-functions-finite-sheaf-quotient-closed: the existing statement says a particular finite-fibre morphism is a closed immersion, not the ideal or module properties of an arbitrary algebraic-space closed immersion.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-formal-functions-finite-sheaf-quotient: the existing statement is the scheme formal-fibre quotient comparison; the new statement concerns arbitrary algebraic spaces and exact fully faithful quasi-coherent direct image with its annihilator essential image.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-weil-pbc-closed-immersion-pushforward-annihilated: the existing statement covers schemes and their ordinary module sheaves; it cannot be applied to algebraic spaces without the etale-chart descent theorem now stated in the new node.

lem-sfb-space-closed-immersion-quasi-coherent-modules vs lem-sfb-space-first-order-ringed-description: the item concerns first-order thickening realization and maps, whereas the new lemma is the general closed-immersion module theorem; it neither identifies etale sites nor constructs a thickening or a morphism from ring-sheaf data.

## Review by Q83

I checked the item against Stacks 05ZS, 05ZT and 05ZN in spaces-more-morphisms.tex. The site equivalence is pullback along the actual thickening, the kernel is an ideal rather than an arbitrarily chosen module, the base ring is the inverse-image sheaf f^{-1}O_C, and the ring-sheaf map reverses the geometric direction. None of the source hypotheses requires properness, finite presentation, Noetherianity, or a scheme target. I retained that generality.

Step 1 cites the existing realization node only for its explicit assertion that pullback identifies the small etale sites. It cites the new closed-immersion module lemma for precisely the surjection with quasi-coherent ideal and the annihilated-module essential image. I read both statements and copied the actual sentences to citations.json. The ideal is square zero by hypothesis, so it annihilates itself; that verifies the essential-image hypothesis with F = J. The inverse-image quotient action is the prescribed O_Z action: the difference of any two lifts belongs to J and has zero product with J. This supplies quasi-coherence on Z, which would not follow merely from quoting the definition of a module or of a thickening. I checked this on the affine test Spec(A/I) inside Spec(A) with I^2 = 0: it says I is an A/I-module, with the same local sections.

Step 2 uses the existing realization statement, not a construction hidden in its proof. The identification X = Z, B = C, G = J preserves every hypothesis: sheaf exactness, algebra quotient, square-zero multiplication, and quasi-coherence over O_Z. Its statement explicitly supplies both the thickening over C and the compatible extension isomorphism. No new clause node was made. Step 3 likewise takes the existing general morphism statement at g = id_Z. If alpha runs from O_(Z'_2) to O_(Z'_1), its conclusion runs from Z'_1 to Z'_2, and its uniqueness is uniqueness of a morphism inducing that specified alpha. This is not a claim that the thickening has no automorphisms.

For the new node I read both 03MB and 04CJ(3), not merely their tags. I checked that it states only their conclusions, has exactness and full faithfulness rather than an unspecified descent claim, and explicitly explains the ideal-annihilation condition. The empty immersion gives the zero-module essential image, the identity immersion has zero ideal and gives all quasi-coherent modules, and a non-nilpotent affine ideal gives the usual A/I-modules among A-modules. These checks exclude an unintended nilpotence or nonemptiness assumption. The item also works for J = 0 (the identity thickening), the empty space, arbitrary quasi-coherent non-finitely generated J, and nonsplit algebra extensions such as Z/4 -> F_2. No splitting of the quotient map is assumed.

Against delivery-errors B–E I checked the full new statement's objects and definition dependencies, the exact Stacks labels, all cited statements (C4), and all substantive inputs (C1). The new node is statement-only, and the assembly proof introduces no hidden comparison lemma: its quotient scalar-action calculation is written out. All three proof steps are shorter than 2000 characters (1068, 664, 637); together they are shorter than 3000. No new node restates the realization or morphism clause, no source argument is used through a node's proof, and neither cited node depends on this item. There is no SGA citation. The same-unit existing realization lemma needs no off-unit tool declaration. Mechanical JSON and verbatim citation checks passed locally; required server dry-run checks follow.

## Unfinished work

No part of this one-level split is left unfinished. The new unsplit closed-immersion theorem remains for the ordinary stage-1 queue. Server preflight/dry-run and push status are recorded by the delivery command.
