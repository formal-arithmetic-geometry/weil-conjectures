# Stage-1 delivery: lem-sfb-graded-normalization-fraction-map

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-graded-normalization-fraction-map.json: existing statement split in eight steps; no exact Mathlib match. Its mathematical statement is unchanged. The existing module-localization definition was added to stmt_deps to support the total ring of fractions mentioned in the statement.
- citations.json: one literal statement quotation for each cited node in each proof step.
- searches.jsonl: actual msearch command results for this item, retained alongside the inherited searches in the item.
- report.md: this report.

No new nodes; no Mathlib leaves delivered. No unit or chapter record changed.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by graded-normalization, fraction-map, associated-graded, and normalization terminology found no project declaration stating the item. I read RingTheory/AssociatedGradedRing.lean: its closed component constructions provide the associated graded ring, not this map or its independence clauses. A proof about a different fraction map is not an attachment. I wrote no Lean and ran no compiler.

## WANTED

None. I read Stacks curves.tex, Tag 0CBT (remark-quadratic-extension), including the three constructions and its explicit omission of the equivalence with (3). The intrinsic fraction proof fills those omitted details and is marked agent-written, not attributed to a proof in Stacks. The homogeneous-overlap tool is Stacks constructions.tex, Tag 01M4 (lemma-standard-open), (1)(c)–(h) and the proof, which I read in full. I also read algebra.tex, Tag 00JM (section-proj), for the degree-zero fractions and homogeneous spectrum. No SGA source is used.

## Faults and changes

The item had an empty proof and no sandbox attempt. Its statement is true under its stated hypotheses, including without Noetherianity or finiteness of B. I retained it verbatim. In particular, I did not add a domain assumption, require that ell be regular in G, or claim that theta is an isomorphism. Its definitions of degree-zero localization, Proj, associated graded ring, quotient algebra and spectrum already exist. The total-fraction notion is the ring case of the existing module-localization definition; its multiplicative set of nonzerodivisors is written explicitly in step 8.

The crucial possible gap was cancelling ell in G. Step 3 instead retains the arbitrary witness k in the localization equality, obtains an element of m^(k+n+m+1), extends to f^(k+n+m+1)B, and cancels only the injective multiplier f^(k+n+m) in B. This proves independence even when G has ell-torsion. The denominator-change calculation is also literal: g=fu, f=gv, uv=1, and d/g^n=(d/f^n)u^(-n).

The proof needs the actual principal-localization description of the common Proj overlap. I did not ask the basic-open intersection node for that stronger algebra statement. Step 6 cites the ring case of lem-weil-pbc-graded-module-away-restriction, clauses (i) and (iii), using the relation h=ell*ell_g, and separately cites the basic-open node and the Proj fractional-sheaf definition for the scheme interpretation.

## What remains unfinished

Nothing in the requested stage-1 split. Proving the Lean statements is outside this task. The accepted dependency nodes remain independent items for their own workers where their status is not mathlib or closed.

## Searches and reuse

The sandbox was initially empty of nodes, report and searches. I read the item's inherited Mathlib search results, retaining all of them, and made the five additional logged searches in searches.jsonl through the required msearch.py command: two semantic phrasings, Loogle, grep, and LeanSearch. These returned general HomogeneousLocalization maps, chart maps and residue maps, not the division-and-residue map from gr_m A together with its independence and normalization naturality. I read HomogeneousLocalization.lean at NumDenSameDeg, its quotient by ordinary localization equality, awayMap, awayMap_mk, and Away.isLocalization_mul, and ProjectiveSpectrum/Basic.lean at the overlap and chart-map lemmas. None states the item as an exact match or a one-line specialization, so mathlib_match remains null.

I searched the whole DAG by the source tag 0CBT, associated graded, total fractions, localization universal property and chart overlaps, and ran blueprint_refs.py ancestor plus searches for homogeneous localization, localization, integral closure, fraction map, associated graded, and chart overlap. The nearest blueprint ancestor is null as already recorded for this imported six-functor chain; I retained its exact from.place and via chain and same_as=[]. I read the current latest blueprint chapter/unit and direct-images proof, rather than an older blueprint snapshot. The item supports that unit's alteration/nodal-branch subargument; it does not state the unit or change its route. Existing definitions and tool nodes supply all needed notions and facts, so there was no reason to create another node. The generic tools outside the unit are declared in split_report.tool_uses.

## Not duplicates

No new nodes. Existing nodes reused include the associated-graded structure theorem, the degree-zero localization definition, the ordinary localization definition and universal property, the graded-away restriction theorem, the Proj basic-open intersection theorem, the Proj definition, and the affine-spectrum correspondence. The normalization/total-fraction nodes with Noetherian, finite-type or dimension-one hypotheses are not used for the general isomorphism functoriality: step 8 proves that two-line fraction-and-monic-equation calculation directly from the definitions.

## Review by NX

I read the required delivery-errors B–E and compared the complete statement with Stacks 0CBT. That source says the normalization residue algebra and tangent Proj are canonical but omits the comparison. The item isolates the intrinsic map needed in that omitted argument; its more general hypotheses suffice for this construction. I checked all eight steps against the actual dependency statements, not their proof texts. No new node is a clause restatement, a duplicate or an elementary fact, because there are no new nodes. The elementary steps below are explicit calculations from definitions and previous steps, with every external structural fact cited. All step texts are below 2000 characters.

Step 1 uses def-weil-pbc-algebra-hom-quotient for ideal products, ideal powers, quotient rings and their structural maps. Expanding products proves m^n B=(mB)^n, and repeated injectivity proves cancellation of f^n. This verifies existence and uniqueness of every division coefficient, including n=0. The F-action comes from the quotient since m maps into mB; it needs no coefficient-field embedding into A.

Step 2 uses the associated-graded definition for the exact equivalence between equality of degree-n classes and difference in m^(n+1), and the quotient-algebra definition for residue classes. I verified that the residual difference is fc after cancellation of f^n. The additivity and scalar assertions follow from the displayed f^n equations, with no use of flatness.

Step 3 uses the degree-zero homogeneous-localization definition for representation by x/ell^n, the ordinary localization definition for an arbitrary extra witness ell^k, and the associated-graded structure theorem for the precise homogeneous product formula. Its exponent k+n+m is the degree of both terms; vanishing means membership in the next ideal power. Cancelling f^(k+n+m), which is injective by step 1, gives the required difference in fB. The cited structure theorem really states multiplication of classes; I did not use a definition as a substitute for a missing theorem.

Step 4 uses the ordinary localization sum/product rules, the graded structure theorem, and the algebra-hom quotient definition. I checked the common denominator ell^(n+m) and numerator f^m d+f^n e. Dividing that numerator and de gives respectively the sum and product of the division coefficients. The n=0 values give preservation of 1 and the F-action. Uniqueness is equality on all representatives, not an unproved generation assertion.

Step 5 uses the quotient-algebra definition only for passing the explicit B-identities to E. The earlier construction applies to g because both hypotheses are assumed for g. The identities g=fu and f=gv imply uv=1 using regularity of f; there is no unsupported assumption that f or g is invertible in B. Substitution checks the nth-power formula, including n=0 and negative powers of the genuine unit u only.

Step 6 uses four actual statements and the Proj fractional-sheaf definition. The basic-open node says exactly that the intersection is the principal open of ell_g/ell in the ell chart. The graded-away restriction node has a stronger relation hypothesis; I checked it using h=ell*ell_g, exponent 1, and multiplier ell_g, with the factors exchanged for the second chart. Both degrees are 1, h has degree 2, so its clause (iii) localizes at h/ell^2=ell_g/ell. Its clause (i) says the maps are the same ordinary fractions. The Proj definition supplies the sheaf of locally represented fractions, so these are the scheme restrictions too. The localization universal-property node applies because [u] and [v] are units; it gives uniqueness on the overlap localizations. The affine-spectrum node supplies exactly the contravariant ring-map correspondence needed to conclude equality of the two composites into Proj. The fractional identity agrees with step 5 on every representative, so this step has no hidden descent claim.

Step 7 uses the associated-graded, localization and quotient-algebra definitions. I checked that alpha and its inverse carry each ideal power onto its counterpart, ensuring the induced graded and quotient maps are isomorphisms. The same fraction equality relation makes the chart map well defined. Applying beta to f^n b=d and using regularity of alpha(f) gives the naturality equation on every fraction. No choice of coordinates or of a residue-field section occurs.

Step 8 uses the ring case of the module-localization definition for total fractions and the integral-closure definition for monic equations. I checked that an isomorphism carries every nonzerodivisor, and only those elements, to a nonzerodivisor. The fraction formula has a literal inverse and respects the displayed localization relation. Applying alpha to a monic equation preserves its leading coefficient 1; applying alpha inverse gives equality of the integral-closure subrings. This supplies the compatible beta required in step 7 without any additional Noetherian or dimension assumption.

I tested small and boundary cases. For a DVR A=B and a uniformizer f the map is the usual residue-field identity; changing to g=af for a unit a gives the displayed inverse power. For the split node A=(k[x,y]/(xy))_(x,y), B the product of its two normalized branches and f=x+y, the quotient is k×k and all formulas are componentwise; this checks that B need not be a domain and also works in characteristic 2. If f is already invertible in B (take B=A[1/f] with f regular), then E=0 and the unique unital map to the zero ring, and the empty-spectrum comparisons, are all allowed. If ell is nilpotent, the constructed ring map forces 1=0 in E by the same extra-power calculation, consistent with the zero source chart; no nonemptiness was assumed.

For a nontrivial extra-power example, take A=(k[x,y]/(xy-x^3))_(x,y), f=y, and B=A[x/y] inside A[1/y]. The ring A is reduced, y is in neither of its two minimal primes and hence is regular; the injection into A[1/y] makes it regular on B. Writing u=x/y gives x=yu and u=yu^3, so mB=yB and [u]=0 in E. In gr_m A the nonzero initial class of x is killed by ell=in_1(y), since xy=x^3 is in m^3. Thus in_1(x)/ell=0 requires exactly the extra-power relation handled in step 3, and its proposed image is indeed [u]=0. Finally, dropping regularity would fail: in k[epsilon]/(epsilon^2) with f=epsilon, the equation f b=0 has both b=0 and b=epsilon. The hypothesis excludes this ambiguity. These checks found no statement dispute or source correction to make.

I verified each citations.json quote as a literal substring of the current node statement and checked that every proof uses entry has its corresponding quote. Server dry-run results and delivery follow below.
