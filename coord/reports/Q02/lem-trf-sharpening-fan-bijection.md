# Stage-1 report: lem-trf-sharpening-fan-bijection

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-sharpening-fan-bijection.json`: statement, corrected domain, fourteen proof steps, exact proof dependencies, blueprint ancestry, dispute and split report. Status split; not a Mathlib leaf.
   - `dag/nodes/sec-trace-formula/lem-trf-fine-monoid-unit-splitting.json`: statement-only algebraic lemma, status unsplit, no Mathlib match. Includes the extra torsion-free sharp-group hypothesis, full source qualification and actual logged searches. No proof or proof dependencies.
   - `citations.json`: one relevant verbatim statement quotation for every step/node citation.
2. Attachments: none. Searches for the item id, sharpening, monoschemes and Kato fans in the project declarations in slopmaster2 found no declaration of this result. The sole “sharpening” docstring concerns tensor powers and semicontinuity, not monoidal geometry. The reference master checkout likewise provides no attachment.
3. WANTED: none. The relevant ILO source is present; this delivery does not invoke its Ogus reference as a black box.
4. The source/statement issues and downstream consequence are recorded below. The inherited proof was empty. The historical blueprint ancestry and current unit/chapter binding were retained; this node is not the unit key theorem. No unit realization record was changed.
5. Nothing in the corrected split remains unfinished except the explicitly statement-only new algebraic lemma, which is the next stage-1 item. No Lean, compiler, Lake, source-repository writes, local DAG checker or git command was used.

## STATEMENT-DISPUTED: domain of the rule correspondence

The imported statement quantifies over all fine torsion-free monoschemes but targets fine torsion-free fans. The current fan definition tests the group completions of SHARP stalks. These conditions differ.

Take the submonoid
\[
P=\langle(2,0),(-2,0),(0,1),(1,1)\rangle\subset\mathbf Z^2.
\]
Its elements are all pairs with positive second coordinate, and the pairs with zero second coordinate and even first coordinate. It is fine and integral, its group completion is \(\mathbf Z^2\), and its units form \(2\mathbf Z\oplus0\). At its unique closed point the sharp stalk is \(P/P^\times\), whose group completion is \(\mathbf Z/2\oplus\mathbf Z\). Thus the sharpening of this torsion-free monoscheme is outside the stated fan category. In particular the proposed operation on rules was not typed on its claimed domain.

The correction keeps the project's existing definitions and requires every sharp stalk group completion on a monoscheme in the rule domain to be torsion free as well. It retains all fine torsion-free fans, including nonsaturated ones, and does not silently assume saturation. It is the local-lift formulation intended in ILO VIII 3.1.26--3.1.27 interpreted in the present DAG categories. Both hypotheses and the corrected rule domain are explicit in the statement and in `statement_dispute`. This is an auxiliary statement correction, not a change to Challenge.lean.

There is also a source error in VIII 3.1.15's assertion that an arbitrary morphism is smooth if and only if its sharpening is smooth: multiplication by 2 from the monoid group \(\mathbf Z\) to \(\mathbf Z\) sharpens to \(0\to0\), but is not a split inclusion with a free orthant/group factor. The proof uses only preservation of smooth maps and equivalence of smoothness for OBJECTS when their unit group is free. It never cites this false reflection assertion.

Downstream maintenance needed: `lem-trf-functorial-fan-desingularization` currently describes a monoscheme rule on ALL fine torsion-free monoschemes in steps 1--4 and invokes this node in step 5. Its construction may simply be restricted to the corrected domain here before applying the bijection; its fan conclusion is unchanged. I did not edit that parent's node. `def-trf-monoscheme-toric-realization` is also unchanged.

## Sources and searches

Read ILO, Travaux de Gabber, Expose VIII, printed pp.98--103 (3.1.1--3.1.29) and p.92 (Remark 2.3.5 in full). Lemma 3.1.25 provides the ideal/chart/tower route; 3.1.26 and Theorem 3.1.27 provide local lifting and finite-disjoint-union synchronization. Remark 3.1.28 confirms that the saturated version is intended. There is no Stacks tag for this monoscheme/fan theorem; no SGA source is used.

The new algebraic lemma makes explicit an ingredient omitted by the source's local-lift discussion. Its proof route for the next worker is: the exact sequence of groups \(0\to U\to P^{gp}\to B^{gp}\to0\) splits because the finitely generated torsion-free group \(B^{gp}\) has an integral basis. Lift that basis to \(P^{gp}\). The resulting group section carries \(B\) into \(P\): any such lift differs from an actual representative by a unit, and negative units still belong to \(P\). This gives \(P=B\oplus U\). The unit group is a subgroup of a finite-rank free abelian group and is itself finite-rank free. This argument is reported here only; the new node carries no proof. Its source is expressly qualified as an agent algebraic refinement of VIII 3.1.11/3.1.26, rather than claiming that the source prints this exact lemma.

Searched the whole DAG by ids, monoid/units/splitting, sharp direct products, source places 3.1.11/3.1.15/3.1.25/3.1.26/3.1.27 and tower gluing/synchronization. Ran blueprint_refs ancestor and searches for sharpening, monoscheme, synchronization, monoid, units, monoid.*unit, sharp.*quotient, and blowup tower; no blueprint node states the new lemma or the rule bijection. Read the relevant existing nodes listed below, including both affine fan section/Hom statements. Project declaration searches did not supply either new result. All Mathlib searches used msearch.py and were logged as returned. Both item and new lemma have two semantic phrasings, LeanSearch, Loogle and grep. The hits concern number-field unit groups, general group completion, units of products, ordinary scheme gluing and monoidal categories of sheaves, and do not state either result. The Mathlib affine-monoid Basic file only introduces the finite/cancellative/torsion-free class; it contains no splitting theorem.

## Not duplicates

lem-trf-fine-monoid-unit-splitting vs lem-trf-fs-face-sharpening: the existing result proves saturation, sharpness and freeness of localized sharp quotients for SATURATED monoids, but gives no section or product isomorphism; the new lemma allows nonsaturated monoids and explicitly proves a section when the sharp group is torsion free.

lem-trf-fine-monoid-unit-splitting vs lem-trf-log-chart-face-tor-comparison: that lemma assumes a chosen monoid section and gives a Tor comparison with log charts over a ring. This lemma supplies a section under purely monoid hypotheses and makes no Tor assertion.

lem-trf-fine-monoid-unit-splitting vs lem-trf-log-regular-sharp-chart: that lemma produces an etale log chart on a log regular fs scheme, not an isomorphism of a fine monoid with its units times its sharp quotient.

lem-trf-fine-monoid-unit-splitting vs lem-trf-fg-torsionfree-group-free: the existing theorem supplies bases for abelian groups; it neither constructs a monoid section nor identifies a positive submonoid with a product.

lem-trf-fine-monoid-unit-splitting vs def-trf-monoscheme-toric-realization: the definition describes the quotient by units and smoothness, but does not assert a splitting theorem. The new lemma supplies precisely the missing algebra and is neither the item nor any clause of its geometric/rule conclusions.

## Review by Q02

I read the ILO places above against the item and read the full statements of every cited DAG node, rather than using their internal proofs. I checked delivery-errors B through E as follows.

Step 1 uses the ideal/units/coherence definitions in def-trf-fine-fan-blowup and the sheaf quotient from def-trf-monoscheme-toric-realization. Unit stability, inverse image/image inversion and lifting generators are written out. They require no theorem about scheme ideals or flatness. This is elementary from the two quoted definitions; the inverse operations are sheaf-local.

Step 2 uses the precise unsharpened chart formula in def-trf-monoscheme-toric-realization and the saturated fan-chart formula in def-trf-fine-fan-blowup. The new splitting lemma applies because both ordinary and sharp stalk group completions are now assumed torsion free. The product saturation calculation is explicit. lem-trf-fine-monoid-finite-saturation states fineness of every saturated chart and localization compatibility. lem-trf-fs-face-sharpening states that its sharp localized group is free; it is applied only AFTER saturation. These statements actually give the claimed fineness and sharp torsion-freeness at later levels.

Step 3 uses the fraction-localization gluing instructions in the two definition nodes. I checked that the comparisons fix the fractions on pair and triple overlaps and that the inverse tower construction is an induction with a specified initial object and center at every stage. It uses no existence/uniqueness theorem hidden inside another node's proof.

Step 4 uses exactly the two smoothness definitions and the new product splitting. For objects, B=N^r and U=Z^s implies P=N^r+Z^s. For maps only the forward sharp implication is asserted. For contraction I checked the current definition carefully: a whole ideal on a nonsaturated object can give a nonidentity saturation and must be retained. The product calculation reflects saturation being an isomorphism, so both tower correspondences delete the same indices.

Step 5 expands rather than cites the source's surjection observation. Localness reflects a unit ideal. At a whole-ideal stage saturation of a smooth product is the product saturation, so a nonidentity initial saturation cannot disappear over a smooth surjection. Recursive blowup charts preserve the same product description. This proves that surjective smooth comparisons preserve every index. Identity functoriality implies assigned rules are contracted. Step 6 is then the elementary three-line disjoint-union argument of Remark 2.3.5(iii), using only the rule definition: adjoin X, use two surjections, restrict back to Y. It is not asserted as a new lemma node because it follows immediately from Step 5 and the definitions.

Step 7 constructs the lift of a fan rule, using the already proved center/tower comparison and object smoothness. It checks identity and composition at the level of ordered centers. There is no use of reflection of smooth morphisms.

Step 8 takes a SINGLE finite disjoint union of sharp affine lifts, not unrelated component towers. The existing affine localization statement identifies sharp local sections and germs. The torsion-free hypothesis is checked at every stalk, so these lifts really are in the corrected monoscheme domain. Unit isomorphism stages are retained on the restricted towers at this point.

Step 9 writes the overlap comparison omitted by the source. Minimal open neighborhoods are justified directly: finite generation makes a prime determined by the generators outside it, and their sum gives the basic open of all generalizations. The existing affine localization node gives the actual localized sharp sections B. The new unit splitting provides the two local lifts B+Z^s and their common product lift. The maps to L are smooth, and Step 6 gives equality of raw towers. Only after this equality are their sharpenings identified; all original stage indices are retained. Comparisons are identities on fractions and therefore satisfy the cocycle condition. No chart-section theorem is cited merely as a theorem about morphisms.

Step 10 uses the explicit gluing definition: ideals are tuples of sections whose restrictions match, and the blowup charts are the prescribed quotient gluing. This is repeated for the finite length n already supplied by R(L); it is not a claim that gluing separately contracted component towers is possible. Coherence and smoothness are local stalk tests. A globally removable stage would be removable on every component, contradicting the fact that R(L) is contracted.

Step 11 checks cover independence using the union of two finite covers. Equality on overlaps shows that a removable stage on one subcover is removable on the other; this is where the covering/surjectivity condition is needed. Thus the two ordered subsequences agree, including the possible initial saturation. The same product-lift comparison removes dependence on affine lifts.

Step 12 uses lem-trf-affine-fan-hom-universal for an actual Hom-to-sections bijection, and lem-trf-affine-fan-localization-sections for the identification of those sections with the sharp stalk on the smallest open. These are the statements required, not just full faithfulness. The smooth product localization formula is written explicitly, then the rule on the models supplies the local comparisons. Synchronization by a finite disjoint union retains their indices until the global contraction test. Finiteness follows since a finite union of finitely generated monoid spectra has finitely many points: membership in a prime is determined by a finite set of generators. The number of local comparisons can therefore be chosen finite.

Step 13 checks the composites directly on generated images and fraction substitutions; no unproved assertion that a comparison “transports” or “commutes” replaces the calculation. Deleting an isomorphism whole-ideal stage affects neither later centers nor their pullbacks. Step 14 checks BOTH inverse operations on a cover and its disjoint union, with the smooth-surjective comparison of Step 5 preventing index loss. Thus the bijection of rules includes the advertised identity/composition data and applies to fans lacking global monoscheme lifts.

For the new node I checked that it introduces P, U, B, their group completions, the section and the projection compatibility. Its statement contains no proof sketch, proof dependencies or disguised copy of the item's conclusion. Its definition dependency really defines each monoid notion. Searches and nonduplicate comparisons are above. Small cases: P=0, P=Z^s and P=N^r+Z^s give the claimed splitting; the nonsaturated P=<2,3>+Z still splits and its whole-ideal saturated blowup is nonidentity. Dropping sharp torsion-freeness fails for the displayed P in Z^2. Empty fans and length-zero towers are allowed; their cover/tower construction is empty and contraction is harmless. Overlap components where an ideal becomes the whole sheaf keep their unit stages until the global test, so unequal local tower lengths do not break gluing.

No step exceeds 2000 characters. I nevertheless inspected the chart, common-lift and cover arguments for concealed lemmas: the substantial standalone algebra is isolated as the new statement-only node; the rest is written in the steps as finite induction, elementary product calculations, generated-ideal identities and the definition's gluing. All citations have relevant verbatim quotations in citations.json. No duplicate tag-based source node, unsupported tool use, cross-unit proof substitution or source-lock violation is present. No second worker was started; this is the direct-delivery self-review authorized in the brief.
