# Worker report — repair of returned head 2fd3511948

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-fd-weil-pullback-local-frobenius.json`: eight-step repair; the item statement is unchanged; no new nodes and no Mathlib leaves.
- `citations.json`: nineteen verbatim statement quotations, one for every citation in every step.
- `report.md`: this repair report. The preceding report is retained in `report.before-repair.md` as superseded historical work, not as the review of this repair. Search output is retained in `searches.jsonl`.

## Attachments

None. I repeated the item-id searches in the read-only slopmaster2 and upstream-master `WeilConjectures/` trees and read the relevant portions of `WeilSheaf/StalkUpperStar.lean` and `StalkCharpoly.lean`. The concrete `WeilSheaf` pullback/Frobenius declarations do not identify their category with this item's raw rationalized/common-stage category, so they do not attach the whole item. The upstream reference is not treated as proof completion.

## WANTED

None. The main-20261015 realified-kernel statement and proof, Deligne's Weil II PDF, and Bhatt–Scholze's pro-etale PDF are present and were read. I read Deligne (1.1.3), (1.1.7)–(1.1.10), printed pp. 150–151 (PDF pp. 15–16), and Bhatt–Scholze Definition 6.8.10, Proposition 6.8.11(3), Proposition 6.8.14(2), and Remark 6.8.15, printed pp. 60–62. The precise comparison normalizations are the explicitly agent-formulated DAG statements, not assertions attributed verbatim to those papers.

## Problems checked and corrections

The current repository item remains unsplit with an empty proof; the retained sandbox was the returned four-step split. I retained its statement, recorded searches, blueprint ancestry, and the substantive finite-field/eigenvalue arguments, and replaced its unsupported coefficient-category inferences. The new split follows the same Step 2 of `lem-fd-realified-kernel-real` and the same Fourier argument of the unit; it does not alter a chapter or unit route.

1. **C3/C4/E6, finite versus rational stalk coherence.** Removed `lem-trf-proetale-pullback-stalk-coherence` entirely from the proof. Step 3 constructs the rational stalk isomorphism as the inverse of pullback composition followed by the point-fibre functor. Its compatibility with finite scalar extension is the equation in `lem-trf-integral-pullback-comparison-realization` together with `lem-weil-point-sections-scalar-extension`. Step 4 writes the actual naturality square involving the Frobenius exchange beta, step 5 composes it with the iterated Weil structure, step 6 proves the power recurrence, and step 7 applies the explicit rational local-transport scalar equation. No rational claim is obtained by applying a finite-ring statement, and no invertible integral Weil lattice or finite Tor-amplitude condition is assumed.
2. **C4, rational heart preservation.** Step 1 is no longer marked elementary. It cites `lem-a1-constructible-pullback-t-exact`, whose statement explicitly uses this item's rationalized/common-stage categories, derived pullback and standard heart, and states t-exactness and the point-fibre clause at both coefficient stages.
3. **Creation metadata requested in the return.** The sandbox item now has `created.item=lem-fd-weil-pullback-local-frobenius`, as requested. However, `deliver.py` lines 123–144 and 198–205 deliberately overlay only `SPLIT_OWNS` for an existing node, and `tools/node_fields.py` lines 30–35 declares `created` maintainer-owned. The current repository origin still has `created.item=lem-fd-realified-kernel-real`, the N3 parent which originally created this node. Consequently the required delivery tool discards the sandbox correction and retains that origin metadata. This requires a maintainer metadata correction, or an authorized tool correction, if the returned review really requires the new self item. I have not edited the repository, launcher or tools or bypassed the overlay. Historical `blueprint.from.node=lem-fd-realified-kernel-real` is retained, as required by the blueprint ancestry contract.

## Not duplicates

No new nodes. Whole-DAG statement searches found the precise existing rational t-exactness, coherent scalar/composition, point-sections scalar-extension and point-transport statements; these are cited rather than copied into new lemmas. `tools/blueprint_refs.py search 'pullback Frobenius'` returned zero blueprint matches, and the ancestor command confirms the original realified-kernel ancestor. The existing `lem-trf-frobenius-degree-formula` is a finite-coefficient trace statement, not the rational morphism-functorial assertion here. `lem-trf-rational-local-frobenius-powers` imposes a finite Tor-amplitude condition on reductions; I read it and deliberately do not cite it, since the item has no such hypothesis. The needed recurrence is written out from naturality and the definition of iterated structure.

## Mathlib searches

The retained item's searches were kept. This repair ran and read the logged grep `WeilSheaf|frobenius.*stalk|stalk.*frobenius` (zero hits), Loogle `"Frobenius", "stalk"` (zero hits), LeanFinder for coherent rational Weil pullback and the residue-degree power (residue-field map comparisons, no common-stage Weil sheaf result), and LeanSearch for pullback of constructible Qbar-ell Weil sheaves (topological stalk pullback, finite-field Frobenius and scheme residue/fibre declarations). These are not statements about the coefficient category and Weil structure in the item. A second phrasing is present in the retained search record and in the differently phrased semantic searches of this repair. No new nodes require searches.

## Tool uses

`split_report.tool_uses` declares the generic coefficient tools from other units: `lem-a1-constructible-pullback-t-exact`, `lem-trf-integral-pullback-comparison-realization`, `lem-weil-point-sections-scalar-extension`, `lem-weil-frobenius-point-transport-natural`, and `lem-trf-local-frobenius-transport-normalization`, together with the closed-point residue-field criterion. They supply the coefficient and point-fibre interfaces below the unit's Fourier argument. None replaces the realification argument or assumes its conclusion.

## What remains unfinished

No new mathematical statement dependencies were created. The requested creation-metadata correction cannot pass through the current required delivery overlay, as detailed above. Mechanical check results are recorded below after running the required dry run.

## Review by Q98

I read the item's current repository version against the retained returned version, the chapter and unit records, and the main-20261015 realified-kernel source, especially its Step 2 sentence about the eigenvalues alpha^e lambda. The item is the rational functorial justification of that sentence; its hypotheses are an arbitrary morphism of separated finite-type schemes over the finite field and a constructible rational Weil sheaf. No smoothness, properness, global lissity, integral Frobenius stability, or finite Tor-amplitude of reductions has been added. The source's geometric Frobenius convention agrees with Deligne (1.1.7) and the return construction in `def-weil-local-frobenius-trace`.

For step 1 I opened `lem-a1-constructible-pullback-t-exact`: its statement names the exact same raw rational/common-stage category and standard heart, and explicitly restricts derived pullback to an exact heart functor. I also read the derived-operation definition and the canonical integral comparison statement to construct the induced Weil structure using the actual commuting geometric Frobenius square. All schemes involved are finite type over k and ell is invertible.

For step 2 I read both directions of `lem-kun-closed-point-field`(a). The source and target here are finite type over k0, so the criterion applies at both z and x. The residue map is a field embedding over k0. The positivity and cardinality calculations use bases in finite extensions; e=1 and d=1 require no exclusion.

For step 3 I read the complete statement of `lem-trf-integral-pullback-comparison-realization`, including its final scalar/composition equation, identity and tower conditions, rationalization clause and explicit absence of a finite Tor hypothesis. The maps zbar, f and their composite are scheme maps on which ell is invertible, precisely its hypotheses. `lem-weil-point-sections-scalar-extension` supplies the sections/fibre comparison, not just an unrelated tensor comparison. The common-stage definition explicitly represents finitely many morphisms and inverse equations after a finite extension, which is all the choice of E uses. This repairs the exact coefficient-category mismatch of the return.

For step 4 I opened `lem-weil-frobenius-point-transport-natural`(2) and `lem-trf-local-frobenius-transport-normalization`. The former is natural on rational categories and explicitly coefficient-compatible; the latter defines the local return maps, states their naturality and scalar equation without a Tor condition. Applying naturality to the composition comparison at s, and then rebracketing the pullbacks by the associative canonical families, gives the displayed square. The return identities are identities of scheme morphisms with the source Frobenius retained, not the false equality gx^n zbar=zbar.

For step 5 the same composition statement supplies naturality and associativity for the induced Weil structure. I checked the domains of beta, c and each J(theta): multiplying the step-4 square by Jx(theta^[n]) gives exactly c Fz on the left. This is a calculation with the specified transformations, not a claim extracted from a cited proof.

For step 6 I checked the ordered product for the iterated Weil structure and the ordered list for the iterated point transport in their definitions. The displayed naturality equality moves theta^[rd] across the d-fold transport, giving a left product by Fx at each induction step. The base r=1 is the definition of Fx. The step applies to any rational Weil structure, so it avoids the extra hypothesis in the nearby rational-local-powers node. This is a short formal composition calculation; it hides no new comparison lemma.

For step 7 I reread the explicit scalar equation at the end of the local-transport normalization statement. Together with the comparison equation and point-sections scalar associator already cited, it identifies every factor of the Frobenius equation after a common finite extension. The point-fibre part of the t-exactness statement justifies degree-zero cohomology at Qbar ell. This is the missing common-stage/Frobenius argument, now stated with its actual maps and hypotheses.

Step 8 is ordinary triangular-matrix linear algebra. Besides the identity map, constant sheaf and zero sheaf, I tested the matrix with eigenvalues 1 and -1 and e=2: both resulting eigenvalues are 1 and the multiplicity stays two. For a scalar lambda the formula is lambda^e, covering arbitrary nonunit Weil eigenvalues without assuming an integral invertible lattice. I checked the finite extension example Spec F_(q^(de)) to Spec F_(q^d), where the return exponents are de and d. The proof keeps source reparametrizations throughout, and all cited statements are used for what they state. No new node, no hollow definition, no SGA citation and no Lean change is introduced. Every non-elementary step is below 2000 characters. The earlier report's claim that finite-ring coherence directly supplied the rational result is superseded by this repair.
