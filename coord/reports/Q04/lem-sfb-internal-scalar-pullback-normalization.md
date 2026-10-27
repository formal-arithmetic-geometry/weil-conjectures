# Worker report

Item: lem-sfb-internal-scalar-pullback-normalization. Group: Q04. Stage 1 only. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-internal-scalar-pullback-normalization.json: existing statement, now split in eight steps; no Mathlib match.
- citations.json: one verbatim statement quote for each step/node citation, including its hypotheses.
- report.md: this report.

No new nodes, Mathlib leaves, Lean files or unit records. Auxiliary writing scripts and the actual msearch log remain in the sandbox. The item's statement, statement dependencies, source and blueprint ancestry are unchanged. All original Mathlib searches are retained, with the additional actual searches appended.

## Attachments

None. I searched WeilConjectures for the blueprint tag and scalar/pullback/tensor normalization terminology. ChangeOfCoefficients.lean contains ordinary pullIso and a derivedPullIso with a global exact-extension assumption; these do not prove this item, which has no flatness assumption and additionally requires tensor normalization and identification of independent adjunctions. InternalScalarTensorComparison.lean under Sheaf also assumes exact scalar extension for its derived comparison and concerns strong monoidality rather than the present restricted tensor comparison.

## WANTED

None. All sources used are present locally.

## What was wrong and what changed

The imported item had no proof or proof dependencies. I retained its full statement and supplied the construction and normalization arguments. In particular, the tensor comparison uses a K-flat source and the possibly nonflat coefficient module in degree zero. I did not infer that scalar restriction preserves K-flatness or that scalar extension is exact. Both interface equations are checked on every complex, not just representatives, by naturality and cancellation of the derived image of a resolution. The ordinary geometric comparison is identified with the specified inverse pullIso by its actual adjunction conjugate, before its localization is used.

The blueprint's scalar-six proof cites 06YV for inverse image and composition; I used the actual ringed-topos lemmas 0G7E and 0D6D named by the item. This corrects the reference, with no change of mathematical route. The node realizes the integral unit's scalar-refined reduction comparison in paragraph (1) and canonical-map compatibility in paragraph (3); it is not the unit's key statement, so no unit realization fields are written.

## Search record and reuse

The original node's existing searches remain intact. Additional searches were run through the required msearch.py wrapper, with their exact queries and actual results in searches.jsonl and mathlib_searches. The two distinct semantic phrasings returned ordinary ModuleCat scalar-unit/counit and scalar-composition lemmas. LeanSearch returned ordinary sheaf pullback and change-of-rings constructions. Loogle returned no hit. The first grep returned no hit, and the second found SheafOfModules.restrictScalars and pullbackComp. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean:36 and PullbackContinuous.lean:167 and the ordinary ModuleCat change-of-rings source: these do not state the unbounded internal comparison or the universal normalization equations. An accidentally repeated first semantic query is logged honestly with its second actual response, rather than represented as a different search. No new node needs an absence claim.

Whole-DAG searches covered the node id, normalized scalar comparisons, internal scalar operations, tensor normalization, K-flat comparisons, and Stacks 0G7E/0D6D/07A6. blueprint_refs.py ancestor returned det-thm-sfb-proper-base-change-integral. Whole-blueprint searches for internal scalar, tensor normalization and K-flat normalization found no blueprint node stating this full normalization assertion. Existing generic nodes are cited instead of copied into new nodes.

## Not duplicates

No new nodes were created. The existing quotient-section tensor normalization is specialized to integral finite quotients and depends on the parent of this item, so it is not used. The generic K-flat scalar comparison is used for its smaller ringed inverse-image/mate assertion, not duplicated. Scalar-adjunction, geometric-operation and tensor equivalence nodes each give only the comparison input described below; their conjunction does not itself construct the two present maps with both interface equations.

## Review by Q04

I read the current integral proper-base-change proof paragraph (1), paragraph (3), the scalar-six pullback proof (1), and the unit and chapter records. The unit's route is the finite/integral/rational reduction route. This item only supplies the ordinary unbounded scalar comparison used by the integral step. The imported statement is mathematically consistent and needs no STATEMENT-DISPUTED correction.

For sources, I read sites-modules.tex Tag 03EK's bilinear tensor construction and Tag 03EL (lemma-tensor-product-pullback); sites-cohomology.tex Tag 06YS (lemma-K-flat-resolution), 06YT (lemma-derived-tor-quasi-isomorphism-other-side), 06YU's derived tensor construction, 0G7D (lemma-factor-through-K-flat), 0G7E (lemma-pullback-K-flat), 0D6D (lemma-derived-pullback-composition), 07A6 (lemma-adjoint), 07A4's K-flat tensor-pullback proof and 0FPI (lemma-adjoints-push-pull-compatibility). I also read categories.tex Tag 0B65's mate/counit square. No SGA reference or trace argument is used. There are no new nodes needing additional sources.

For step 1 I opened all four comparison statements: pe-internal-section-tensor-comparison explicitly preserves total tensor, flatness and K-flatness; internal-section-scalar-adjunction explicitly identifies scalar operations, the specified adjunctions and the derived representative maps; pd-section-derived-pushpull-normalization explicitly identifies independent derived geometric adjunctions with their resolution comparisons; pd-section-derived-tensor-normalization explicitly includes the localization tensor map and regular unit. I added sk-def-sfb-sheaf-tensor to discharge the sheafification, closed tensor and monoidal-local-equivalence hypotheses rather than silently assume them. All sites are small relative to the given coefficient universe and both coefficient rings are commutative.

For step 2 I checked that extension-tensor-comparison actually states restricted scalar extension is the sheaf tensor, rather than merely defining extension. The pe tensor and scalar-adjunction statements identify its pure generators under the fixed equivalences. Symmetry gives the stated direction s tensor x to x tensor s; the balancing identity and inverse are written out. The degree-zero scalar has no sign. The interface definition supplies exactly the ordinary comparison and single-factor total convention used here. This is an elementary composition of the cited maps, not a new lemma.

For step 3, derived-change-of-rings gives the invertible scalar computation on K-flat inputs. The native-tensor statement explicitly allows either input to be K-flat, so it applies to P and VS[0] even when a is a nonflat quotient. The site-derived-tensor-descent statement supplies the equivalence from localized flat-term K-flat complexes; descending this natural representative isomorphism in one variable uses that equivalence. The scalar and derived tensor comparisons from step 1 give precisely the internal functors, rather than a separately chosen model. No target regular module is assumed flat over the source ring.

For step 4 I opened the K-flat-resolution statement: every unbounded complex has a flat-term K-flat resolution. The all-complex TensorNormalized equation was checked against its actual Lean definition in InternalDerivedScalarComparisons.lean. Naturality produces equality after precomposition with VD_a(Qq), which is invertible; q tensor VS need not be a quasi-isomorphism. Thus cancellation proves the equation at an arbitrary complex. This is a two-line naturality argument from the cited resolution and interface, kept elementary.

For step 5, coefficient-morphisms says alpha is a component of one natural isomorphism, not merely that there exists some ring isomorphism; naturality at a is the required commuting coefficient square. The internal inverse-image comparison explicitly identifies scalar actions and reconstructed ring operations. The generic K-flat scalar-comparison statement contains the ordinary coequalizer comparison and preservation of the scalar unit; I apply it first to actual inverse-image rings, then transport along alpha. Commutativity and invertibility of both alpha maps are present. This avoids applying a fixed-ring assertion to unrelated coefficient rings.

For step 6, I opened internal-module-operations-transport and checked it identifies ordinary geometric units/counits; internal-section-scalar-adjunction does the same for scalars. comap-lower-star-iso states the common underlying action of the restriction/direct-image square. The conjugate-iso-unit-equation gives uniqueness of the unit-compatible conjugate. On the unit generator x maps to 1 tensor x on each route; applying the counit gives the same scalar action. This proves that the chosen balanced map has the specified conjugate, so its inverse is pullIso. I read ChangeOfCoefficients.lean:158 to check its orientation. This is an elementary adjunction calculation using the cited normalizations; no uniqueness of arbitrary isomorphisms is asserted.

For step 7 I verified ringed-pullback-preserves-kflat requires both K-flatness and flat terms, and explicitly requires no flat structural map. Both hypotheses hold for the selected representative, and both are preserved at the intermediate coefficient-extension and geometric-pullback stages. The generic scalar normalization theorem states the inverse localized ordinary map is the scalar mate; hence its inverse has exactly the desired direction. The internal scalar and geometric derived equivalence statements preserve the computation comparisons, giving PullNormalized with inverse pullIso. Naturality and cancellation extend the equation from the resolving class to all complexes just as in step 4; no claim that the ordinary scalar extension of a resolution remains a quasi-isomorphism against an arbitrary complex is needed.

For step 8, the adjunction clauses come directly from the two specified comparison statements, rather than from mere uniqueness of left/right adjoints. Representative independence and naturality use the explicit localized representative equivalence already cited. I checked the identity coefficient map and identity f, the zero coefficient ring, empty schemes, unbounded complexes, and a nonflat quotient such as Z to Z/n. In each case the maps have the stated sources and targets; the argument uses K-flat representatives, not flat coefficients or boundedness. The degree-zero swap has no Koszul sign.

I checked delivery-errors B–E against every step. No new-node self-containedness, duplicate, or relabelled-clause issue arises; all non-elementary facts have nodes, and citations.json quotes their actual full statements. I traversed all candidate dependency closures and found no path back to this item. All off-unit proof tools are declared in split_report.tool_uses, with their role in this unit explained. No proof step exceeds 2000 characters, and no hidden standalone comparison is passed off as a long routine step. I corrected the missing explicit sheaf-tensor hypothesis citation during this audit.

## What could not be finished

Nothing in the stage-1 split. No Lean proof or compilation is part of this delivery.

## Validation

The server review_split check passed before this report was written. Final delivery preflight and DAG validation are run by the required deliver.py dry run.
