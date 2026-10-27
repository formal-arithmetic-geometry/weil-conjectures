# Q124: lem-sfb-space-generator-detects-lower-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-generator-detects-lower-bound.json: item, statement unchanged; eight-step split of Stacks 0GFI.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-ext-window.json: statement, unsplit; no Mathlib match. Stacks 09MB(1).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-generator-thick.json: statement, unsplit; no Mathlib match. Stacks 0GFC.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-open-retract.json: statement, unsplit; no Mathlib match. Stacks 09IX.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-supported-koszul-low-localization.json: statement, unsplit; no Mathlib match. Supported Koszul localization input of 0GFI, using 08GG, 08HK and 0GEK.
- citations.json: an exact statement quotation for every step/node citation.
- searches.jsonl: searches recorded by the required launcher command. write_split.py is a sandbox-local generation script, not a project change.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, perfect generators and lower bounds, classical generators, and the relevant Stacks tags. Existing scheme-specific perfect generation and Hom-gap declarations do not state the algebraic-space criterion. No compiler, Lake, or Lean editing was used.

## WANTED

None. All source arguments are available in literature/stacks-project.

## Audit of the imported item and route

The item was unsplit, with empty proof and inherited searches. Its statement agrees with 0GFI(1),(2)/(3),(6), including the sign Hom(G[-i],E)=Hom(G,E[i]); no correction or STATEMENT-DISPUTED is needed. The source and statement dependencies are retained. The existing blueprint ancestor is null: blueprint_refs.py ancestor prints None. This is inherited metadata (also present in the reviewed sibling lem-sfb-space-compact-perfect-generator); I have preserved it and extended precise places rather than inventing an ancestor. I read only blueprint/latest for the current chapter, unit and direct-image proof (3). The long inherited chain serves the 0GFL relative-perfection input, and this item supplies its 0GFI lower-bound test; none of that unit's route is replaced.

There are four real supporting statements, not copies of the conclusion. The Hom-window lemma has no generator hypothesis and tests an arbitrary complex with a finite gap. Classical generation has no boundedness assertion. Open-retract extension has no target complex E or Hom-vanishing assertion. Supported Koszul localization applies to a specified elementary distinguished square and concludes an isomorphism of *truncated derived objects*, not boundedness of E. It packages the supported chart comparison used in the source; its internal proof remains for its future worker. No elementary truncation-invariance lemma was created: that three-line argument is step 4.

## Not duplicates

lem-sfb-space-perfect-ext-window vs lem-sc-perfect-ext-bounded-qcoh-vanishing: the existing node assumes a scheme with its Zariski quasi-coherent derived category; the new statement is for arbitrary qcqs algebraic spaces on their small etale structure sites. A scheme cover does not directly prove global Hom vanishing on a space.
lem-sfb-space-perfect-generator-thick vs lem-sc-compact-generator-ambient-thick: the existing theorem requires a supplied telescope and compactness hypotheses in a specified ambient subcategory; the new space theorem deduces thick generation from perfect weak generation without a supplied telescope. Its future proof may use that categorical tool after constructing the required telescope.
lem-sfb-space-perfect-open-retract vs lem-pc-supported-perfect-generator: the existing theorem constructs a supported generator on a scheme, not an extension of an arbitrary perfect object on a qc open algebraic subspace.
lem-sfb-space-supported-koszul-low-localization vs lem-sfb-space-generator-detects-lower-bound: the item detects a lower bound using a global generator; the new input constructs a perfect supported Koszul test for a distinguished square and only identifies low truncations of a localization unit.
lem-sfb-space-supported-koszul-low-localization vs lem-sfb-space-perfect-test-relative-perfection: the latter tests relative perfection for a flat locally finitely presented map, using every perfect tensor test over the base; the new statement has no such morphism, relative perfection, or base tensor tests and concludes only a square-local truncation comparison. Its source may mention 0GFI as a prerequisite, not as this statement.

Whole-DAG and blueprint searches were run for 09MB, 0GFC, 09IX, 0GEK, 0GFI, 08GG, 08HK, perfect complex, generator, classical, direct summand, bounded below, Koszul, and finite window. No existing node gives any of the four new assertions in the required generality. The Mathlib generator file defines classical generation, but supplies no weak-generator-to-classical-generation theorem for these algebraic spaces. Mathlib's generic truncation and projective-dimension hits do not prove the finite-gap assertion. The putative new representable-homological Mathlib leaf was dropped when existing exactness nodes were found; they are cited instead.

## Review by Q124

I read spaces-perfect.tex proposition-detecting-bounded-below (0GFI), the entire proof including the elementary distinguished-square induction, and checked its assumptions against the item. I also read the statements and proofs at lemma-ext-from-perfect-into-bounded-QCoh (09MB), remark-classical-generator (0GFC), lemma-direct-summand-of-a-restriction (09IX), lemma-bounded-below-truncation (0GFG), lemma-pushforward-with-support-in-open (08GG), lemma-pushforward-perfect (08HK), and perfect.tex lemma-orthogonal-koszul-second-variant (0GEK), including its affine Situation. These are the sources of the four new nodes. The supported node preserves the whole comparison in the derived category. In its intended proof, the finite principal-open covering gives the Koszul complex, 08HK makes its supported pushforward perfect, 08GG identifies it with extension by zero, and the extension-by-zero adjunction gives Hom on V. Apply 0GEK to E restricted to V. Etale restriction/base change and the covering U,V identify the canonical truncation map on W; it is already the identity on U. This is strictly the localization part of 0GFI, before any boundedness deduction.

For step 1, the newly stated 09MB lemma says exactly that Hom vanishes when cohomology vanishes throughout a fixed interval. The computation q+j<c for j<c-b checks the cohomological sign. Step 2 uses the actual evaluation isomorphism in lem-sfb-ringed-site-perfect-duality and the all-integer H^j/Hom identification in lem-sfb-derived-internal-hom-sections-model; these are valid on small ringed sites without boundedness. It does not cite a definition of internal Hom in place of the theorem.

For step 3, I checked lem-weil-pbc-hom-out-of-triangle-exact: it gives factorization exactness for Hom(-,W), and rotations supply the adjacent terms. Together with the explicit finite-sum/retract/shift calculations this verifies thickness, then the new 0GFC statement puts every perfect object in that thick class. Step 4 uses the new finite-window lemma, the actual Hom-into-triangle exactness statement of lem-weil-pbc-hom-into-triangle-exact, and def-sbc-standard-tstructure-derived-category, which explicitly gives the standard truncation triangle and its cohomological support. It proves truncation invariance instead of introducing another node.

For step 5, lem-sfb-space-qcqs-distinguished-square-induction states the exact three-vertex induction premise used here, including affine V and the empty affine case. The existing lem-sfb-affine-etale-derived-module-realization is valid for every commutative ring, not just Noetherian rings: it states the equivalence, exact faithful realization, and quasi-inverse RΓ. Together with the global-Hom sections model with source O in degree zero it proves the affine base case directly. No unsupported comparison of etale perfect objects with Zariski perfect objects is needed.

Step 6 uses exactly the new supported Koszul localization statement. Its perfect B_W is among the tests, so its eventual vanishing hypothesis is supplied, and its conclusion is precisely the canonical derived isomorphism needed. Step 7 uses lem-sfb-space-derived-pushforward-coproducts only for its explicit landing-in-QCoh clause; i is qcqs because U is quasi-compact open in qcqs W. The canonical derived adjunction and exact restriction come from lem-sfb-space-derived-etale-chart-calculus. The new 09IX node extends each arbitrary perfect A on U as a retract of i*Q; precomposition gives the displayed retract of Hom groups. This spells out the missing passage instead of assuming that restriction of the original generator generates. This stronger induction step needs only the hypothesis for U, which is allowed by the three-vertex induction premise.

For step 8, lem-sc-bounded-below-injective-resolution is a ringed-site theorem (not the narrower scheme version), and explicitly supplies a bounded-below K-injective representative. Applying i_* to it preserves zero terms and computes Ri_* by its prescribed resolution construction. The truncation comparison then gives the explicit minimum bound. The stated induction property is now verified for every object in the domain of the induction lemma, and the all-perfect tests from step 3 give the converse. Hom exactness and bounded-injective resolution are declared generic off-unit tool uses in split_report; no tool_uses field is written.

I checked B--E: all new nodes introduce their objects and notions, have no proof or proof dependencies, and carry searches and exact source tags; no definition has been replaced or created. The item has exact proof_deps equal to its step uses. citations.json quotes whole statements verbatim, after I read them, rather than claiming something present only in their proofs. No step is over 2000 characters. No hidden induction or comparison remains in the assembly steps; the nontrivial supported comparison is explicitly a prerequisite.

Edge cases: X empty and A=0 give only the zero complex. On Spec(A), G=O gives ordinary module-cohomology detection; shifting G changes only the bound, agreeing with step 3. If the distinguished-square complement is empty, one may choose f_1=1, so B=0 and U=W and the localization comparison is the identity. If U is empty, choose the empty list: B=O_V, V maps isomorphically to W, and low Hom vanishing forces tau_le_a E=0. The supported construction imposes no regular-sequence hypothesis: a Koszul complex of any finite list is perfect, and the orthogonality statement in 0GEK needs no regularity. Retraction arguments require only rs=1, not a chosen complementary summand. No uniform bound over all perfect tests is assumed.

## Unfinished work

The four new nodes remain statement-only, as required for a one-level split. No Lean proof has been attempted. Mechanical dry-run validation and push are performed with the required delivery tool.
