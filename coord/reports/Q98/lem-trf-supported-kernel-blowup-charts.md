# Q98: lem-trf-supported-kernel-blowup-charts

## Files written

- dag/nodes/sec-trace-formula/lem-trf-supported-kernel-blowup-charts.json: statement, split into five steps; not a Mathlib leaf. Statement and statement dependencies retained.
- citations.json: one verbatim statement quotation for each of the 14 step/node citation pairs.
- report.md and searches.jsonl: report and actual search log.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the notions supported kernel, blowup charts, and power torsion. The finite-structure supported-unit-kernel lemma concerns annihilation under a closed immersion, not this statement. Submodule.powTorsion_eq_ker_localization already belongs to lemma-nagata-power-torsion-kernel-localization; it supplies only the algebraic kernel assertion, not an attachment for this item.

## WANTED

None. All literature used is present.

## Audit findings and corrections

The item was statement-only, with no proof. Its statement is correct, including the explicit absence of regularity and torsion-free hypotheses: this item only identifies two kernels, whereas the later equality of the two power-torsion modules in Tag 080H requires additional assumptions. No statement change or route change was needed. No repair note exists for this item.

Read the chapter and unit records, the three levels in SETUP, and the current latest blueprint chapter/unit and locality statement/proof (main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). The item's provenance is a supporting lemma for the existing Orgogozo/strict-transform chain. Its source is Tag 080H's affine reduction; this split does not change the fixed chapter or substitute another argument for a unit step.

Searched the whole DAG by tags 07ZP and 0804 and by supported-section, affine-pullback, localization, and chart terminology. Ran blueprint_refs ancestor and searches for supported sections, supported, blowup, affine blowup, and power torsion. Reused the existing nodes instead of creating principal-support, tensor-associator, or chart-specialization duplicates. Read the existing statement-level affine pullback formulas instead of using their proofs as black boxes.

Mathlib searches were run with the required msearch command and their exact tool/query pairs copied from searches.jsonl. Two semantic phrasings returned structure-sheaf restriction vanishing and tilde construction, not the combined blowup statement. The returned structure-sheaf lemma in Morphisms/QuasiCompact.lean was read at lines 250 ff.; its section is a ring element, whereas this item concerns arbitrary modules. The tilde constructor and toOpen at Modules/Tilde.lean lines 150 ff. construct the sheaf, not the two supported subsheaves. Localization commuting with kernels in Algebra/Module/LocalizedModule/Submodule.lean lines 359 ff. likewise does not supply blowup geometry. The original item's recorded searches are retained.

## Not duplicates

No new node pairs to compare: this delivery creates no nodes. The existing supported-section theorem lem-trf-supported-sections-quasi-coherent is used on each chart; prop-nagata-affine-blowup-chart-cover supplies the cover. The full flat-pullback kernel theorem is not used, since the present base change need not be flat.

## Review by Q98

I read divisors.tex Tag 0804 (lemma-blowing-up-affine), including its proof by standard degree-one Rees charts, and Tag 080H (lemma-strict-transform-different-centers), especially the reduction of clause (2) to a-power and xa-power torsion. I read properties.tex Tag 07ZP (lemma-sections-supported-on-closed-subset), both clauses (2)-(3) and the restriction-kernel sequence in its proof. I checked Schemes 01I4/01JQ for the actual tensor-product fibre scheme, 01JY for open base change, 01I9 for pullback of an associated module, and 01IA for reconstruction from affine sections; Modules 01BG confirms pullback quasi-coherence. There are no new-node sources to check.

Step 1 uses exactly the finite cover in prop-nagata-affine-blowup-chart-cover, the affine-local quasi-coherent definition pqf-def-coherent, open-immersion base change, the fibre-product universal property, and the affine-spectrum tensor-product formula. The open-chart intersections are identified by their projections; covering is checked pointwise. No quasi-separatedness of X or affineness of intersections of arbitrary affine opens is assumed.

Step 2 uses lem-weil-pbc-module-pullback-quasi-coherent to justify applying affine reconstruction. The statement of lem-weil-pbc-module-pullback-affine-sections applies to any affine pair W over U, and gives the actual tensor section map and naturality; it requires no flatness. The Mathlib affine tilde-Gamma node states both reconstruction and the unit isomorphism. The extra tensor presentation is proved by two displayed inverse maps, so no new lemma is hidden in an associativity assertion.

Step 3 uses only the definition of the chart subalgebra: its fractions satisfy a(f_j/a)=f_j in A_a. This remains an equality in the subalgebra, even when a is a zero divisor. Both containments IB=(a), extension to C, and prime-containment tests are written out. This is an elementary step rather than a new node for one clause of the item.

Step 4 checks the actual retrocompactness hypothesis of lem-trf-supported-sections-quasi-coherent. On every affine open the complement is a principal open, homeomorphic to a spectrum by lem-weil-pbc-spec-localization-away-basic-open; the cited quasi-compact-spectrum node states precisely its needed compactness clause. Applied separately to (a) and (xa), the supported-section theorem gives quasi-coherence and sections killed by a power of the defining ideal. Since that ideal is principal, its power annihilation is equivalent to the definition in def-nagata-power-torsion. This is a theorem citation, not an inference of the support theorem from a definition.

Step 5 uses clauses (1)-(3) of lem-weil-pbc-affine-tilde-gamma-adjunction: the Hom bijection, unit, and quasi-coherent counit. Naturality of that counit identifies the inclusion itself with the associated map, not just an abstract isomorphism of the two sheaves. This addresses the inclusion clause in the item. All cited statements were opened and their used portions appear verbatim in citations.json.

I checked delivery-errors B-E against the written split: no new unsearched or non-self-contained node, no copied proof masquerading as a statement, no unsupported non-elementary comparison, no off-unit replacement route, and no circular citation. Three generic off-unit tools are declared in split_report.tool_uses; the remaining off-unit facts are definitions or Mathlib leaves. No step is longer than 2000 characters. During the source audit I removed an incorrect tentative principal-localization tag (00D4 is a directed-system definition); the proof now names only the verified compactness tag and the existing localization node.

Small cases checked: I=0 makes all blowup charts zero rings and the assertion vacuous on the empty blowup; I=A gives a unit chart and zero exceptional support; zero C and zero N cause no exception. For t=0 or nilpotent, D(t) is empty and the supported module is all N. For t a unit it is zero. Taking x=0 makes the second supported module all N, while x a unit makes the two supports agree. Arbitrary x-torsion and nonflat R over A are allowed throughout, since no tensoring of a monomorphism was used.

## Unfinished work

None within stage 1. No Lean was written or compiled. The accepted split still leaves its already existing dependencies to their own workers.
