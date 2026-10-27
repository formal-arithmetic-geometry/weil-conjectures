# Q47: lem-sfb-compact-generics-flat-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-compact-generics-flat-open.json: statement, split into five proof steps; no exact Mathlib match. The statement and statement dependencies are unchanged.
- citations.json: thirteen step/node records, each quoting the cited statement verbatim.
- searches.jsonl: actual search-command records. write_split.py is sandbox-only preparation scratch.

There are zero new nodes and zero new Mathlib leaves. Existing Mathlib leaves are reused.

## Attachments

None. Searched the project's WeilConjectures source both for the exact blueprint tag and for generic-flatness/flat-open concepts. GenericFlatness.lean and GenericFlatFinitePresentation.lean require an integral base and produce a nonempty open; these do not supply all the component generic points of an arbitrary reduced base. DescendFlatFinitePresentation.lean is the existing general descent tool, not a declaration of the item.

## WANTED

WANTED: David Rydh, Submersions and effective descent of etale morphisms, Lemma (3.5), printed p.12, for lem-sfb-compact-generics-flat-open; local archival PDF absent. Read the primary PDF online at https://davidrydh.se/papers/submersion20100305.pdf, page index 11. Nothing was downloaded into the repository. The lemma's statement asks for a dense qc open, and its proof explicitly obtains one containing all generic points. Also read its cited EGA IV_3 Corollary 11.3.2, printed p.133, from literature/ega/EGA-IV-3_PMIHES-28-1966.pdf using pdftotext.

## Corrections and source checks

No statement dispute: Rydh gives precisely the needed result, including the stronger generic-point containment in his proof. Finite presentation here includes both quasi-compactness and quasi-separatedness, as the unchanged item explicitly requires. The latter is needed to apply the existing qcqs limit-descent tool. Generic flatness for an integral base is not sufficient by itself, and no finiteness of the set of irreducible components was introduced.

The source's reference to EGA 11.3.2 is expanded using the existing local-ring affine-neighbourhood limit and flatness descent nodes. This is the same local-flat-neighbourhood argument, with the finiteness assumptions checked explicitly; it does not import a new generic-flatness theorem. proof_origin is agent because this is an explicit assembly from local Stacks statements, with Rydh's PDF only read online.

Read the latest blueprint direct-images proof, clause (3), and the unit and chapter records. The inherited chain's historical alteration/moduli description is not literally the latest direct-images paragraph, which now uses compactification and proper/open preservation. The current item's independent Rydh statement remains valid. No unit route or target is changed. blueprint_refs.py ancestor returns null; retained the existing null ancestor and full inherited place/via rather than fabricating an ancestor. Whole-blueprint searches for generic flat, flat neighbourhood, and generic stalk, and the whole-DAG searches, produced no exact replacement for this item.

## Mathlib searches

Ran the required command's LeanFinder, Loogle, grep, and LeanSearch searches and a second LeanFinder formulation. All services answered. Read each returned signature. The hits are flatness definitions/stalk criteria, flat implies universally open, fpqc/fppf descent, localization of flat modules, and generic-point topology; none proves existence of a flat open around all generic points of a reduced base. The grep had no hits. The item's preexisting search records are retained, and the five actual Q47 records are appended verbatim from searches.jsonl.

## Not duplicates

No new nodes. Reused the existing 00EU minimal-prime field node, 00ES components node, 01HV affine-stalk node, 0GWT local-ring-limit node, 04AI flatness-descent node, 01IT affine-basis node, qcqs permanence and affine qcqs leaves, the field-flat leaf, 004W component-cover leaf and 01IS sobriety leaf. No copy of a fact or of the item's flat-open clause was created.

## Review by Q47

I read delivery-errors B through E in both occurrences and checked the written item against them. There are no new statement-only nodes to audit, no new definitions and no Lean edits. Every non-elementary step is below 2000 characters and names its input statements. I opened and read the full statement of every cited node; citations.json quotes those actual statements, not their proofs.

Step 1 uses affine-opens-basis to choose W0, spec-irreducible-components-minimal-primes to identify the minimal prime, reduced-scheme for reduced sections, minimal-prime-reduced-localization-field for R_p being a field, and affine-open-stalk-localization for the actual stalk. These statements do not assume Noetherianity. The small topological comparison K intersect W0 is proved in the step: the closure of an irreducible enlargement would enlarge the component K. I read the local Stacks 00ES and 00EU statements and proofs and 01IT/01HV references. This avoids using the existing reduced-Noetherian total-fractions theorem outside its hypotheses.

Step 2 uses local-ring-spec-limit-affine-neighbourhoods for a genuinely directed system, its affine transition maps, qcqs stages and the specified limit, not merely for the existence of a canonical stalk morphism. I read its entire statement, including clauses (1)-(3), and the 0GWT proof's local-ring-limit sentence. The system is restricted to affine neighbourhoods inside the already chosen W0 by applying the node to W0 itself. The open restriction has the same local ring. qcqs-morphism-permanence (3) supplies finite presentation after base change; its clause (2) makes X0 qcqs over the affine W0. flat-field then applies to the whole limit morphism because step 1 proved its base ring is a field. No flatness of a morphism to a nonreduced artinian local ring is asserted.

Step 3 uses descend-flat-finite-presentation exactly with S0=Y0=W0, X0=h^{-1}(W0), and the directed system of step 2. I read local Stacks 04AI and its Situation 081D. All three original schemes are qcqs, transitions affine, and f0 is locally finitely presented, so its conclusion gives an affine stage containing eta. The base-changed arrow is the open restriction, by the defining pullback property. This is the only spreading inference and it is fully accounted for by the cited descent statement. The two general limit/descent tools are declared in split_report.tool_uses; no node in this unit states them.

Step 4 uses affine-scheme-qcqs only for quasi-compactness of the affine stages, and flat-morphism only for its local-ring criterion. The step writes out the finite-subcover argument on the subspace C_gen, the finite-union quasi-compactness argument, and the equality of local-ring maps on open restrictions. It does not claim that an arbitrary open of a qc scheme is qc or that an intersection of affines is affine. No extra theorem is hidden in the elementary gluing of flatness on these open restrictions.

Step 5 uses irreducible-components-cover for a component through each point and scheme-sober for existence of its generic point. Neither node is replaced by a definition of components. The closure inclusion proving density is then written explicitly. I read Stacks 004W and 01IS at their local labels. This also proves C is empty if its generic-point set is empty.

Small cases checked: C empty gives U empty; h with empty source is flat and the argument still applies; C the spectrum of a field gives a field limit and a permissible affine neighbourhood; a disconnected finite union of reduced components needs no single generic point; infinitely many components with quasi-compact generic-point subspace are covered by compactness of that subspace, not by a nonexistent finite-component enumeration. Nonreduced bases fail the field argument and are correctly excluded. No new hypotheses were inserted. There is no circular dependency on the item and no forbidden SGA source.

## Unfinished work

None in the mathematical split. Delivery checks are run with the authorized server tools; no local validator, compiler, Lake or build is invoked.
