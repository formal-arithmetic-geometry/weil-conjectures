# Stage-1 split: lem-trf-open-hom-mate

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-open-hom-mate.json`: statement, split in four steps; no Mathlib match. The statement and all six statement dependencies are unchanged.
- No new DAG nodes or Mathlib leaves. `citations.json` records a verbatim statement passage for every step citation. The search output files and `searches.jsonl` retain the five searches made for this item.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` source for the blueprint tag and for exceptional/internal Hom, open mates, and internal-Hom comparisons. The closest concrete declaration, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom` in `WeilConjectures/SixFunctors/Etale/Derived/BoundaryDuality.lean:58`, supplies only existence of an isomorphism on the etale derived categories, not this equality of normalized maps and sections. The ordinary pro-etale sheaf internal-Hom pullback theorem and the abstract lax-monoidal `ihomComparison` lemmas also do not state the item. No attachment is claimed.

## WANTED

None. The source PDF, Stacks source, current blueprint, and relevant Lean source are available locally.

## Corrections and source audit

There was no statement error. The imported item was a statement-only auxiliary node extracted from returned step 2 of the trace-class open-restriction proof; its proof was empty. I supplied the argument rather than a new node restating its conclusion. In particular the proof does not identify derived morphisms by their stalks, and it does not use ordinary restriction as if it commuted with internal Hom at a closed point.

The main-20261015 proof of `lem-trf-local-term-locality`, paragraphs (1)-(2), uses the Varshavsky contracting-correspondence/normal-cone route. This auxiliary item realizes the open-support section comparison used through `lem-trf-trace-class-open-restriction` step 3. The unit and chapter routes are unchanged; the item is not their key statement, so no unit file was changed. The ancestor search gave `lem-trf-local-term-locality`, as already recorded. Whole-blueprint searches for exceptional internal Hom and open restriction found no second statement of this equality, so `same_as` stays empty.

I read both the inherited Mathlib search hits and the five fresh search outputs. LeanFinder's two phrasings returned structure-sheaf restriction or module scalar adjunctions. Loogle returned `Adjunction.homEquiv` and its unit/counit formulas. LeanSearch was available on this run and returned ordinary open-immersion structure-sheaf formulas. The fresh grep returned mentions of Verdier triangulated categories, not exceptional internal Hom. These are insufficient to make the item a one-line Mathlib specialization: the exceptional comparison must first be identified with the ordinary restriction/tensor normalization. The inherited search records are preserved; the fresh raw results are additionally recorded without changing their verdict to a fictitious service failure or a match.

## Unfinished work

None in this one-level split. The cited nodes remain separate existing work items, where not already split; no assertion of their Lean completion is made.

## Not duplicates

No new nodes. The existing `lem-trf-exceptional-internal-hom-exchange` gives the canonical isomorphism for general morphisms, but not the present open-section normalization. `lem-sf-open-tensor-normalization` gives the inverse open projection's adjoint, which the proof uses directly. `lem-trf-exceptional-tensor-open-restriction` compares exceptional tensor maps across a general open square; it does not give a second statement of this section equation, and is unnecessary for the short triangle calculation here. `det-sf-mate-open-restriction` concerns condensed/localizing coefficient categories and geometric restriction, not the current internal-Hom section identity. None was copied into a new node.

## Review by Q40

I read Varshavsky's local PDF, printed pages 5-6, §0.3(a)-(b), including the full definitions (0.2) and (0.3). These fix the direction that matters: the paper's map (0.3) goes from exceptional pullback of internal Hom to internal Hom of ordinary/exceptional pullbacks; the item denotes its inverse by E_j. I also read Stacks `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`, statement and proof, and `sites-modules.tex`, Tag 0E8I with the same label, statement and proof. Those tags give the projection isomorphism; the stronger specified open-unit normalization is taken from the *statement* of the existing `lem-sf-open-tensor-normalization`, not silently attributed to Stacks' omitted derived details. No SGA source is used or cited in the split.

For Step 1 I opened the full statements of `prop-functor-package`, `prop-exc-open-adjoint`, and `sk-def-sf-operations`. Package clause (6), in dimension zero, supplies the normalized open purity already required by the item. The open-adjoint proposition is explicitly on the entire ordinary pro-etale derived module categories and so permits this calculation without an ambient exceptional adjoint for arbitrary morphisms. The operations node explicitly states the tensor-internal-Hom adjunction and naturality; the operation definition alone would not have sufficed. Transport includes the unit and counit, rather than only objects. The given finite-stage category embeds fully, so the resulting equality restricts to it. Coefficients remain the same finite commutative A_{E,n}; there is no passage to condensed coefficients, field coefficients, or site-perfect objects.

For Step 2 I read the statement of `def-exchange-projection` and the complete statement of `lem-sf-open-tensor-normalization` against the two Stacks sources. Taking the proper factor to be the identity gives precisely the displayed open projection gamma. The normalization lemma explicitly states that gamma inverse is adjoint to u tensor identity. Substituting P=RB into that equation and postcomposing with R(e_B tensor identity) gives the triangle R(e_B) u_RB=identity. This is three lines of the adjunction calculation from the cited statements, so I kept it as an elementary step rather than creating a comparison lemma node. The calculation fixes the map, including its orientation, and does not merely prove invertibility.

For Step 3 I opened `lem-trf-exceptional-internal-hom-exchange` and checked that its statement provides the *canonical* comparison with the first variable ordinary and the second exceptional, for the same coefficient stage. The word canonical is unpacked using the definition (0.3) in the item's cited PDF, not a claim that an arbitrary natural isomorphism preserves sections. Equation (0.3) defines Q=E_j inverse as the transpose of exceptional tensor followed by pulled-back evaluation; Step 2 identifies that exceptional tensor map with the canonical restriction/tensor comparison. The tensor-Hom adjunction used to express this evaluation equation is again the explicit operations-node statement. I did not substitute an existential isomorphism from the Lean candidate.

For Step 4 I opened `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and checked its conclusion asserts naturality simultaneously in both inputs in small ringed-site derived module categories. It gives the naturality at (tilde f, identity_M), not just an unspecified tensor isomorphism. The coefficient-unit comparison sends 1 to 1. On a K-flat representative the remaining unitor composite sends 1 tensor m to m in every degree, so this is an actual derived-map equality rather than an equality tested only locally. The two uncurried sections are both Rf. Injectivity of the tensor-Hom bijection gives the equality before inverting Q, and postcomposition by its specified inverse gives exactly the item's order of composition.

I tested j=identity (the equation becomes the original tensor-Hom mate identity), W empty (all target maps are the unique zero-category maps), f=0, M=0 or N=0 (both sections vanish), and M=N=A_C with f a scalar (both sides give its ordinary restriction). Over a point and A=Z/ell^2 the calculation is the usual scalar-module adjunction; it introduces no division and needs no semisimplicity. A nontrivial open, such as G_m inside A^1, is also covered by the ambient open adjunction without extending a section over the boundary. No properness, invertibility of f, or local constancy was added.

Against delivery-errors B-E: there are no new statements to test for B1-B9 or D1-D2. All symbols are introduced in the item or the proof. Every non-elementary input is an existing cited statement, and every citation has a verbatim entry in citations.json. The remaining work is explicit substitution in adjunction bijections, a triangle identity, naturality, and cancellation of an isomorphism. Proof dependencies are exactly the union of step uses; a dependency walk shows no path back to the item. Generic off-unit tools are declared in split_report.tool_uses. Every proof step has fewer than 2000 characters; there is no long step hiding a new lemma, no new definition, and no route or target statement change.
