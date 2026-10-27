# Q131 stage-1 delivery: lem-sfb-smooth-coordinate-blowup-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-coordinate-blowup-charts.json: statement, split in eight steps; no Mathlib match for the entire statement.
- citations.json: one verbatim statement quotation for every use in each numbered step.
- No new DAG nodes and no new Mathlib leaves. Existing coordinate-model and commutative-algebra tools suffice.

## Attachments

None for the item. Searches of lean/WeilConjectures for its blueprint tag and coordinate/blowup notions found no declaration stating the full result. Existing strict-transform chart constructions and IsRegular.of_smooth cover tools only. Their existence is not claimed as an attachment of the item.

## WANTED

None: all sources used here are present. The inherited ancestor mentions a missing Vidal article; this local coordinate argument does not use it.

## Problems found and scope

No correction to the item's statement was needed. The source's coordinate substitution must be combined with flatness to justify the relative smooth charts over arbitrary fields, and with a schematic closure computation to identify the strict transform. In particular the total inverse-image equation has an exceptional factor of multiplicity |S|; it is the reduction that has exponent one. The strict transform of the boundary divisor is not its total transform. The singleton case is an identity blowup with empty strict transform.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor reports None. The existing node's blueprint.from.node and via metadata are maintained rather than invented. Its from.place already specifies VIII 4.2.9 and X 2.2. I read the current latest blueprint's direct-images proof clause (3) and the current unit section. The computation supplies the same existing open-direct-image branch, without modifying that route.

## Unfinished work

None at this level. The existing unsplit coordinate-model node is reused, not split here. Its future worker must prove its polynomial chart isomorphism. This item supplies the relative pullback, boundary and strict-transform assembly.

## Not duplicates

No new nodes are created. The DAG search found lem-trf-coordinate-subspace-blowup-charts (0H1H, arbitrary base ring), thm-nagata-blowup-flat-base-change (0805), and the existing regular-sequence, regular-quotient and Nakayama nodes; all are reused. The affine coordinate model has no smooth arbitrary pullback, reduced boundary or strict-transform clause, so it is not an attachment for this item. Whole-blueprint searches for coordinate and blowup found no alternate blueprint statement of this combined item; blueprint.same_as remains empty.

## Review by Q131

I read Stacks more-morphisms.tex remark-relative-blowup (0H1H), its displayed affine rings and exceptional equation, and lemma-blowup (0FUT), whose reduction invokes flat base change. I also read divisors.tex lemma-blowing-up-affine (0804) and lemma-flat-base-change-blowing-up (0805), algebra.tex lemma-regular-ring-CM (00NQ) and lemma-regular-quotient-regular (00NR), and varieties.tex lemma-smooth-regular (056S). The ILO PDF, VIII Lemma 4.2.9 on printed p.121, provides the chart substitution and strict-transform calculation; its neighboring Proposition 4.2.8 and proof explain the use in the permissible blowup route. There are no new nodes requiring separate sources.

For step 1 I opened the cited smooth base-change, affine-space smoothness, smooth-composition, smooth-over-field regularity and regular-local-domain statements. They provide precisely the asserted operations and regularity, with no perfect-field assumption. Reducedness is checked from the cited stalkwise definition, since domains have no nonzero nilpotents.

For step 2, smooth-flat supplies flatness; def-weil-flat-morphism supplies the local flat map. The weak-regularity localization node explicitly preserves each multiplication injection without demanding a nonzero final quotient. The flat-tensor-exact node explicitly preserves those injections, not merely the definition of flatness. Polynomial-variable injections are checked coefficientwise. The quotient is nonzero only at points where all the selected coordinates lie in the maximal ideal, exactly where regular-sequence nonzeroness is needed.

For step 3 the dimension formula is applied only to the nonzero Noetherian local ring R and the regular sequence just proved. Both R and R/J are regular by step 1, so the regular-quotient kernel-parameters theorem applies. The regular-parameter quotient theorem identifies the length of its kernel prefix as r. This avoids the invalid inference that arbitrary regular sequences are partial regular parameters. The two generating lists span the same r-dimensional subspace of m/m^2, so the actual coordinate classes are independent. Nakayama applies to the finitely generated maximal ideal of a Noetherian local ring and makes a lifted cotangent basis generate it. At a component generic point the reduced zero-dimensional local ring is a field; the same dimension formula gives the component's codimension.

For step 4 the regular-parameter quotient statement makes every single-coordinate quotient regular; the domain statement then makes its ideal prime. The distinct parameter classes exclude divisibility by another. I wrote the intersection-equals-product induction explicitly, which proves radicality and does not appeal to an uncited UFD theorem. Units are removed locally. Products are nonzerodivisors in the local domain. This verifies both the effective Cartier and reduced assertions by their definitions.

For step 5 the flat-base-change theorem names bc_g, so I also cite and read its defining node, which specifies the flat map, extended center and chart-preserving Proj identifications. Its hypotheses hold because c is smooth and hence flat. The arbitrary-ring affine model provides the cover and polynomial isomorphisms for |S|>0; setting its base ring to F and permuting the variables gives the desired charts. The same smooth base-change node of step 1 proves the new chart-to-model maps smooth. I do not use the smooth-pair etale local model, which is unnecessary here and would require constructing extra etale coordinates.

In step 6 I apply the preceding general coordinate argument to these new smooth maps. Substituting z_a=t*u_a gives t^s*q*h, while the exceptional ideal is (t). The prime-ideal test proves radical(t^s*q*h)=radical(t*q*h), and step 4 proves the latter ideal radical. Thus the reduction equation follows from the cited definition of scheme reduction. This is a calculation, not an additional geometric lemma.

In step 7 I read the strict-transform and scheme-image definitions: they specify scheme-theoretic closure and its kernel ideal, with the kernel itself for a quasi-compact immersion. On the chart the relevant immersion is closed in D(t), hence quasi-compact. Inverting t turns the total equation into q. I wrote the localization equality criterion t^N*f in (q) and its prime-factor cancellation, so the kernel is exactly (q) even in the presence of empty loci and units. This identifies the closed subscheme, not just its support. The closure also sits in the full inverse image since its ideal contains (t^s*q).

Step 8 checks |S|=1, n=0, empty V, empty center, empty charts and intersections. For S a singleton the chart map is literally the identity and q=1, including when the divisor is empty. Nonperfect fields, nonintegral disjoint unions, varying relative dimensions and non-quasi-compact schemes do not invalidate any step: every assertion is obtained by smooth base change or checked locally. No global dimension equality or finite global affine cover is used.

Against delivery-errors B--E: statements of all cited nodes were read, and citations.json quotes their exact statement text. No new statement-only node hides an item clause, no new elementary node is introduced, and no source citation substitutes for a non-elementary dependency. Generic off-unit tools are declared in split_report.tool_uses, for the maintainer to judge. No proof step exceeds 2000 characters; I still checked the parameter argument and the closure argument for hidden comparisons and included all of their algebra explicitly. All Mathlib search entries added by this worker come from searches.jsonl; semantic hits concern general smoothness and fail to state the blowup/boundary result. No compiler, Lake command, repository write or git command was run by this worker.

Final source check corrected the strict-transform definition tag from the section tag 080C to its definition tag 080D, and spelled out finite presentation of the center from its finite coordinate generators. The first full dry run passed; the final dry run includes these clarifications.
