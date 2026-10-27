## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-special-linear-picard-zero.json: statement, split; no Mathlib match for the item. Statement text unchanged. Added the polynomial-ring and quotient-algebra notions to stmt_deps.
- citations.json: verbatim statement quotations for all 11 step/node citation pairs.
- report.md and searches.jsonl: report and genuine msearch output records.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live lean/WeilConjectures source by the exact blueprint tag and id, SpecialLinear/special.linear, and Picard terminology. There is no project declaration stating this determinant-one affine-scheme Picard vanishing; the general Picard and curve declarations do not establish it.

## WANTED

None. All sources needed here are present in literature/.

## Corrections and source route

The imported item had no proof. Its statement agrees with Milne, Algebraic Groups, Proposition 20.30 (printed p.417, PDF p.429), including an arbitrary ground field and no characteristic restriction. Read also 2.42 (printed p.53, PDF p.65). Milne first proves Pic(GL_n)=0 using the localized polynomial UFD, then retracts from GL_n to SL_n via the scheme product SL_n times G_m. This delivery uses exactly that route, reusing lem-sfb-affine-space-open-invertible-trivial for the first assertion and writing the coordinate retraction for the second. Its source is Stacks Tag 0BDA, divisors.tex, lemma-open-subscheme-UFD, whose statement and proof I read.

There is no statement dispute or change of hypotheses. I corrected an initial source locator for the affine basic-open construction to Tag 01I3 (lemma-standard-open-affine), after checking tags/tags; Tag 01HV supplies its section ring. The two new statement dependencies name notions already used in the displayed coordinate algebra. No other item's file was changed.

The current latest blueprint unit sk-thm-sf-ctf-stability and the chapter were read. This is an auxiliary at the end of the inherited alteration/moduli/rank-one-group chain, not the unit's key node. The ancestor command returns None, consistently with blueprint.from.node=null; the inherited detailed from.place and via chain are retained. The whole-blueprint searches for Picard, special linear, line bundles, and invertible pullback found no equivalent statement for this item; the general-linear-group definition is a notion, not Picard vanishing. same_as remains []. No unit route was replaced and no unit record was edited. The cited non-Mathlib statement lem-sfb-affine-space-open-invertible-trivial has this item's own unit. The other statement tools used are already Mathlib leaves.

## Mathlib searches

Preserved the item's inherited Q92 search records. Ran five further logged queries with the required msearch.py command: leanfinder for invertible sheaves on the determinant-one matrix scheme; loogle for CommRing.Pic, Matrix.SpecialLinearGroup; grep for Pic.*SpecialLinear|SpecialLinear.*Pic; leansearch for Picard vanishing of the special linear group scheme; and a second leanfinder phrasing for invertible modules on the quotient polynomial ring by determinant minus one. All services responded. Read the hits and the sources at RingTheory/PicardGroup.lean:478–535 and LinearAlgebra/Matrix/SpecialLinearGroup.lean:64–70. The ring Picard criteria characterize triviality but do not supply it here; the local/semilocal instances have hypotheses absent for this coordinate ring; the SpecialLinearGroup results describe matrices, not invertible sheaves. No match or one-line specialization proves the item. Searches are recorded as actually run, with their JSON log records and verdicts.

## Not duplicates

No new nodes were created. The existing lem-sfb-affine-space-open-invertible-trivial states the precise stronger open-of-affine-space vanishing needed for GL_n, so I cite it instead of creating a UFD or GL_n Picard node. The explicit first-column determinant calculation and rank-one tensor-pullback calculation are short steps, not new lemmas. No node repeats a clause of the item.

## Review by Q104

I read Milne Proposition 20.30 and 2.42 in the PDF and the Stacks 0BDA source with the node files open. In particular, the retraction is a morphism of schemes over every field, not merely a formula on k-points. No perfectness, algebraic closure, reducedness, or characteristic hypothesis is introduced.

Step 1 uses the actual statement of lem-weil-pbc-affine-open-section-vanishing-prime, clause (b), which gives both affineness and the ring of the basic open. I did not use the purely topological localization-spectrum node to assert a scheme isomorphism. Here the ambient affine open is all of Spec(P), the element is d, and B is precisely its localization. def-weil-ring-localization-away says d becomes a unit. These establish that G is the open of affine n^2-space required later.

Step 2 uses lem-weil-pbc-ring-localization-universal-property only with the powers of d and the map P to A sending d to 1. Its unit hypothesis therefore holds, and its statement actually gives q, including q(d^{-1})=1. I read def-weil-pbc-matrix-determinant and used its Leibniz formula: each term contains exactly one first-column factor. This proves det(y)=1 directly, without invoking uncited determinant multiplicativity. The polynomial definition gives evaluation; the quotient-algebra definition supplies its kernel, and the text explicitly checks descent through d-1. def-weil-affine-spectrum gives contravariant functoriality. Checking q s on all residue variables and constants gives the identity as a ring map, hence the displayed morphisms satisfy r j=id. No claim from the proof of a cited node is used. This calculation is elementary relative to those cited statements.

Step 3 reads tensor pullback from def-pc-module-pullback and rank-one local trivializations from def-sc-invertible-module. The proof explicitly gives the local multiplication map and its inverse a to a tensor 1. Thus pullback is locally O on the inverse-image cover; local free rank one modules are quasi-coherent locally, as required by the invertible-module definition. This is the elementary local proof of the standard fact in Tag 0B8L (modules.tex, lemma-pullback-invertible), which I also read, not an unsupported citation of that tag as a black box. The same two-line tensor-unit calculation proves j^*O_G=O_X.

Step 4 uses the exact statement of lem-sfb-affine-space-open-invertible-trivial: any open in affine space over any field, and every invertible module on it. Step 1 supplies the open and Step 3 the invertibility. Unlike lem-sfb-affine-cell-picard-product, it requires neither a proper factor nor an algebraically closed field. The composition and identity pullback isomorphisms are explicitly in def-pc-module-pullback's statement, which I read. Applied to r j=id, they identify j^*r^*L with L; pulling back an isomorphism preserves its inverse by functoriality. The resulting isomorphism proves all of the item, and the Picard-group conclusion follows from its given definition.

I tested n=1 separately: the quotient is k and x/d=1. For n=2 the matrix sent to SL_2 has first column (a/d,c/d), second column (b,e), with determinant (ae-bc)/d=1, including characteristic two. These checks also work over nonreduced k-algebras because the formulas use the literal relation d d^{-1}=1 and not pointwise equality or cancellation in a domain. For arbitrary n each Leibniz term has one first-column entry. The assumption n>=1 is exactly what selects that column. There is no excluded characteristic and no extraction of an nth root. No empty-scheme or nilpotent case is used to infer a false equality. No new statement needs an edge-case test.

I checked delivery-errors B–E point by point: no new nodes or leaves need B1/B2/B6 validation, all notions used have their definition nodes, statement text and TeX are preserved, source labels are checked, and genuine search logs are retained. Each used node's statement is quoted verbatim in citations.json; the non-elementary steps cite actual statements, the elementary steps contain their calculations, and no argument is hidden in a new node. No off-route non-Mathlib theorem is used. All four steps are under 2000 characters (447, 1109, 546, 767); none hides a long auxiliary lemma. The dependency union is exact and the cited nodes exist and are unmerged. The server dry run supplies the final global cycle and preflight checks.

## Unfinished work

None in the stage-1 split. No Lean files were written, and no compiler or build tools were run.
