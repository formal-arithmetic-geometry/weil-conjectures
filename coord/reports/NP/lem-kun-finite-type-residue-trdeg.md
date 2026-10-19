## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-finite-type-residue-trdeg.json`: item, statement split into two proof steps.
- No new nodes; the existing Mathlib leaf `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` is cited.

## Attachments

None.

## WANTED

None.

## Not duplicates

No new nodes were created, so no duplicate pairs arise.

## What was checked

The item statement and source were read in `literature/stacks-project/algebra.tex`, Lemma 10.116.1 (Tag 00P0), and the blueprint sentence in `lem-kun-dimension-finite-type`. I checked the source's affine reduction: finite type over a field gives an affine chart with a finitely generated coordinate algebra, and the residue field at a prime is the fraction field of the prime quotient. Step 1 records this reduction and uses only the finite-type and residue-field definitions; it is elementary once those definitions are fixed.

For Step 2 I opened the existing node `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` and verified that its statement gives a finite transcendence basis for every finitely generated field extension. I also checked `def-kun-transcendence-degree`, whose statement identifies transcendence degree with the size of a transcendence basis. Thus every cited statement says exactly what the step uses, and all hypotheses (field base, finite generation, prime quotient) are established in Step 1. The Mathlib searches were rerun with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable, while LeanFinder found only the general `trdeg_lt_aleph0` theorem and no direct scheme statement. The edge cases of a zero-element basis (algebraic residue field, transcendence degree 0) and the empty scheme (vacuous point assertion) are covered.

## Review by NP

I read the item source (Stacks Tag 00P0) and the blueprint ancestor, and checked the two proof steps against the cited node statements. Step 1 uses the finite-type definition to obtain a finitely generated affine coordinate algebra and the residue-field definition to identify the point's field; no hidden hypothesis is used. Step 2 uses the existing finite-transcendence-basis statement exactly under the finite-generation hypothesis established in Step 1, then uses the transcendence-degree definition. I verified the field and prime hypotheses, checked the zero-dimensional algebraic case and the empty-scheme case, and corrected the citation quotes to be verbatim. No new node was needed because the only non-elementary field fact is already the existing Mathlib leaf.

## Second reading by NP

- Item statement: checked algebra.tex Tag 00P0, lemma-dimension-prime-polynomial-ring, on the domain A/𝔭, and fields.tex Tag 030F, lemma-transcendence-degree; correct, no hypothesis or conclusion change. Checked Spec K (degree 0), the generic point of affine one-space (degree 1), prime quotients with algebraic residue fields, and the empty scheme. A zero coordinate ring has no prime point.
- Step 1: checked the complete statements of def-weil-finite-type-morphism, def-weil-affine-spectrum, def-weil-pbc-module-stalk, def-weil-pbc-localization-at-prime and def-weil-residue-field, and schemes.tex Tag 01HU, definition-structure-sheaf with its preceding standard-open construction; repaired to choose a chart supplied by the definition and give the germ and fraction calculations explicitly. The quotient is a domain because 𝔭 is prime; the unital map from K is injective because the residue field is nonzero. No closed-point assumption is used.
- Step 2: checked lem-weil-pbc-finitely-generated-field-finite-transcendence-basis and def-kun-transcendence-degree verbatim, and fields.tex Tag 030F, lemma-transcendence-degree; correct. Finite field generation is precisely Step 1's conclusion, and cardinality of the finite basis gives the requested finiteness.
- New nodes: none; no elementary, duplicate, clause-restatement or unnecessary new leaf to remove. The existing finite-basis Mathlib leaf supplies the substantive field input.
- Independent searches: ran LeanFinder on essentially finite-type residue extensions, Loogle on residueField/FiniteType, and grep on residueField/finiteType and trdeg_lt_aleph0. Read the hits: LocallyOfFiniteType.stalkMap and RingHom.EssFiniteType.residueFieldMap are ingredients; no single returned declaration states the item's scheme-level conclusion. The existing finite-basis leaf is already Mathlib. Plain source search in the read-only slopmaster2 WeilConjectures/ and Comparator/ trees found no item-id or finiteType/trdeg match. Blueprint search for residue field transcendence returned no match; ancestor is lem-kun-dimension-finite-type.

Changes: expanded Step 1's affine germ calculation and justified the precise choice of chart; kept Step 2's mathematical argument while using precise TeX/cardinality wording; replaced narrow citation fragments by complete verbatim statements; corrected tag/label source descriptions; replaced unlogged search summaries with the actual recorded queries/results (including unavailable LeanSearch); removed worker-written split_report.tool_uses, since the cited tool is already a Mathlib leaf and that field is the maintainer's; removed the stale root-level unsplit copy so the sandbox has one authoritative item file. No new nodes and no statement changes.
