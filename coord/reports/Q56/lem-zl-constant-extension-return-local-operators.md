# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-return-local-operators.json`: item, statement unchanged, split into eleven proof steps. No Mathlib match.
- No new DAG nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 32 step/node citations. For the comparison tools the quotation retains the whole statement, including the domain and normalization hypotheses.
- `searches.jsonl`: actual searches made with the required command. The local writing script is only a sandbox artifact, not a delivery file.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint id and by constant-extension, sheet-return and local-operator vocabulary found no declaration proving every clause. `WeilSheaf/LocalFrobenius.lean` concerns the local operator and conjugacy, not the sheet-return equivalence, whole-tower block identity and filtration correspondence together. No existing declaration is treated as a completed proof merely because its docstring names one of these notions.

## WANTED

None for this split. I read Deligne, *La conjecture de Weil II*, printed pp.150–154: (1.1.7)–(1.1.10), the following base-field-independence paragraph, (1.1.13), and especially the real-valued fixed-iota convention (1.2.6). The integral/common-stage enhancement is explicitly agent-written from the cited DAG tool statements; it is not attributed verbatim to Deligne. No SGA route is used.

## Audit and changes

The sandbox initially contained only dispatcher markers: no earlier item, report, search log, or delivery receipt. I found no running delivery for this item before starting. I copied the live unsplit item and retained its source, inherited searches and creation metadata. There was no released stage-1 repair note for the item.

The item is well-typed under the sheet-coordinate statement, and I found no statement dispute. I left every hypothesis and conclusion unchanged. The source's remark on changing the finite base field is expanded into ordered transition and point-transport calculations. The proof avoids the parent `lem-zl-constant-extension-weil-heart-equivalence`, which already cites this item: using that parent would be circular.

The new split reuses `lem-zl-constant-extension-sheet-heart-coordinates` and `lem-zl-cyclic-return-exact-equivalence`, both already present, instead of making new nodes for exactness, subobject correspondence or filtration lifting. It proves the local comparison in steps 2–8. The purity and filtration consequences are elementary steps 9–11. The blueprint field names paragraphs 1 and 5 of the current `thm-zl-real-mixed-by-curves` proof, before finite pushforward; no chapter or unit route was changed.

I searched the whole DAG for sheet-return, cyclic-sheet and point-transport vocabulary, and ran `tools/blueprint_refs.py ancestor` and the whole-blueprint searches `constant extension`, `point transport`, and `filtrations`. The existing coordinate, cyclic-return, finite point-composition, integral tower-powers and scalar-calculus nodes supply the needed tools. None of the imported blueprint search results states the complete item. No new definition or statement is needed.

For Mathlib I ran all four requested search kinds. The first Loogle pattern returned an unknown-identifier diagnostic, so it is recorded as inconclusive and replaced by `CategoryTheory.Sheaf, "equiv"`; it is not counted as evidence of absence. The second semantic phrasing searched for equivariant sheaves on cyclically permuted disjoint components. I read its candidate `CategoryTheory.Presheaf.coherentExtensiveEquivalence` at Mathlib/CategoryTheory/Sites/Coherent/SheafComparison.lean:268: it compares coherent and extensive topologies on a preregular extensive category with projective objects, and gives no cyclic Weil data or Frobenius return operator. The other hits concern ordinary Frobenius on rings, sheaf evaluation or unrelated coherent/extensive comparisons. The two grep patterns found no Weil-sheaf/local-Frobenius implementation. These are not matches for this item. All additional search records use exactly the tool/query pairs in the local log; inherited records were kept as inherited records.

## Not duplicates

No new nodes. In particular, the finite and integral transport tools are reused rather than copied into a new base-field-comparison lemma, and the purity consequence remains an argument in the item's proof.

## Review by Q56

I read the source paragraph on printed p.152 as an equivalence for the same scheme interpreted over two finite base fields. That agrees with the item: the geometric scheme in the k0 interpretation has m sheets, whereas the km interpretation uses the distinguished sheet. This is not the restriction of an arbitrary Weil sheaf on X0 followed by a power claim; here N already lives on X0,m. At a closed point of that same scheme, its absolute residue field is unchanged. Deligne (1.2.6), p.154, is the source for arbitrary real weights with one fixed iota; the earlier integer-weight definition alone would not justify that part of the statement. There are no new nodes whose source or statement needs a separate audit.

Step 1 also cites `def-weil-constructible-heart`, whose statement expressly says that this heart is abelian; this checks the category hypothesis of cyclic return. Step 1 uses the actual statement of the sheet-coordinate node: its heart equivalence, exactness of P and the coordinate arrows a_i. The cyclic-return node explicitly states the return functor, exactness and the subobject/filtration correspondence. Their composite is the required functor on objects and morphisms. Neither cited node asserts the present local-operator result, so the substantive comparison remains in this split.

Step 2 uses `lem-kun-closed-point-field` only for finiteness of the residue degree; it does not ask that lemma for a cardinality formula. The latter is written out using an r-element basis over km. Multiplication of bases gives degree mr over k0. The local-operator definition explicitly uses the residue degree, and its return condition is equality after reparametrizing Spec k. The sheet-coordinate node explicitly supplies H^m j0 = j0 g_X^m. Thus both comparison squares in the step are justified; the proof never substitutes literal fixedness of a geometric point.

Step 3 uses the local definition's recurrence and the sheet relation to expand return Weil maps. The finite pullback-composition node supplies the actual finite comparison map, and the integral realization node explicitly supplies associative, unital comparisons respecting equality of scheme morphisms and finite iterations. I checked that the induction appends the block starting at mb and does not commute noncommuting Weil factors. It proves an ordered product identity, not just a statement about eigenvalues.

Step 4 uses the finite point-composition node's displayed recurrence for the single recipe along h^t and its naturality for every derived point morphism. Iterating that recurrence identifies the recipe for h^m with m old recipes. Applying it at U^(bm)V then gives the consecutive block bm,...,bm+m-1. This is exactly the iterated transport in the local definition. The finite pullback node is used for the targets and comparison maps, not for a separate scalar or tower assertion it does not state.

Step 5 uses the whole statement of `lem-trf-integral-point-transport-tower-powers`. Its maps exist for arbitrary systems, its recurrence is a whole-tower identity, and it states both the zeta/nu realization equation and compositor equation. Those clauses justify using the theorem again on G_(bm)C. The required derived limit is bounded constructible for the reduction system of the integral point pullback; the comparison theorem is expressly formulated without finite Tor-amplitude. The integral realization node supplies the same normalization for the return-square comparisons, including transformations before realization. This corrects the tempting but unjustified shortcut of arguing solely from separate finite reductions.

Step 6 assembles the three factors in the local definition after steps 3–5. I checked source, target and ordering: c maps the return stalk to the original stalk, so its equation is c F_R = F_N c. Finite/tower naturality applies to the structure-square maps of a Weil morphism. No stalkwise exactness or lissity assertion is smuggled into this assembly step.

Step 7 uses precisely the scalar-localization theorem's preservation of transformation equations and whiskering. A rational Weil arrow need not be an integral isomorphism; writing it as f/varpi^a gives equal denominators on both ordered products. The iterated-return scalar-calculus node states compatibility for both the point transport and the return-square comparison, with identity/successive extensions; it is not merely a statement of scalar compatibility on objects. Finally the common-stage coefficient definition supplies representatives and equality after a common extension. This checks the category at which the result is asserted, without Karoubi completion or an integral-lattice hypothesis on the Weil map.

Step 8 uses local conjugacy only at the rational finite stage where that node states it, for finite-type schemes over k0 and km separately. The displayed calculation then constructs the new intertwiner. Common-stage passage is justified by step 7 and the common-stage definition; the rational conjugacy theorem is not invoked as a finite-torsion or arbitrary integral-tower theorem.

Step 9 writes out why the intertwiner identifies eigenvalues: map an eigenvector and use the inverse for the converse. The punctual-weight definition provides exactly the same equation at the same absolute residue size. Steps 10 and 11 use the explicitly stated exact and filtration correspondence from step 1, and then apply step 9 to each quotient. The inverse filtration is unique as subobjects of N; it does not claim uniqueness of selected monomorphism representatives. The weight definition permits repeated terms, so zero quotients cause no difficulty.

I checked the small cases m=1 (no intermediate arrows), r=1 (one return block), m=2 and r=2 (four ordered factors, grouped as the first two and the last two without reversal), the zero stalk and zero object (no eigenvalues), the length-zero filtration and the empty scheme. All remain in the statement. Every residue-degree assertion uses finite type. No step needs geometric connectedness, lissity, semisimplicity, or finite Tor-amplitude. I checked that the cited tools' dependency closures do not contain this item. Every proof step is below 2000 characters, and none hides a new comparison lemma: comparisons with their own hypotheses are the existing cited nodes.

The off-unit tools are declared in `split_report.tool_uses`, with the mathematical operation each supplies. They are generic coefficient/point-transport tools, not replacements for the constant-extension route. I did not write maintainer-owned `tool_uses` or `reviewed` fields. I checked delivery-errors B–E against the actual files: no new-node shape or duplicate issue arises; all 32 citations quote the statement actually used; block products and whole-tower realization are explicit; and purity is deduced rather than moved into a new clause node.

## What remains

No mathematical work remains for this one-level split. The existing statement-only dependencies remain queued independently. The delivery requires the prescribed server dry run and push, followed by the maintainer's independent review.
