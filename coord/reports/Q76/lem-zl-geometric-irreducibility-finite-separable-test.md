# Q76: lem-zl-geometric-irreducibility-finite-separable-test

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-irreducibility-finite-separable-test.json: item, statement, split in six steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-general/lem-zl-sepclosed-algebras-tensor-irreducible.json: one new statement-only node, Stacks Tag 00I7 for arbitrary algebras; no Mathlib match. No new Mathlib leaves.
- citations.json: literal statement quotations for every citation in the six proof steps.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the item id, geometric-irreducibility names, finite separability, Tag 00I7, and the separably-closed tensor/minimal-prime assertion. No project declaration states the item or the helper. The existing separable-closure project declaration IsSepClosure.exists_intermediateField_mem belongs to def-pd-separable-closure, which is already the node used; it only covers finite-subextension membership, not the item. No Lean was written or compiled.

## WANTED

None. All proof sources used are present in literature/stacks-project/algebra.tex.

## Audit and changes

The item statement is correct and unchanged. I read Tag 037K (lemma-geometrically-irreducible), including all four conditions and its complete proof. I retain its route through a separable closure and a common overfield. Instead of introducing an unnecessary algebraic-closure intermediate object, I apply its cited Tag 00I7 directly over the separably closed separable closure. This is the same tensor-product argument and does not invoke the later, circular Tag 037M. Finite support and the existing prime-nilradical criterion spell out the finite-subextension passage and the final descent without new minimal-prime or going-down nodes.

The imported item had no proof. Existing Mathlib search records were retained and the actual Q76 searches appended. The item's inherited blueprint ancestry points through lem-zl-field-extension-algebraically-closed-geometric and lem-zl-geometric-irreducibility-separable to lem-zl-bertini-finite-cover-curve. I read the chapter and unit records and the current ancestor's blueprint_update: paragraph 3 is the geometric-irreducibility input to Tag 0G4F. The helper serves that same reduction, with ancestry via the present item. Whole-DAG and blueprint searches for geometric irreducibility, irreducible spectrum, nilradical, tensor products, separably closed, and Tag 00I7 found no existing node stating the full helper.

Mathlib searches used only msearch.py and are logged in searches.jsonl. Both item and helper received LeanFinder, Loogle, grep and LeanSearch queries, with two semantic phrasings each. For the item, hits concern geometrically reduced algebras or the definition and stability of geometrically irreducible scheme maps, not the finite-separable test. For the helper, hits concern tensor-product ring structure, reducedness, linear disjointness, or purely inseparable spectral homeomorphisms, not irreducibility for two arbitrary algebras over a separably closed field. I read the pinned Mathlib AlgebraicGeometry/Geometrically/Irreducible.lean and the relevant declarations in RingTheory/Nilpotent/GeometricallyReduced.lean; none specializes to the requested assertions in one line. No unavailable service was recorded as absence.

## Not duplicates

lem-zl-sepclosed-algebras-tensor-irreducible vs lem-weil-pbc-field-tensor-irreducible: the existing Tag 00I7 node requires BOTH factors to be fields; the new node allows BOTH to be arbitrary commutative algebras with irreducible spectra. Our factor R tensor k_s need not be a field or reduced, so the existing statement does not apply.

lem-zl-sepclosed-algebras-tensor-irreducible vs lem-weil-pbc-sepclosed-tensor-reduction: the existing Tag 00I7 reduction assumes two field extensions and identifies a spectrum after passage to reductions over an algebraic closure; it does not assert tensor irreducibility for arbitrary algebras.

lem-zl-sepclosed-algebras-tensor-irreducible vs lem-weil-pbc-algclosed-finite-type-tensor-domain: the existing node assumes the base algebraically closed and one factor a finite type domain, and concludes domainness; the new node assumes only a separably closed base and allows arbitrary, possibly nonreduced, non-finitely-generated factors with irreducible spectra.

lem-zl-sepclosed-algebras-tensor-irreducible vs lem-weil-pbc-sections-base-field-extension: the existing node is invariance of sections of etale sheaves under extension of a separably closed field; it is not a tensor-irreducibility statement.

lem-zl-sepclosed-algebras-tensor-irreducible vs lem-zl-geometric-irreducibility-subalgebra-colimit: the existing node is stability of GEOMETRIC irreducibility under injections and directed colimits, whereas the new node concerns ORDINARY irreducibility of the tensor product of two algebras over a separably closed base. The existing statement cannot first establish geometric irreducibility here.

## Review by Q76

I checked B through E against the written nodes and sources. For the item I read Tag 037K in algebra.tex, especially the (2) to (3) finite-subextension passage and the final common-overfield argument. For the new helper I read the full statement and proof of Tag 00I7, lemma-separably-closed-irreducible, immediately preceding Tag 037K. Its hypothesis is a separably closed field and two algebras with unique minimal prime, equivalently nonempty irreducible spectra. Thus it genuinely covers the nonreduced algebra R tensor k_s needed here. The helper is left statement-only with empty proof and proof dependencies. It is a general tensor theorem, neither a clause of the item's finite-separable equivalence nor a renaming of that equivalence.

Step 1 is just specialization of a universal quantifier. Step 2 uses the tensor definition's bilinearity and generation and the algebra-tensor universal property's multiplication/unit, with explicit mutually inverse formulas for reassociation. I read both node statements. The faithfully-flat base-change node permits every commutative algebra D, so it applies to D = R tensor E with no finite-type assumption. The ideal-contraction node explicitly gives injectivity at I = 0; I use that theorem rather than treating the definition of faithful flatness as an injectivity theorem.

Step 3 uses the exact separable-closure definition's filtered-colimit/finite-subextension assertion and its separably-closed hypothesis. The existing spectrum/nilradical node includes properness and the zero-ring exclusion, so it gives R nonzero from condition (2) at E = k. Injectivity from Step 2 gives the needed nonzero algebra over k_s. Step 4 again uses tensor generation and the same filtered-union assertion to put finitely many coefficients into a single finite separable E. It detects the equation (x_E y_E)^n = 0 by the injectivity already proved; this avoids silently assuming an equation descends merely because its coefficients do. The nilradical criterion supplies exactly primality at E and irreducibility at k_s. No claim about minimal primes is borrowed from a definition node.

Step 5 uses the common-extension-fields node, whose statement explicitly gives compatible k-embeddings for arbitrary extensions, so it applies to L and k_s with no algebraicity assumption on L. I declare this off-unit generic field-theory tool in split_report.tool_uses. The proof verifies the field M has proper prime zero ideal before using the nilradical criterion. Both algebras over the separably closed field k_s now meet the new helper's stated hypotheses; its precise conclusion is the irreducibility taken by this step. Step 6 uses only the same criterion and the already established injective unital scalar-extension map. It writes out both nilpotent reflection and contraction of a proper prime, proving the last descent rather than hiding it under a topology slogan. Every step's citation was checked against its node statement and has a verbatim quote in citations.json. The whole DAG dependency list is the union of the six steps' uses.

Small-case checks: R = 0 makes both sides of the equivalence false, so condition (2) cannot start the reverse proof; the proof explicitly excludes that case at E = k. For R = k, all scalar extensions are fields and the proof works. Nilpotents are permitted throughout: k[epsilon]/(epsilon^2) has prime nilradical and all its field extensions are irreducible. A product k times k violates the hypothesis already at E = k. In positive characteristic with imperfect separably closed k, the helper asserts irreducibility, not reducedness or domainness; this distinction is necessary for inseparable tensor products. Neither helper factor is required to be finite type. All six step texts are below 2000 characters; reassociation and nilradical contraction are explicit routine calculations, and the substantive separably-closed tensor theorem has its own node.

No statement correction, route dispute, SGA source, additional axiom, compiler call, or write to either read-only repository was used. I corrected a draft citation substring to the literal cited statement before delivery.

## Unfinished work

The item's one-level split is complete. The single new helper is intentionally unsplit, to be handled as a separate future item. Delivery validation follows below.
