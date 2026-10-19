# Stage-1 report: lem-per-local-cohomology-cech-bound

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-cech-bound.json`: split statement; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-adjoint-cech.json`: statement-only intermediate lemma; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-noetherian-comparison.json`: statement-only intermediate lemma; no Mathlib match.
- `citations.json`: verbatim statement quotes for all four proof-step citations.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, its title, and the local-cohomology/Čech declarations; no sorry-free declaration states this item or either new lemma.

## WANTED

None. The cited Stacks documents are present in `literature/stacks-project/`.

## Not duplicates

- `lem-per-local-cohomology-adjoint-cech` vs `lem-sbc-local-cohomology-derived-torsion`: the existing node identifies an Ext colimit with derived ideal-power torsion (Tag 0954), while this node gives the extended localization Čech model for the derived closed-support right adjoint (Tag 0A6R).
- `lem-per-local-cohomology-adjoint-cech` vs `def-per-closed-support-plus-adjunction`: the existing definition concerns bounded-below small-etale sheaf categories for finite coefficients and a closed-immersion exceptional functor; this node concerns unbounded module derived categories over an affine ring and ideal-power torsion.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-sbc-local-cohomology-derived-torsion`: the existing node is the Ext-colimit computation (Tag 0954), whereas this node is the Noetherian equivalence between the derived torsion functor and derived closed support (Tag 0955).
- `lem-per-local-cohomology-noetherian-comparison` vs `def-per-local-cohomological-dimension`: the existing node only defines the numerical cohomological dimension; this node proves the functorial comparison of the two derived support constructions.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-per-local-cohomology-sum-spectral`: the existing node is the spectral sequence for a sum of ideals (Tag 0BJC), while this node is the Noetherian torsion/closed-support comparison (Tag 0955).

- `lem-per-local-cohomology-adjoint-cech` vs `lem-per-local-cohomology-cech-bound`: the new node states the arbitrary-ring right adjoint for the torsion-cohomology subcategory; the existing node states Extended Cech model for ideal local cohomology.
- `lem-per-local-cohomology-adjoint-cech` vs `lem-weil-pbc-ring-complex-cech-base-change`: the new node states the arbitrary-ring right adjoint for the torsion-cohomology subcategory; the existing node states Augmentation-compatible base change for two ordered localization models.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-per-local-cohomology-flat-base-change`: the new node compares derived ideal torsion with the categorical closed-support right adjoint for every derived complex; the existing node states Flat base change for derived ideal-torsion local cohomology.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-per-algebraic-local-duality`: the new node compares derived ideal torsion with the categorical closed-support right adjoint for every derived complex; the existing node states Algebraic local duality with completed Ext.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-per-local-cohomology-cech-bound`: the new node compares derived ideal torsion with the categorical closed-support right adjoint for every derived complex; the existing node states Extended Cech model for ideal local cohomology.
- `lem-per-local-cohomology-noetherian-comparison` vs `lem-per-affine-support-cech-localization`: the new node compares derived ideal torsion with the categorical closed-support right adjoint for every derived complex; the existing node states Canonical affine supported-section triangle and its localization models.

## What was wrong or checked

The imported item was mathematically consistent with Stacks Tag 0956, but it was unsplit. Its source proof explicitly invokes Tag 0955 and the extended Čech right-adjoint model of Tag 0A6R, so those are real intermediate statements rather than restatements of the target. I kept the target statement and its hypotheses, including the (r=0) case. The item has no finished Lean declaration in either source checkout. The current shared item is still unsplit and its statement agrees verbatim with the saved item; its statement has not been changed.

I read the unit record `dag/units/sk-p-dl-a1-perverse.json`, the blueprint ancestor `lem-per-artin-gabber-affine-curve` and its proof, the complete item node, and the Stacks source passages for Tags 0A6R, 0955, and 0956. Mathlib searches for the item and both new nodes were run with `msearch.py`; the recorded searches are in the corresponding `searches.jsonl` files. Mathlib's `LocalCohomology.lean` documents the Čech-like comparison as future work and has no matching theorem, so no Mathlib leaf was claimed.

## Review by Q02

I read `dualizing.tex` at Tags 0A6R (`lemma-local-cohomology-adjoint`), 0955 (`lemma-local-cohomology-noetherian`) and 0956 (`lemma-compute-local-cohomology-noetherian`), including the statements and proofs. Tag 0956 is exactly the item's module computation, including arbitrary modules without finite-generation assumptions. Tag 0A6R gives the closed-support right adjoint over an arbitrary commutative ring for a finitely generated ideal; its explicit ordinary total tensor construction gives the module specialization in the first new node. Tag 0955(3) gives the second new node for every unbounded derived object over a Noetherian ring. Its canonical transformation is defined immediately before the lemma by adjunction factorization. I added the definition-node references for the derived category, spectrum and localization and made the second new node explicitly refer to the right adjoint of the first. Both new nodes remain statement-only.

The saved first auxiliary draft had an off-by-one error: in degree q it used q+1 generators. This fails already for A=k[x], I=(x), M=A: that draft has no localization factor in degree one, so H^1 is zero, whereas the correct local cohomology is k[x,x^{-1}]/k[x], which is nonzero. I corrected its degree-q term to the product indexed by q-element subsets, gave the differential and bounds explicitly, and kept the item's correct statement unchanged. This is a correction to a new auxiliary draft, not a change of the imported target.

Step 1 uses only the statement of `lem-per-local-cohomology-adjoint-cech`: it supplies exactly H^j(C_A(f) tensor M) = H^j(RΓ_Z(M)), naturally and A-linearly. All its hypotheses hold for the given finite list and module, even for the empty list.

Step 2 uses the statement of `lem-weil-pbc-localization-tensor-over-base`, which I opened and read. With R=A, its module M=A, its N equal to our module M, and T the powers of a product of generators, it gives the needed localization/tensor isomorphism with exactly the formula quoted. The elementary finite-product identification is proved by coordinate projections and inclusions. For each face map the proof writes the common image of a pure tensor; this checks commutation with the differential, including the signs. This is a generic tool from another unit, declared in split_report.tool_uses, not a replacement route. No flatness assumption is used here.

Step 3 uses the statement of `lem-per-local-cohomology-noetherian-comparison` at M[0]. It supplies exactly the natural comparison isomorphism, and `def-sbc-ideal-power-torsion-functor` explicitly supplies the injective-resolution convention identifying its degree-j cohomology with R^jΓ_I(M). Taking cohomology and composing the named isomorphisms is the argument, not an additional comparison theorem left implicit. Inverting the latter comparison gives the direction required by the item. Its only extra hypothesis is Noetherianity, which is present. Naturality follows by composing natural maps; the empty-list case reduces to the identity torsion functor.

I checked r=0, r=1, M=0, the zero ring, a nilpotent generator, and a unit generator. The corrected r=1 complex is M→M_f; for a nilpotent f its target is zero and ideal-power torsion is the whole module, while for f=1 the map is the identity and both sides vanish. No nonzero-ring, proper-ideal, finite-module or nonempty-list hypothesis was introduced. No proof step exceeds 2000 characters, and neither new node merely repeats the item's Noetherian ideal-torsion computation: one concerns the closed-support adjoint without Noetherianity, the other compares two derived torsion constructions without mentioning a Čech complex.

I searched the whole DAG for the tags and for the local-cohomology terminology and ran blueprint_refs searches for local cohomology, Čech, 0A6R and 0955, as well as its ancestor command. No blueprint node states either new auxiliary theorem. The current blueprint ancestor text at main-20261015 and its current DAG proof were read; the ancestry remains the technical commutative-algebra input under its first perverse-duality step. The existing `lem-per-ideal-torsion-cech-computation` states essentially the same module theorem as the item but already cites this item, so citing it here would be circular. `lem-per-affine-support-cech-localization` concerns geometric quasi-coherent support/localization triangles over Noetherian rings; it neither states the arbitrary-ring torsion-subcategory right adjoint nor identifies that categorical right adjoint with derived ideal torsion. I did not use its proof or silently identify those notions.

The initial mandatory dry run rejected the prior auxiliary search records because they were absent from this item's searches.jsonl. I ran all eight actual searches with msearch.py under Q02 and this item, read every returned hit, and replaced the unsupported records with the exact resulting log entries and verdicts. The repaired Loogle query uses the qualified name CategoryTheory.Functor.rightDerived and returns zero hits rather than an unknown-identifier error. LeanFinder and LeanSearch give independent phrasings for each auxiliary statement. The grep hits lead to LocalCohomology.lean, whose lines 42–46 explicitly list derived torsion and Čech comparisons as future work. No Mathlib leaf is claimed. The earlier four item-level search log entries are preserved, and the item's inherited search records are also preserved.

The final check of delivery-errors B–E found no proof hidden in a new statement, unstated non-elementary comparison, misuse of a cited statement, or cycle. I checked every citation quote against its node's actual statement before writing citations.json. The two proof lemmas had incorrectly been added to stmt_deps in the saved draft; I restored the original statement dependencies, since the item's statement defines its own complex and needs neither auxiliary theorem to be stated.

## Unfinished

The repaired stage-1 split is ready for the required server dry run and push; the two new theorem statements remain unsplit as required for one-level delivery.
