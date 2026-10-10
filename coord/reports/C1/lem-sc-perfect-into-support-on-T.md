Files written:

- `dag/nodes/sec-picard-framework/lem-sc-perfect-into-support-on-T.json`: repaired statement split, 2 new statement dependencies, no Mathlib leaves.
- `dag/nodes/sec-picard-framework/lem-sc-derived-mayer-vietoris-hom.json`: statement-only Stacks Tag 08DJ-area dependency, Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-sc-qcqs-affine-induction-principle.json`: statement-only Stacks Tag 08GL dependency, Mathlib no match.

Attachments: none.

WANTED: none.

## Not duplicates

lem-sc-derived-mayer-vietoris-hom vs lem-pc-derived-internal-hom-pullback-adjunction: the new node states the Mayer–Vietoris long exact sequence for Hom and Ext under an open cover, while the existing node states a derived pullback/internal-Hom adjunction for an arbitrary morphism of schemes and no open-cover exactness.

lem-sc-derived-mayer-vietoris-hom vs lem-sc-ext-stalk-localization: the new node is the open-cover Mayer–Vietoris sequence in derived categories, while the existing node is localization of coherent sheaf Ext at a stalk on a Noetherian scheme.

The returned version had a false Step 3: vanishing after restriction to each open does not imply global vanishing for derived morphisms. It also treated the affine calculation as a chain-level finiteness assertion without the finite-projective model and truncation induction. I repaired both points. The item statement remains the Tag 08EJ statement. I searched the DAG and blueprint for duplicates before adding the two generic dependencies; neither statement already existed.

## Review by C1

I read the item proof in `literature/stacks-project/perfect.tex`, Tag 08EJ (the lemma `lemma-perfect-into-support-on-T`), and read the cited source passages for Mayer–Vietoris Hom and the qcqs induction principle. Step 1 uses the existing node `lem-sc-rhom-supported-qcoherent`; its statement explicitly says that internal Hom from a perfect source is quasi-coherent and that support is preserved by restriction. Step 2 now cites `lem-sc-derived-mayer-vietoris-hom` for the long exact Hom/Ext sequence and `lem-sc-qcqs-affine-induction-principle` for reduction to the affine case. The exponent on an overlap is combined additively through the connecting term, which is the Mayer–Vietoris argument in Tag 08EJ; quasi-separatedness is used exactly to make overlaps quasi-compact for the induction principle. Step 3 cites `lem-pc-affine-qcoh-derived-equivalence` for the identification with D(A) and `lem-pc-perfect-affine-bounded-projective` for a bounded finite-projective model. I checked the stupid-truncation triangle, the reduction to a single finite projective module in degree zero, the fact that support on V(f) makes every element f-power torsion, and the uniform exponent obtained from finite generation.

I tested the repaired reasoning on f a unit (the target support is empty and alpha is zero), f=0 (n=0 is allowed), alpha=0, a one-term finite projective complex, and a two-term complex where the truncation step combines exponents from the two triangles. The previous local-conservativity claim was removed; the missing use of quasi-separatedness is now explicit in the induction step. The new nodes' Mathlib searches were run with LeanFinder, Loogle, source grep, and LeanSearch; generic Mathlib Mayer–Vietoris or compact-open declarations did not state either Stacks result.

## Second reading by C1

- Item statement checked against Stacks Tag 08EJ (perfect.tex, Lemma 36.13.9), hypothesis by hypothesis; correct.
- Step 1 checked against `lem-sc-rhom-supported-qcoherent`; its quasi-coherence and support conclusions say exactly what is used.
- Step 2 checked against Stacks Tag 08BW and existing `lem-sc-derived-hom-mayer-vietoris`, plus Tag 08DR and existing `lem-sc-invert-s-cohomology-induction`; citations and exponent-gluing text were corrected.
- Step 3 checked against the affine equivalence and bounded finite-projective nodes and the affine paragraph of Tag 08EJ; truncation and finite-generation argument match.
- The proposed Mayer–Vietoris node duplicated existing `lem-sc-derived-hom-mayer-vietoris` (same Tag 08BW), so it was removed.
- The proposed qcqs induction node duplicated existing `lem-sc-invert-s-cohomology-induction` (same Tag 08DR), so it was removed.
- Updated `citations.json` with verbatim quotes from the existing nodes and removed stale duplicate-node citations.
- Small cases checked: f a unit, f=0, alpha=0, one-term finite projective, and a two-term truncation.
