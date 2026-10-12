## What changed

The target signature and original docstring are unchanged. Replaced the first worker's circular existence/compatibility split by a real reduction: construct the right-adjoint restriction square from t, take its inverse mate, prove the mate invertible along restriction equivalences, and derive the section formula from Mathlib's unit equation. Added AffineEtaleRestrictionLargeSets and InverseMateEquivalence as plain proof imports. All original public imports are required for the existing target signature.

## Proved and sorry left

AlgebraicGeometry.Scheme.affineEtale_inverseImage_restriction_unit has no local sorry: it is proved relative to the restriction-equivalence obligation and pre-existing open dependencies. CategoryTheory.isIso_inverseMate_of_equivalences is fully proved and has only propext, Classical.choice and Quot.sound as axioms.

AlgebraicGeometry.Scheme.fullAffineEtale_large_sets_equivalence in Sheaf.AlgebraicGeometry.AffineEtaleRestrictionLargeSets is the sole sorry added or left by this delivery, with node lem-stage3-affine-etale-restriction-large-sets. The target's axiom closure still contains sorryAx; this is a partial proof delivery, not an axiom-free closure of the target.

## No longer needed

Removed the first worker's AffineEtaleRestrictionExists and AffineEtaleRestrictionCompatibility modules and their circular nodes; these were never in the repository. The old proof dependencies def-weil-pbc-composite-adjunction and lem-weil-pbc-conjugate-iso-unit-equation are no longer directly used: the generic inverse-mate proof uses natural Hom bijections and the target uses def-weil-pbc-adjunction-mate. No original public import is removed. FullAffineEtaleTopos remains needed for inclusion continuity, and its role in the restriction comparison remains on the route. The sk-thm-iff unit realized fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's compatibility lemma asserted unit compatibility for every comparison isomorphism. This is unjustified: an arbitrary isomorphism can be modified by a natural automorphism, whereas the adjunction chooses a specific unit-compatible isomorphism. Its two new nodes also depended on the target itself, creating a cycle. Both were removed. The report's claim that the composite-adjunction and conjugate-unit nodes lacked usable declarations was misleading: both are Mathlib leaves with explicit mathlib_match records. Mathlib's mate unit equation is used in the repaired reduction instead.

Searches used launcher msearch.py (leansearch unavailable, leanfinder, loogle and grep successful), plus project and upstream source searches. Mathlib's affine-spectrum sheaf equivalence concerns an induced topology, whereas our full affine site has its finite-cover topology. Existing FullAffineEtaleTopos only states the set equivalence at Type u, so the Type (u+1) obligation is distinct. Upstream's forward-mate invertibility theorem does not directly state the inverse-mate result; the latter was proved by Hom bijections.

## New nodes

lem-stage3-affine-etale-restriction-large-sets: the sole open theorem, full affine restriction at Type (u+1), from Stacks 04HR/03A0. Its docstring gives the affine refinement, induced topology and gluing construction. Its node records source, proof steps, real searches and exact Lean signature.

lem-stage3-inverse-mate-equivalences: fully proved generic invertibility of an inverse mate when the vertical functors are equivalences. The proof constructs Hom bijections, identifies them by the mate unit equation and naturality, and applies the coyoneda criterion. Its node records this actual proof route. No change record is needed: no existing signature or definition changes.

## Second reading by J1

1. I compared the delivered target module with `lean/Sheaf/AlgebraicGeometry/AffineEtaleRestrictionUnit.lean`; the theorem signature is byte for byte unchanged. The two former split theorems were circular restatements and were removed.

2. I compiled all delivered modules with `lcompile.py --all`. The target and the new generic inverse-mate theorem compile; the only remaining `sorry` is the named theorem `fullAffineEtale_large_sets_equivalence`, recorded by node `lem-stage3-affine-etale-restriction-large-sets`. A probe reports only the permitted standard axioms plus `sorryAx` through that open theorem.

3. The generic inverse-mate statement is true and strictly supports the target: its proof is a natural Hom-bijection argument using `unit_mateEquiv_symm`, and it does not restate the target. The restriction equivalence statement is the universe-sensitive site comparison needed by the target, with its full source and proof obligation documented in its docstring and node.

4. The target now follows the unit route through the full affine étale restriction equivalence, the continuous base-change square, and the inverse mate. The old circular existence and compatibility nodes and modules are no longer needed. The remaining open node is precisely the larger-universe restriction equivalence.

5. DAG `proof`, `proof_deps`, and `proof_origin` now match the Lean route. Imports were pruned: the two circular split modules and the unused `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` import were removed; proof-only imports are plain imports. The unit record realizes its statement and step by lemma-weil-pbc-property-iff-acyclicity; this auxiliary target is below that unit and its prescribed restriction/adjunction route is kept.

### Changes made

Removed `AffineEtaleRestrictionExists.lean` and `AffineEtaleRestrictionCompatibility.lean`, added `CategoryTheory/InverseMateEquivalence.lean` and `AffineEtaleRestrictionLargeSets.lean`, and replaced the target proof with the mate/unit reduction. Updated the target node and added nodes `lem-stage3-inverse-mate-equivalences` and `lem-stage3-affine-etale-restriction-large-sets`.

The new nodes are `lem-stage3-inverse-mate-equivalences` (proved) and `lem-stage3-affine-etale-restriction-large-sets` (the sole open theorem).

Edge cases checked: when the vertical functors in the generic lemma are identities,
it reduces to the usual conjugate isomorphism; empty categories make its component
assertion vacuous. The proof's explicit Hom equivalences cover arbitrary adjunction
units, including twisted choices, so it makes no claim about arbitrary comparison
isomorphisms. For the affine-site obligation, an empty scheme has its empty covering,
forcing singleton sections, and both sheaf categories are terminal up to equivalence;
nonempty affine objects use identity covers and finite affine refinements, without
assuming the base scheme is affine or quasi-compact.
