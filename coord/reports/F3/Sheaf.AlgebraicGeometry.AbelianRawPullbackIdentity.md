## What changed

Proved `AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_identity` with its
original signature and docstring. The proof substitutes the identity scheme map and coefficient
map, expands the raw factors, applies the sheaf left unit law, and cancels the derived identity
comparison using its single-complex and shift compatibility.

Repair of the returned duplicate-statement finding: removed the local `single_hom` and
`complex_single_natIso` declarations. Also removed the local `derived_single_natIso` and
`plus_single_natIso` helpers, whose proofs are already available in the same existing module.
Added the proof-only `import all Sheaf.AlgebraicGeometry.AbelianHigherDirectImageCoreComp`
to use its private `AlgebraicGeometry.Etale.single_hom` and
`AlgebraicGeometry.Etale.plus_single_natIso` directly. The latter uses the existing complex
and derived compatibility lemmas. No existing module is adapted and no helper is reproved.
The local `id_single`, `identity_commShift` and `identity_single_shift` remain fully proved.
The two public imports and the public interface are unchanged.

Updated the item's DAG proof and proof dependencies to record this reuse. The unit
`sk-lem-failure-field` has no realized entries for this node; its route is unchanged.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_identity`
(node `lem-sbc-abelian-raw-pullback-identity`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
Every remaining private helper has a complete proof; no statements are split off.

## No longer needed

Removed original proof-only import `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
and node `lem-weil-pbc-derived-inverse-image-composition`: the full derived composition
conjunction is not needed for the identity law. The redundant proposed proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` remains absent.

Pruned four duplicate local helpers: `CategoryTheory.Functor.single_hom`,
`CategoryTheory.Functor.complex_single_natIso`, `CategoryTheory.Functor.derived_single_natIso`
and `CategoryTheory.Functor.plus_single_natIso`. Their existing implementations in
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageCoreComp` are reused. No other original
import is removed; that module and its node are now required by the actual proof.
Pruning of the derived-composition module is local to this item.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two statements already present in
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageCoreComp`. The earlier assessment that
private single-complex helpers had to be adapted locally was wrong: Lean's proof-only
`import all` permits their reuse without exposing them to importers. Both returned duplicates
and the two subsequent compatibility helpers have now been removed. The earlier second-reading
section described the returned version and has been removed for a fresh independent reading.

No false statement or changed interface was found. The original DAG's full derived-composition
conjunction is stronger than needed. Zero objects, zero classes, empty schemes and degree zero
need no additional hypotheses.

## Second reading by F3

1. **Unchanged interface: pass.** Compared the only delivered Lean module against the
repository with `diff`. The existing public theorem signature is byte for byte unchanged,
including `ha`, the arbitrary triangle witness `w`, `hφ : HEq`, and every scheme, sheaf,
degree, test object and class parameter. Its docstring is unchanged. No definition is
changed or added. The two public imports remain identical; the changed import is proof-only.

2. **Proof and trust: pass.** Compiled the delivered module with `lcompile.py`: no errors
or warnings (30.6 seconds). A fresh scratch copy of the delivered version with
`#print axioms` for `id_single`, `identity_commShift`, `identity_single_shift`, and
`AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_identity` compiled cleanly.
Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
Scanned the delivered Lean for holes and forbidden declarations: none. The three private
helpers have complete proofs and introduce no data chosen from an unproved existence claim.
Read the cancellation: the shift equation and naturality move the derived identity
component next to the source comparison, then both comparison pairs cancel.

3. **Split statements and reuse: pass.** No new public statement, split-off hole, or new
node is delivered. Read `single_hom`, `complex_single_natIso`, `derived_single_natIso`,
and `plus_single_natIso` in `AbelianHigherDirectImageCoreComp`: all are proved, and the
first and last are reused through `import all`, rather than copied. Checked the remaining
helpers on the identity endofunctor, zero source or target and zero morphism; the argument
uses naturality and inverse identities without exclusions. Any integer shift is allowed,
so degree zero, zero sheaves and empty schemes require no extra hypothesis.

4. **Route and pruning: pass.** Read the proof from the public theorem downward:
substitution of the identity data, `upperStarComp_id_left`, and the generic
`identity_single_shift` calculation. Searched `lean/` for the derived identity and shift
comparison names and ran `msearch.py ... grep 'mapDerivedCategoryPlusIdIso'` (no Mathlib
hits). Nearby `HigherDirectImageTransitionIdentity.single_iso_id` combines identity and
single compatibility for a different direct-image argument; it does not supply the shift
cancellation here. No shorter complete route was found. All three imports are used; the
core-composition import supplies private compatibility lemmas and the public imports
supply the existing signature and sheaf unit law. The old proof dependency
`lem-weil-pbc-derived-inverse-image-composition` and its removed import are explicitly
listed under No longer needed. Read `dag/units/sk-lem-failure-field.json`: both its
statement and step realized lists are empty, so this change bypasses no realized unit node.

5. **DAG and Lean: pass.** The only node changes are `proof`, `proof_deps`, and
`proof_origin`. The proof-dependency list equals the union of the steps' uses: the sheaf
composition law and the core-composition module carrying the reused private proofs.
The four steps describe the actual substitutions, single comparison, shift descent and
cancellation. The node statement and Lean record remain unchanged. No new-node fields
or change records are needed.

Second reading changed only this report, adding the independent checks above.
No repair to the delivered Lean or node was necessary. Confirmed holes closed: 1;
holes added: 0; split off: 0. The Lean4 skill was used for proof and axiom review;
compilation remained exclusively through the launcher required by the brief.
