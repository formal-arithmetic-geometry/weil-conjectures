## What changed

Repair of return fcca1ddba: removed the unused `set_option warn.sorry false`. The landing
ledger matched the option name at line 44 as an unattributed hole; it was not a proof hole.
Both delivered modules now contain no hole tokens, and warning suppression is unnecessary.
The returned proof, declarations and node attachments are retained.

Proved `AlgebraicGeometry.nodal_subcurve_boundary` from the existing complementary-component,
reduced-image and nodal-subcurve declarations. The original theorem signature and all three
complement/boundary definitions are unchanged. Added private helpers for reduced closed-subscheme
uniqueness, completion transport, smooth-locus neighbourhoods, rational residue fields, and scalar
compatibility. Added the proved generic theorem `MvPowerSeries.nodal_coefficient_straightening` in
`Sheaf.RingTheory.NodalCoefficientStraightening`: residue-surjective coefficients in the standard
node are conjugate to the standard coefficients by an automorphism. All new imports are private.

The two complement constructions are compared as reduced closed immersions with equal ranges.
Pasting pullback squares gives the actual boundary isomorphism and preserves both projections.
Applying the existing nodal theorem in both complementary orders proves smoothness on both sides.
No other group's module is changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.nodal_subcurve_boundary`
(`lem-trf-nodal-subcurve-boundary`). Added zero holes. The new theorem
`MvPowerSeries.nodal_coefficient_straightening` is proved, as are all private helpers.
No `sorry` remains in either delivered Lean module. The main theorem uses the existing
`stacks_nodal_closed_subcurve`, `complementary_pure_subcurve_components` and
`schemeTheoreticImage_reduced` declarations; their existing holes are outside this packet.

## No longer needed

`lemma-nagata-scheme-image-restrict-open` is not used: open embeddings commute with taking the
closure of the complementary range, and reduced closed immersions with equal ranges are
canonically isomorphic. Its old tool-use approval is removed from this node. Removed the unused private import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` and the
redundant private `Mathlib.AlgebraicGeometry.Morphisms.Separated` import. No module is
withdrawn. All other declared geometric dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

Step 5 silently treated an abstract completed-local-ring isomorphism as scalar compatible.
The claimed general nodal theorem requires an explicit scalar identity. The new coefficient
straightening argument supplies this identity without changing that theorem's signature.
Empty schemes, empty complementary components and the empty boundary are handled by the same
pullback/isomorphism constructions; no nonemptiness hypothesis was added.

## New nodes

`lem-trf-nodal-coefficient-straightening`: a separate generic local-algebra result about a
coefficient field in the standard split node, proved using power-series evaluation, completeness,
and stabilization of the kernels of a surjective Noetherian ring endomorphism. It is used only
to reconcile the original abstract ring hypothesis with the existing scalar-compatible nodal
input. No definition or statement repair is required. The option-command removal is recorded in
`coord/changes/nodal-subcurve-boundary-warning-option.md`, including the downstream inventory,
because preflight classifies that file-level command as an interface change.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
