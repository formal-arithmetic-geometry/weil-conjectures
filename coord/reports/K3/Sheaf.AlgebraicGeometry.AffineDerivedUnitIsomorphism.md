## What changed

Filled `AlgebraicGeometry.affineDerivedUnit_isIso` by applying
`DerivedCategory.isIso_iff` and reduced the degreewise calculation to the new
public theorem `affineDerivedUnit_homology_isIso`. Added its module and DAG node.

## Proved and sorry left

The target theorem `affineDerivedUnit_isIso` is proved. The new theorem
`affineDerivedUnit_homology_isIso` remains sorry as a strictly smaller
cohomology-level calculation (node `new-affine-derived-unit-homology-isIso`).

## No longer needed

No imports were removed. The target's existing proof-dependency imports remain;
the helper imports only the derived-category and affine sections comparison
interfaces needed to state the reduction.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omits a separately stated degreewise unit calculation. The
reduction exposes that missing step explicitly rather than leaving a partial
proof with an anonymous sorry.

## New nodes

`new-affine-derived-unit-homology-isIso`, in
`dag/nodes/sec-picard-framework/new-affine-derived-unit-homology-isIso.json`.

## Earlier second reading (a previous round; superseded)

The target module and the helper module were compiled together. The target proof
uses exactly `DerivedCategory.isIso_iff` and the helper's degreewise statement;
the helper has the same hypotheses and objects as the target and is strictly
smaller. The remaining sorry is named and documented, with a matching DAG node.

## Second reading by K3

1. Compared the delivered item module against the repository version. The theorem signature is byte-for-byte unchanged; only its proof and the proof-only helper import were added. The helper is a new module and does not alter existing declarations.

2. Compiled all sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The item theorem has no `sorry`; the only remaining `sorry` is the named helper theorem `affineDerivedUnit_homology_isIso`, which is documented and has node `new-affine-derived-unit-homology-isIso`. No definitions contain `sorry`, and no forbidden declarations were introduced.

3. The helper statement is a genuine degreewise reduction of the target and is strictly smaller (it concludes only `IsIso` after applying homology in one degree). Its source and proof sketch are recorded in the docstring and DAG node. It is not duplicated by an existing declaration found by repository search. The target proof uses the standard `DerivedCategory.isIso_iff` criterion.

4. The proof follows the unit route through the degreewise homology calculation. No existing imports were removable: the public interfaces remain required by the statements, while the helper's comparison import is proof-only. The old target proof dependency is replaced by the new helper node in the target node.

5. The target and helper declarations match their DAG `lean.statement` fields. The unit `sk-thm-picard-f-representable` and its realized route are preserved; the helper is a split lower step for the unit calculation. I changed only the target proof, added the helper module and node, and added this review record.
