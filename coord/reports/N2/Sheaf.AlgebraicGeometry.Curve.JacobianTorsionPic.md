## What changed

Proved `AlgebraicGeometry.Scheme.Hom.jacobian_torsion_pic` in
`Sheaf.AlgebraicGeometry.Curve.JacobianTorsionPic` without changing its statement.
The inclusion is the inverse of the group-compatible rational-point comparison followed
by the degree-zero subgroup inclusion. Divisibility uses `surjective_npow_points` for
all positive integers. The kernel universal property identifies scheme torsion with
pointwise torsion, and the torsion-free integer degree puts every Picard torsion class
in that inclusion's image. The quotient calculation uses the existing degree-compatible
product decomposition and the first isomorphism theorem; its value on every representative
is proved to be degree modulo n. Updated the existing node's proof description to record
this product-coordinate implementation of the cokernel argument.

Single-file compilation via `lcompile.py` passed without warnings. All positive n are
covered, including n=1 and multiples of the characteristic; no invertibility assumption
was introduced. The genus-zero case uses the same argument. No source-library module,
public import, definition, signature or consumer was changed.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.Hom.jacobian_torsion_pic`
(node `det-cor-jacobian-torsion-pic`).

Holes added: 0. Holes remaining in the delivered module: 0. No split-off statements.
The proof uses existing library theorems, whose remaining transitive proof obligations
are not claimed as closed by this delivery.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.Picard.Scheme`: the specific rational-point and
multiplicativity comparisons are available through the existing public Jacobian import.
Only the two used private proof imports remain: `Curve.PicardDecomposition` and
`AbelianVariety.Isogeny`. No public import was removed.

No planned proof-dependency node is pruned: `sk-thm-picard-main`,
`lem-sc-pic-proper-decomposition`, `lem-sc-isogeny-surjective` and `sk-def-av-mult-n`
all supply parts of the proof. No module is withdrawn. In particular, the removed direct
import does not claim that its module is absent from the transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing prime-to-characteristic Picard torsion and
cokernel theorems do not provide this theorem's all-positive-n statement or its specified
inclusion and representative formula. Their algebraic proof pattern was reusable, with
divisibility taken directly from the all-positive-n isogeny theorem. The DAG's elementary
cokernel chase is implemented using its already-declared split degree sequence, with
no change to the unit route and no new dependency.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
