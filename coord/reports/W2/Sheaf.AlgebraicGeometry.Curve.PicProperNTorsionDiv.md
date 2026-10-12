## What changed

Proved `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_div` in
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv`, preserving its signature and public imports.
The proof obtains geometric integrality from geometric connectedness and smoothness, applies
`exists_jacobian`, installs the resulting abelian-variety instance, and transports an nth root
from clause (d) of `abelianVariety_estimate_of_isAlgClosed` through the group equivalence.
Updated `lem-sc-pic-proper-ntorsion-div` to record that proof route.
Added the proof import `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`.
The Jacobian and abelian-variety units remain used through their stated unit theorems.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_div` (node
`lem-sc-pic-proper-ntorsion-div`): one of one original sorries removed. No new statements or
sorries. Its existing Jacobian and abelian-variety dependencies still have transitive sorries;
this delivery reduces to those established interfaces as intended in stage 3.
The hypothesis on n excludes zero; n = 1 works by the same transport. Connectedness excludes
empty curves, and dimension one is used to establish smooth relative dimension one.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.Variety`
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`
- `WeilConjectures.AlgebraicGeometry.DensePoints`
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`

The local proof does not need nodes `lem-sc-pic-proper-decomposition`,
`lem-sc-proper-dim-one-projective`, `def-pc-curve`, `def-pc-smooth-projective-curve`,
`lem-pc-rational-points-dense`, `prop-pc-xk-integral`, `def-sc-jacobian`,
`def-sc-genus`, or `lem-pc-genus-agrees-sc`. This is local pruning: some removed direct imports
remain transitive dependencies of the Jacobian or abelian-variety modules, and no claim is made
that they are globally unreachable. In particular RiemannRoch remains transitively imported;
the proof uses its arithmetic genus only as the relative dimension provided by exists_jacobian,
without invoking genus equality. No explicit projectivity instance or rational point is needed
by the existing exists_jacobian signature.

## Where the brief, the DAG or earlier work was wrong

The old proof plan and original declaration docstring describe a longer valid route through
projectivity, a rational point, and a genus comparison. The existing Lean representability
statement accepts properness, smooth relative dimension one, and geometric integrality
without those extra steps. Divisibility does not involve the Jacobian dimension.
The original `prop-pc-xk-integral` attachment lists base-change smoothness/properness/reducedness
and global-sections results; it is not itself a direct geometric-integrality bridge. The proof
uses the already proved geometric-connectedness and regularity results instead.
Mathlib searches (LeanFinder, Loogle, grep) were run; no general curve Picard divisibility
shortcut was found. No statement or definition was changed, and no new nodes were added.

## Second reading by W2

1. Compared the delivered module with the repository version: the theorem signature and all
existing declarations are unchanged byte for byte; only proof imports and the proof body differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the file contains no
`sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The proof uses only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the last comes from existing
open dependencies, not a new sorry in this delivery.
3. Checked the reduction and its edge cases: `n > 0` follows from the nonzero characteristic
image, and the same transport works for `n = 1`; membership is preserved by the subgroup
bijection. The theorem statement remains exactly the target statement, with no split-off claims.
4. Checked the proof from the top downward and pruned imports and dependencies that are unused;
the Jacobian and abelian-variety unit interfaces remain on the route. No shorter Mathlib route was
found in the recorded searches.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof and verified
that the unit route is retained; no new nodes or change records are needed.

Updated the theorem docstring to describe the actual geometric-connectedness reduction,
and added this second-reading record with the explicit axiom result. No proof or DAG repair
was necessary.
