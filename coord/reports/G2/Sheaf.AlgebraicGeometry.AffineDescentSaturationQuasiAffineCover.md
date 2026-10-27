## What changed

Proved `CategoryTheory.Over.DescentDatum.affine_descent_saturation_quasi_affine_cover`
with its statement unchanged. A proved private helper constructs the relation involution
from transport and its cocycle, then proves that `D.toHom` is open. The main proof constructs
each open as the actual range, proves compactness by continuous image, proves containment
using the diagonal lift and `transport_self`, and applies the existing Zariski main theorem
quasi-affineness result. Supremum monotonicity gives the covering.

Replaced the two private proof imports `IsLocallyQuasiFiniteResLE` and
`LocallyOfFiniteTypeOfIsLocallyQuasiFinite` by
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`. All public imports,
existing signatures, and upstream modules are preserved. Updated the existing node's proof
and dependencies to describe this implementation.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Over.DescentDatum.affine_descent_saturation_quasi_affine_cover`
(node `lem-trf-affine-descent-saturation-quasi-affine-cover`).
No holes added, no holes left, and no split-off statements. The private helper is proved.
The final file compiles through `lcompile.py` in 5.3 seconds without warnings.
The original theorem signature is textually unchanged; the new import passes the
import-cycle check. The required delivery preflight checks axioms as well.

## No longer needed

Removed the direct proof imports
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE` and
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`.
The former node `lem-weil-pbc-lqf-restriction-to-opens` is not needed by this argument:
Mathlib composition instances restrict both properties after the comparison theorem.
The local finite type result remains an indirect dependency of the comparison theorem;
its module and node are not claimed as pruned. No module is withdrawn, and no other
planned mathematical dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's geometrical argument is valid. The transport
interface already includes normalization (`transport_self`), so no separate proof
of diagonal normalization is needed. The comparison theorem gives both Mathlib
hypotheses needed for quasi-affineness, and standard composition instances replace
the explicit restricted Stacks-sense quasi-finiteness lemma. The unit route is preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
