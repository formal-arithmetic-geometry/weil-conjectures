## What changed

Proved the original `AlgebraicGeometry.ProEtale.properEtaleOriginScalarIsomorphism`
from a separate qcqs projection-square compatibility. The Lean assembly cancels
canonical source isomorphisms to obtain the exact required formula, applies the
proper torsion projection formula to the finite ring A, removes the invertible
direct-image restriction factor, and reflects the resulting isomorphism through
exact scalar restriction using all homology functors. The proper torsion argument
and derived conservativity are proved private helpers. No flatness, Noetherian,
finite Tor dimension or additional boundedness assumption was introduced.

Extracted the eight supporting definitions verbatim into
`Sheaf.Paper.ProperEtaleOriginScalarData`; the original module publicly reexports
them and retains the same original public-import closure. Their expressions,
signatures, attributes and visibility were checked against the original source.
The extraction avoids a dependency cycle for the independent qcqs square; it is
not a compile-time workaround. The existing theorem signature is unchanged.

The new `Sheaf.Paper.EtaleOriginScalarProjectionSquare` states the compatibility
for qcqs morphisms, without properness or an invertibility assertion. Its complete
proof in words specifies specialization of the existing fixed-coefficient square,
transport through the section-normalized realization, K-flat representative
identifications, and the published scalar-mate normalization. This is the remaining
mathematical obligation, not an assumption that the proper mate is invertible.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.properEtaleOriginScalarIsomorphism`
(node `lem-fix-proper-etale-origin-scalar-isomorphism`). Its proof is complete
relative to the imported declarations.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.etaleOriginScalarProjectionSquare`
(node `lem-fix-etale-origin-scalar-projection-square`). Its proof is exactly
`:= by sorry`. It is the properness-independent canonical-map compatibility,
strictly one part of the argument. It does not assert the original conclusion or
assume any projection map invertible. The original proof genuinely supplies the
proper projection theorem, rearrangement, and derived reflection step.

This delivery is a decomposition: one old hole closed, one lower hole added,
net zero holes. The data module has zero holes. No definition contains a sorry.
The original theorem is not claimed axiom-free independently of its dependencies.

Validation: remote all-file compilation succeeded for the data module (7.9 seconds),
the square statement (6.7 seconds), and the original module with both private
helpers (9.2 seconds). Final delivery performs the required checks.

## No longer needed

Removed direct proof imports from the original item:
`WeilConjectures.AlgebraicGeometry.ProperBasic`,
`Sheaf.SixFunctors.GeometricInverseImageConstantModule`, and
`Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale`.
Mathlib proper-morphism instances supply qcqs directly, so `pqf-lem-proper-basic`
is unnecessary to this proof. The generic geometric constant-module and projection
comparison nodes are still needed by the lower compatibility proof and are not
claimed globally pruned. Their dependency is recorded on the new square node.
The canonical mate and tensor-pullback interfaces are retained by the unchanged
data definitions and by that square; they are not pruned.

The original public imports have been factored through the publicly imported data
module, preserving the original public closure. No Lean module is withdrawn, and
no source-library declaration or proof is removed. No parent or unit route is
bypassed. Consequently the globally pruned-module list is none.

## Where the brief, the DAG or earlier work was wrong

The proper projection formula and conservative restriction fit directly. The
fixed-coefficient projection-comparison theorem does not itself state the square
in intrinsic constant-ring modules. In particular, the selected section-normalized
realization/direct-image isomorphisms and the selected scalar/tensor comparisons
must still be identified with the transported arrows. Merely applying the generic
projection square cannot close that equality by cancellation. The new qcqs lemma
records this missing, independently sourced compatibility rather than asserting
it follows definitionally. Its edge cases include zero rings, empty schemes and
identity maps, and its proof uses only the stated bounds on E and E tensor B. For a zero ring,
the module categories are zero categories and both arrows coincide. For an empty
source scheme the same argument applies after direct image. For identity scheme
maps the square is the naturality of the canonical q identification; its factors
need not be definitionally identities. These checks introduce no hypothesis that
would imply flatness of B. The normalization theorem is explicitly unbounded, so
its input R_e E requires no additional bound on scalar extension.

No statement was found false, and no target statement or supporting mathematical
definition is repaired or weakened. Searches of the source library, Sheaf, Mathlib,
and the imported blueprint found no matching intrinsic compatibility theorem.

## New nodes

`def-fix-proper-etale-origin-scalar-data` attaches the eight unchanged supporting
constructions to their new module. It creates no mathematical choice and has no
proof hole. The original theorem node retains its statement and now records the
actual assembly proof and its three dependencies.

`lem-fix-etale-origin-scalar-projection-square` is the qcqs canonical-map square
specialized to B as the constant A-module. Source: Stacks Tags 0E48 and 0B56,
with the canonical etale/pro-etale comparisons (09A6). Its complete proof in words
and Lean signature are recorded, including the realization-normalization step.

Change record: `coord/changes/W6-proper-etale-origin-scalar-data.md`.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
