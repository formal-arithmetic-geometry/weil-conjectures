## What changed

Replaced the sole proof hole in `native_ordinary_representative_currying` with a direct native
module-object tensor–Hom calculation. Private helpers construct the signed equivalence of cochains,
prove compatibility with the differential and homotopies, prove K-injectivity of product Hom from
acyclic-test K-flatness, and build the representative Hom bijections. Functorial flat resolutions
and K-injective localization let fully faithful restriction extend these natural bijections to all
derived objects. The restriction equation gives the specified uncurried representative and its
unsigned homogeneous counit formula. The public signature and public imports are unchanged.

The calculation of cochains follows the proved private calculation in the downstream
`KFlatBifunctorTensorHom` module. That module cannot be imported because of its path through this
item; the required generic calculation is re-established locally. The private total tensor
comparison in `NativeOrdinaryTensorRepresentatives` supplies the connection between acyclic-test
K-flatness and functorial K-flat resolutions. No new public definition or theorem is introduced. The existing Grothendieck K-injective
resolution theorem supplies the target localization. The generic assembly uses K-flatness only
for P; the original additional Q hypothesis is retained unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_representative_currying`.
All private helpers have complete proofs. Holes left: zero. Holes added: zero. No split-off
statement is added. The supplied arbitrary natural tensor model and supplied Hom representatives
are used in the equivalence itself, so the final normalization is preserved.

## No longer needed

The original planned proof dependencies `lem-sf-native-scalar-forgetting-equivalence`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`, and
`lem-sf-ringed-derived-tensor-hom-adjunction` are not used by this proof. The argument stays in
native module objects, rather than changing ambient scalars or comparing section rings. None of
their modules is added as a direct proof import. They may still occur in the transitive public
imports of the fixed statement module; no claim is made that they leave the target closure.

No existing public import is removed, no module is withdrawn, and no unit route is bypassed.
The current unit record has no realized step assigned to this refinement. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The original node planned transport through the ringed-site adjunction, but the library already
has the native underived parametrized adjunction and the total tensor comparison needed to prove
the result directly. Its only missing work is the explicit chain/homotopy calculation and descent,
which this delivery supplies. No false statement, statement change, definition repair, or shared
consumer adaptation was needed. Zero complexes, the empty scheme, and unbounded inputs require
no extra hypotheses.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
