## What changed

Implemented the ordinary realization by comparing direct-image scalar actions and taking
adjunction mates. Constructed the underlying inverse-image isomorphism from scalar extension
along the specified ring isomorphism. Constructed the ringed monoidal pullback from its existing
coherence equations, transported it through scalar restriction, and checked its generalized
pure-tensor normalization. The braided-to-monoidal coherence calculation is proved
privately from the standard monoidal-functor constructor. Local irreducibility keeps the large sheaf tensor
structures behind their APIs; the equivalence transport takes an abstract quasi-inverse to
avoid unfolding a chosen inverse during normalization. A private scalar-value API keeps chosen
sheafification functors behind their naturality equations. The scalar operation calculation is
a proved private lemma; tensor equations are composed directly to avoid repeated dependent
rewriting. All new helper declarations are private and proved. The target statement and all
public interfaces are unchanged.

## Proved and sorry left

Closed: `CategoryTheory.ConstantModuleDerivedProjection.constant_module_ordinary_realization`
(the module's one original hole). Added holes: none. Remaining holes in this module: none.
The proof uses the existing stated scalar-restriction and ringed tensor interfaces; their
upstream holes are not new holes in this delivery.

Validation: individual scalar, mate and tensor calculations were checked through `lcompile.py`;
`deliver3.py` runs the final complete compile and axiom probe.

## No longer needed

The planned fresh construction of an ordinary ringed module adjunction is unnecessary:
`GeometricData` already supplies both module adjunctions and their normalized Hom equations.
Thus the proof does not invoke `lem-weil-pbc-ringed-topoi-module-adjunction`.
The proposed new balanced tensor and sheafification coherence argument is replaced by the
proved `ModuleTensorMonoidalEquations` and `CochainComparisonMonoidalEquations` APIs, together
with the given `ringTensor.pure`. No direct invocation of
`def-weil-pbc-ringed-tensor-section-calculus` is needed here. These nodes may remain needed by
other consumers; no module is withdrawn.

The ring-isomorphism tensor transport module is unnecessary here: its elementary ordinary
coherence calculation is proved locally without importing its derived transport theory.
No module is withdrawn for this reason.

No original import was removed: `ConstantModuleDerivedComparisonData` is the statement's
public interface. Added proof imports are private. No new public lemma or DAG node is added.

## Where the brief, the DAG or earlier work was wrong

The constant-scalar geometric adjunction helper uses constant RingCat sheaves, whereas this
item's datum uses the underlying RingCat sheaf of a constant CommRingCat sheaf. Applying that
helper directly does not typecheck. The proof compares the two scalar-section presentations
using `constantCommuteCompose` and the sheafification-unit equations, then repeats the existing
linearity calculation with the required presentation. No definition or statement repair is
needed. The node's proof and dependencies now record the actual mate and tensor transport.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
