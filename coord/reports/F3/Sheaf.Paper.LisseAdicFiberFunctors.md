## What changed

Replaced the only remaining proof hole in `Sheaf.Paper.LisseAdicFiberFunctors`,
`AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`, with a complete proof
from one strictly smaller coefficient-endomorphism theorem. All existing declaration
signatures, definitions and visibility are unchanged. This is a decomposition, not a
net reduction in the number of holes.

Constructed the integral scalar comparison using finite-level stalk comparison and
adic reconstruction. Proved its germ formula, uniqueness and naturality. Proved that
its reductions are the expected quotients and that completeness makes the comparison
an isomorphism. Rationalized the comparison and proved naturality on arbitrary rational
arrows by clearing denominators; no additivity hypothesis on the selected rational
fibre functor was silently assumed.

Transported the rational comparisons to the actual coefficient diagram. Proved a
generic normalization theorem which obtains both coherence laws from bijectivity on
natural endomorphisms after precomposition from a least object. Applied it to the
least finite coefficient field, using the new remaining theorem described below.
Constructed the functor on the Grothendieck construction, proved that it inverts
cocartesian arrows, and descended it through the explicit localization. Constructed
the rational-model natural isomorphism and proved the exact inverse pure-tensor
formula required by the original statement.

Added seven supporting modules and seven nodes. Added only proof imports to the
existing module. The supporting modules use public imports only for their statements
and definitions; imports needed solely for proofs remain private. The existing node's
proof, proof dependencies and proof origin now describe this route.

All eight sandbox modules compile together through `lcompile.py --all`; the slowest
is the original module (37 seconds), followed by the rational comparison (16 seconds).
No Lean warnings were emitted. Every new Lean line is at most 100 characters.
The delivery dry run also passes compilation and preflight, with review class CODEX.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`.
There were one original hole and no other original holes to close; the six holes
previously closed by J1 remain closed without changes to their proofs.

Added exactly one hole:
`AlgebraicGeometry.Scheme.lisseCoefficientFiberEndomorphisms_whisker_bijective`,
in `Sheaf.Paper.LisseCoefficientFiberEndomorphisms`, node
`lem-pod-lisse-coefficient-fiber-endomorphisms`. Its proof is exactly `by sorry`, with
its source, edge cases and complete natural-language argument in the docstring.
It still needs the construction of restriction of coefficients on rational lisse
sheaves, the comparison of its geometric fibre, and the separability-idempotent
argument extending and detecting natural endomorphisms. This is a statement about
endomorphisms under a single coefficient transition, with no algebraic localization,
choice of coherent comparisons, or prescribed object-value theorem in its conclusion.
It is strictly a part of the argument, not a repackaging of the original theorem.

Thus this delivery closes one upper hole and adds one lower hole: one decomposition,
net zero holes closed. The original module has zero holes; the entire delivery has
one. Existing imported theorem holes are used as the stage requires; no claim of an
axiom-free completed target is made.

The six other new supporting modules have no holes. Their principal proved results
are `lisseIntegralScalarFiberComparison_exists`,
`lisseIntegralScalarFiberComparison_reductions`,
`lisseIntegralScalarFiberComparison_isIso`,
`lisseRationalFiberComparison_naturality`,
`lisseCoefficientFiberComparisons_exists`, and
`CategoryTheory.Pseudofunctor.coherentFiberComparisons_of_endWhisker`.
The map is selected only from its proved unique-existence theorem; no new definition
selects arbitrary data from an unproved existence statement.

## No longer needed

No existing library module, declaration, or original import is pruned. The assigned
node originally had no proof dependencies or proof steps, so there is no unused
stated route to remove. All dependencies introduced in the updated node are used.
No unit statement or realized proof step is bypassed.

The original module needs only the direct proof import
`Sheaf.Paper.LisseCoefficientFiberComparisons`: the integral isomorphism is used
through the rational comparison dependency. No separate direct import of
`Sheaf.Paper.LisseIntegralScalarFiberIsomorphism` is needed there. This removes an
experimental import from this session, not an import of the shared library.
The rational comparison module also omits a redundant direct public import of
`LisseScalarFiberMaps`, already publicly imported by its integral-isomorphism dependency.
The integral isomorphism proof uses completeness of finite modules and quotient
comparisons; it does not require a separate finite-free scalar-extension theorem.

## Where the brief, the DAG or earlier work was wrong

The assigned node supplied no proof plan (`proof` and `proof_deps` were empty).
The geometric comparison and localization argument above therefore supply the
missing route; all existing stated dependencies were read and retained.

The coefficient diagram interface records its category values and arrow functors,
but it does not prescribe formulas for its `mapId` and `mapComp` constraints.
Consequently canonical tensor comparisons cannot simply be asserted to satisfy those
particular constraints. The proved normalization theorem uses the actual recorded
constraints and their pseudofunctor axioms. The remaining endomorphism theorem is
what permits that normalization; the distinction is explicit in its statement and
in the node proof.

A shortcut through the rational representation equivalences would import the
assigned module itself through `GaloisLisseRepresentationData`, making a cycle.
Searches found no existing adic restriction-of-coefficients interface supplying the
remaining density argument. Ordinary sheaf coefficient restriction and derived
condensed coefficient comparisons have different signatures.

No existing statement or definition was repaired, weakened, or disputed, and no
forced adaptation of another group's module was made.

## New nodes

`lem-pod-lisse-integral-scalar-fiber-map`: canonical integral scalar map, its
uniquely specified germ formula and naturality; module `LisseScalarFiberMaps`.

`lem-pod-lisse-scalar-fiber-reductions`: surjectivity and ideal-power kernel of
each reduction of that map; module `LisseScalarFiberReductions`.

`lem-pod-lisse-integral-scalar-fiber-isomorphism`: completeness and reduction
comparisons prove the integral map invertible; module `LisseIntegralScalarFiberIsomorphism`.

`lem-pod-lisse-rational-scalar-fiber-comparison`: rational comparison and
naturality by clearing denominators; module `LisseRationalScalarFiberMaps`.

`lem-pod-lisse-fiber-coherence-normalization`: the generic proved categorical
normalization lemma; module `LisseFiberCoherenceNormalization`.

`lem-pod-lisse-coefficient-fiber-endomorphisms`: the sole remaining hole,
detection and extension of natural endomorphisms from the least coefficient field;
module `LisseCoefficientFiberEndomorphisms`.

`lem-pod-lisse-coefficient-fiber-comparisons`: transport and coherent normalization
of the rational comparisons; module `LisseCoefficientFiberComparisons`.

All new nodes are in `dag/nodes/sec-poincare-duality/`, retain unit `sk-lem-finite`,
and trace their blueprint ancestry to `cor-galois-lisse-representations` through
`def-pod-lisse-adic-fibre-functors`. No change record is needed: no existing signature
or definition changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
