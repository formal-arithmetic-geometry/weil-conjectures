## What changed

Proved all four open theorems in
`lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteModules.lean`.
The coefficient constants are locally injective by evaluation on any point of a
nonempty scheme; for an empty scheme the empty sieve is covering. For local
surjectivity, pull a continuous function back from connected components, take its
open level sets indexed by points of the underlying scheme, and apply the existing
`Scheme.ProEt.mem_topology_of_openImmersion`. On each level set its restriction is
the appropriate constant function. Compose with the locally bijective
sheafification unit.

A fully proved private helper identifies the specified realization functor as an
equivalence for a locally bijective map out of a constant ring presheaf. Encoding
module-valued presheaves is fully faithful. The module-sheafification unit is an
isomorphism on encoded sheaves because its underlying additive map is the
ordinary sheafification unit of a sheaf. Cancel the fully faithful scalar
restriction to obtain full faithfulness. For essential surjectivity, restrict an
intrinsic module sheaf along the scalar map; this retains its additive sheaf.
The module-sheafification counit then gives the required isomorphism. Apply this
helper to both sites. The pro-etale equivalence preserves finite limits and
colimits, and finite-product preservation implies additivity.

Moved `finiteCoefficientModulePresheaf` earlier, with its signature and body
unchanged, so the private helpers can precede its two applications. No public
statement, definition body, instance registration, or import changed. The proof
follows the existing theorem docstrings, so the definition node's route and all
unit realizations are unchanged. There are no new public intermediate statements.

Searches: LeanFinder returned generic module-sheaf units and forgetful functors;
Loogle returned no result for `Presheaf.IsLocallySurjective` (unknown identifier
in that service); grep found locally constant functions and constant-sheaf
transport, not this realization equivalence. Local searches found the fully
proved `SiteModuleSheafConstantRingEquivalence` implementation, but its public
statement assumes commutative coefficients and does not identify the specified
functor. Adapted only its fully faithful encoding/unit/counit argument, allowing
general rings and the actual site and module universes. The Mathlib
`PresheafOfModules.sheafificationAdjunction` already supports noncommutative rings.
This is the same sheafification argument as Stacks, Modules on Sites, Tag 03CY
(`lemma-sheafification-presheaf-modules`) and Tag 093I (`section-constant`).

Validation: the module compiles cleanly through `lcompile.py`; explicit
`#print axioms` checks of all four completed theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. The proof includes empty schemes, the zero
ring, disconnected schemes, and arbitrary finite noncommutative coefficient
rings. No data are selected from an unproved existence theorem.

## Proved and sorry left

Closed 4 original holes, all attached to `def-weil-pbc-proetale-modules`:

- `AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap_locallyBijective`
- `AlgebraicGeometry.ProEtale.finiteCoefficientEtaleRealization_isEquivalence`
- `AlgebraicGeometry.ProEtale.finiteCoefficientRealization_exact`
- `AlgebraicGeometry.ProEtale.finiteCoefficientRealization_isEquivalence_ring`

Added 0 holes; split off 0 statements. Actual remaining hole count: 0.
The private helpers are fully proved. This is a proof, not a decomposition;
all four completed theorem terms are free of `sorryAx`, including transitively.

## No longer needed

None. No original proof-dependency imports were present, no imports were added,
and no module or node was withdrawn. The original public imports remain the
module's existing exported statement interface. In particular the commutative
`SiteModuleSheafConstantRingEquivalence` module is not imported by this proof.
There are no unit-route departures.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The node is a definition node with no theorem proof
steps; its four implementation obligations had complete natural-language
proofs in their existing docstrings. Those arguments are now implemented in
Lean. The general equivalence found by search is restricted to commutative
rings, so it cannot directly discharge this module's noncommutative statements.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
