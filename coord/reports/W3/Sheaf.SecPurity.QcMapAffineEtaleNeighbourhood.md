## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_neighbourhood` in
`Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood`, preserving its signature and public imports.
The proof takes an arbitrary atlas from the definition of an algebraic space, pulls it back
to C, and extracts a finite cover from the images of inverse images of its affine opens.
Their finite coproduct constructs U. The existing separated-chart theorem supplies V;
uniqueness of represented pullbacks identifies it with U ×_W P, proving surjectivity by
Mathlib scheme point lifting. The proved unramified scheme theorem supplies local
quasi-finiteness. The finite subcover and empty coproduct also cover empty C.

Added two proved private helpers: `property_of_represented_pullback` transfers an
isomorphism-invariant scheme-test property between representing squares using Mathlib's
relative morphism-property API; `yoneda_isEtale` constructs the scheme tests of an étale
scheme map by ordinary pullbacks. Added proof imports for scheme coproducts,
UniversallyOpen, PullbackCarrier, relative representability, and UnramifiedQuasiFinite.
Updated the existing node's proof, proof_deps, and proof_origin to this route.

Validation: the item compiled through lcompile.py with exit code 0 in 7.1 seconds,
without warnings. No public interface changes or consumer adaptations are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_neighbourhood`
(node `lem-a1-qc-map-affine-etale-neighbourhood`).

Holes added: 0. Holes remaining in the delivered module: 0. Split off: 0.
Both new private helpers are fully proved. The proof uses the already stated
`AlgebraicSpace.isEtale_comp` and `AlgebraicSpace.separated_etale_chart`, whose existing
proof holes remain in their own modules; no axiom-freedom of the transitive argument is
claimed here. The imported `Scheme.Hom.isLocallyQuasiFinite_of_unramified` is proved.

## No longer needed

Removed these three proof imports and their corresponding proof-dependency edges:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`, node
  `lem-a1-space-affine-etale-cover`: use the atlas in the definition, and select charts
  using the topology of C and the scheme pullback P instead of the point topology of E.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, node
  `lem-a1-space-fibre-product-point`: lift ordinary scheme points in U ×_W P and transfer
  them through the unique represented-pullback isomorphism.
- `Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite`, node
  `lem-a1-etale-space-locally-quasi-finite`: apply the proved scheme unramified theorem
  directly, avoiding the chartwise reformulation.

All other original proof dependencies remain used. The added Mathlib-leaf edges record
scheme affine opens, étale openness, Yoneda, and scheme base-change images; the new source
edge records the proved unramified theorem. These three modules are unnecessary for this
proof; no global unreachability or withdrawal is asserted. No top-level tool_uses entries
were removed. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned algebraic-space point-topology
argument is more elaborate than necessary: base changing the initial atlas first lets
all compactness and point-lifting work take place on schemes. The chartwise algebraic-space
local quasi-finiteness lemma is likewise unnecessary for a projection already known étale.
No statements, definitions, target declarations, or source-library files were changed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
