## What changed

Replaced the hole in `field_projection_system_square` by the actual proper/open
factorization and categorical pasting argument, followed by inverse cancellation.
The theorem signature is unchanged. Relocated the existing tensor comparison data
and four projection declarations verbatim to `FieldProjectionSystemData`, publicly
re-exported from the original module, so the new component statements can mention
them without an import cycle. The data module adds explicit `leftProper` and
`leftOpen` factors. Change record: `coord/changes/S2-field-projection-system-data.md`.

The proper projection naturality helper is proved by transposing under its
adjunction and using tensorator and counit naturality. The factorization cancels
the adjacent tensor symmetry and its inverse. The proof then pastes the proper
and open squares using naturality of the actual proper mate, projection naturality,
and functoriality. The inverted equality follows by precomposition with the image
of the source projection and cancellation of both inverses.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_projection_system_square`.
Closed that upper hole by decomposition; this is not claimed as a complete proof
of the component calculations. Three holes are added, each exactly `:= by sorry`:

- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_projection_tensor_construction`
  (`lem-sp-field-projection-tensor-construction`): only the canonical tensor data.
- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_projection_proper_square`
  (`lem-sp-field-projection-proper-square`): only the proper counit square.
- `AlgebraicGeometry.ProEtale.FieldShriekSystem.field_projection_open_square`
  (`lem-sp-field-projection-open-square`): only the open tensor square.

No hole is left in the assigned module or in a definition. No axiom is added.
The three statements separate independent pieces of the original proof and are
combined by real Lean naturality and functoriality calculations.

Validation: `lcompile.py --all` compiled all five sandbox modules successfully
with exit code zero and no reported warnings. The assigned module contains zero
`sorry` tokens, the shared data module zero, and each component module one.

## No longer needed

The original proof-only imports of `RingedExchangeTensorCoherence`,
`OpenTensorNormalization`, `SmoothPurityTowerGluing` and `ScalarExtensionFunctor`
are removed from the assigned module. The first two support the respective new
component statements; they are not globally withdrawn. The latter two are not
needed by this formal conclusion: invertibility of both projections is supplied
explicitly by `hA` and `hB`. The actual scalar-preservation and projection-isomorphism
results remain needed elsewhere, and no module is withdrawn.

The original direct proof dependencies `det-sp-scalar-extension-functor`,
`det-sp-tower-shriek-levels`, `def-exchange-projection`,
`lem-coef-semilinear-derived-sections`, `lem-sf-open-tensor-normalization`,
`lem-sp-field-shriek-system-comparison` and
`lem-weil-pbc-ringed-exchange-tensor-coherence` are replaced in the item's
proof_deps by the three component nodes and shared-data node. The comparison
construction and other definitions remain available through statement imports;
the generic coherence results occur in the component nodes' dependencies.
Both existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original natural-language plan proves invertibility using normalized domains,
but the Lean theorem asks only for the inverted equality conditional on explicit
invertibility witnesses. No stronger assertion is silently claimed. The generic
ringed-topos and open-normalization declarations exist and were read; their
coordinate-identification work does not yet appear as a theorem for this fixed
field-system interface, so it is isolated as the proper and open component lemmas.

Edge cases checked on the formulas: E=F is the identity coefficient comparison;
zero inputs give zero maps; p=id removes the proper mate; j=id removes the open
factor; an empty source has the same zero-system calculation. Ramified coefficient
extensions cause no new assumption: all tensor comparisons are derived and the
system scalar normalization permits nonflat transitions. The component squares
are stated on whole derived systems, never inferred from finite evaluations.

## New nodes

`def-sp-field-projection-factor-data` attaches the relocated five declarations
and the explicit proper/open factors. `lem-sp-field-projection-tensor-construction`
is the signed K-flat symmetry and scalar tensor construction only.
`lem-sp-field-projection-proper-square` is the specialization of ringed
exchange/tensor coherence before any open extension.
`lem-sp-field-projection-open-square` is open restriction and tensor normalization
with the compactification compositor, before any proper direct image. Each has
its source, proof in words and recorded searches. The generic ringed coherence,
open normalization and semilinear derived calculus serve as tools in their
component proofs for exactly the roles already approved on the parent node;
there is no alternate field-extension unit route. The existing item node now
records the actual factorization, naturality pasting and inverse-cancellation route.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
