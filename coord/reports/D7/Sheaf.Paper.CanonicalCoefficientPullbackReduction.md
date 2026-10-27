## What changed

Prove `WeilConjectures.canonicalCoefficientPullbackReduction` without changing its
statement or any coefficient construction. The unchanged constructions and the
existing model-map proof move to `Sheaf.Paper.CanonicalCoefficientPullbackModels`,
publicly reexported by the item. Proved comparison results and private helpers live in
`Sheaf.Paper.CanonicalCoefficientUnitNormalization`,
`Sheaf.Paper.CanonicalCoefficientChainNormalization`, and
`Sheaf.Paper.CanonicalCoefficientFiniteCompatibility`. These files separate the
single-complex models, chain normalization, and finite compatibility checks; no
public declaration is removed or renamed. The monolithic version still took
100.4 seconds after replacing a 46-second colimit-instance search with direct
cancellation and making the new constructions locally irreducible. The file split
follows the brief's updated step 3a, after those optimizations. Private helpers compare the sectionwise
regular-module inverse image with the regular complex, identify its zero-homotopy
Roos augmentation with `constantWeilChainUnit`, and identify finite multiplication
with the existing regular pullback isomorphism. The inverse identities follow by
cancelling these specified isomorphisms. The normalized unit's actual cone
projections give both projection identities. Quotient generators and epimorphic
regular quotient maps give strict transition compatibility; the unit's strict
compatibility gives the derived rho identity.

## Proved and sorry left

Closed one existing hole: `WeilConjectures.canonicalCoefficientPullbackReduction`
(node `lem-pod-canonical-coefficient-pullback-reduction`).
Added zero holes. No `sorry` remains in the item. The previously proved
`WeilConjectures.canonicalCoefficientModelMaps_isIso` is retained.

Validation: `lcompile.py --all` accepted all five delivery modules and the unchanged
direct importers `Sheaf.Paper.FiniteRegularCoefficientComparisons` and
`Sheaf.Paper.FrobeniusFixesUnitSection`. The compile service enforces the 60-second
Lean-run limit; its displayed total times also include artifact setup and cache
waits. The supporting nodes expose their proved entry theorems; auxiliary lemmas remain
private. The narrow private-module warning options used in an earlier preflight
were removed. No proof-checking or style linter is disabled in the final packet.
Both temporary importer copies were removed after verification. Every delivery
module has zero `sorry` tokens, no profiling options, and lines at most 100 characters.
The final theorem statement and relocated construction block were compared verbatim
with the original source.

## No longer needed

No import or module is withdrawn. The public model import reexports the unchanged
coefficient constructions, and the original public imports preserve the existing
public interface. The new proof imports are private. The following planned proof dependencies are unnecessary
for this regular-coefficient argument and are removed from this node's proof route:

- `lem-pc-kflat-resolution`: the fixed regular good representative is already available.
- `def-pur-sheaf-tensor-product`: use the existing proved regular coefficient isomorphisms.
- `lem-weil-proetale-countable-products-exact` and `lem-weil-derived-limit-existence`:
  `constantWeilChainUnit_isIso` already proves the needed normalized Roos comparison.
- `lem-pur-integral-operations-well-defined` and `lem-weil-strict-roos-comparison`:
  the strict model and its good-representative comparison are existing constructions;
  the proof checks their actual maps rather than building another general comparison.
- `lem-weil-constant-coefficient-objects-constructible` and
  `lem-weil-finite-free-completed-scalar-comparison`: invertibility of the specific
  normalized regular Roos unit has already been proved in ConstantWeilStructure.
- `def-pc-kflat-complex`, `lem-weil-integral-reduction-tower-well-defined`, and
  `lem-pur-derived-change-of-rings`: no replacement of the fixed regular resolution
  or comparison between different resolutions is needed.

The nine corresponding obsolete `tool_uses` approvals are also removed; the
pro-etale isomorphism inverse-image approval is retained.

These are local proof-route removals, not claims that another consumer no longer
needs these nodes or their modules. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The remaining DAG plan reconstructed general tensor/cone comparisons that are
already proved for the regular coefficient object in ConstantWeilStructure.
Its normalized unit and finite regular-module APIs suffice for a shorter argument.
The historical blueprint citation points to a snapshot path; in the current latest
blueprint the cohomological-finiteness proof is under sec-six-functors/sk-lem-finite.
There is no statement dispute and no target or definition change. Preflight required
one new node with an exact `lean.file` for every supporting module; a parent
`lean.modules` list alone was insufficient. The relocated definitions now belong
to the model node, which is added to the parent's statement dependencies without
changing its mathematical statement.

Change record: `coord/changes/canonical-coefficient-proof-modules.md`. A byte-for-byte
comparison confirms that the relocated declaration block is unchanged. The source-only
consumer check finds 306 transitive importers and two direct importers; their unchanged
sources compiled successfully against the delivery and were removed from the sandbox afterward.

## New nodes

`lem-pod-canonical-coefficient-model-maps` attaches the unchanged coefficient
constructions and the already proved `canonicalCoefficientModelMaps_isIso` to
`CanonicalCoefficientPullbackModels`. Its proof is the existing sectionwise unit,
normalized scalar-reduction, and regular tensor-unit triangle argument.

`lem-pod-canonical-coefficient-unit-roos-normalization` attaches
`coefficientIntegralInverseIso` and the proved `coefficientUnit_roos` to
`CanonicalCoefficientUnitNormalization`. The inverse coefficient identification
conjugates the actual zero-homotopy Roos augmentation to the normalized chain unit;
the proof checks the product projections and the zero shifted coordinate.

`lem-pod-canonical-coefficient-chain-normalization` attaches the proved
`coefficientKappa_factor` to `CanonicalCoefficientChainNormalization`. It identifies
the specified kappa with the derived coefficient comparison followed by the inverse
normalized Roos comparison, using the preceding chain augmentation equation and
the exact-functor single/derived comparison.

`lem-pod-canonical-coefficient-finite-compatibility` attaches the proved
`coefficientStrictTransition` to `CanonicalCoefficientFiniteCompatibility`. It
proves the strict finite transition equation by regular quotient generators and
epimorphic cancellation. All four nodes are fully proved; none adds a hole.

Change record: `coord/changes/canonical-coefficient-proof-modules.md`.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
