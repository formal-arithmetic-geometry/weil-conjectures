## What changed

Proved `AlgebraicGeometry.ProEtale.locallyClosedCoefficientExtension_composition`
in `Sheaf.Paper.LocallyClosedCoefficientExtensionComposition` with its exact original
signature. Added the proof-only import
`import all Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection` to reuse its
already proved generic internal-module support and reconstruction helpers.
All public imports, declarations, definitions and statements remain unchanged.

The three actual closure extensions are the open-then-closed cases of the existing
`generatorExtension` construction. For `N = a_! b_! M`, disjoint restriction along
`g : Y → X` is supported on `Y ×_X S`. Its restriction to that immersion is zero:
the other projection misses `b(T)`, and restriction of `a_!` recovers `b_! M`.
Supported-zero detection proves support on `b ≫ a`. Reconstruction and the two
source-restriction isomorphisms give exactly the requested isomorphism.
No extension functor is chosen from an existence theorem.

Updated the existing DAG node's proof, proof dependencies and proof origin to this
shorter route. The integral-model unit's statement and all its proof steps remain
realized as before. The helpers used here work on arbitrary internal modules;
none requires lisseness or a tensor-product hypothesis.

Validation: the remote single-file compiler is used for the item; the delivery
preflight also checks compilation and axioms. An import-graph check permits the
new proof import. Its entire import closure is already in `TargetsCheck`'s
closure (zero modules newly reached from the targets). Empty schemes and zero
modules use the same support and restriction proofs without case exclusions.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.locallyClosedCoefficientExtension_composition`
(node `lem-sfb-internal-locally-closed-extension-composition`).
Zero holes remain in the delivered module; zero holes are added and zero are
split off. The proof uses the existing proved helpers `generatorExtension_support`,
`generatorRestriction_isIso`, `supported_pullback`, `supported_zero`,
`generatorExtension_reconstruct` and `immersion_noetherian`; it does not assume a
new composition statement.

## No longer needed

No original imports were removed, and no module is withdrawn.
The former planned proof dependencies
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`sk-prop-sfb-cartesian-coefficients`,
`lem-sfb-locally-closed-module-extension-coherence`, and
`lem-sfb-coefficient-heart-locally-closed-extension` are not used directly and are
removed from this node's proof dependency list. In particular the proof does not
need the unproved normalized sectionwise-module extension system or a new
internal/sectionwise transport comparison. The locally closed extension theorem's
statement-dependency entry remains: its actual extension construction is unchanged.
Some of these modules remain transitively imported for other declarations; no
claim is made that they become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original docstring and DAG describe a valid but longer sectionwise-transport
route. Existing internal-module support helpers already suffice. The node now
records the shorter argument; the original public docstring is preserved.
No mathematical statement repair or consumer adaptation was needed.

LeanFinder, Loogle and Mathlib grep searches found pullback-composition and
adjoint-uniqueness APIs, but no direct theorem for this internal condensed-ring
composition. Repository search found the stronger generic support helpers above.

No new nodes or change records are required.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
