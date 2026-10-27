## What changed

Proved `AlgebraicGeometry.ProEtale.QuotientChange.flatScalarCoefficientMap_linear`
from multiplication preservation of `coefficientMap`, with the tensor morphism
expanded into its two whiskerings.

Reduced `flat_coefficient_square_normalization` to the two independent source steps
`flat_scalar_unit_normalization` and `flat_scalar_geometric_coherence`. The combining
proof transports exactness along the given ordinary tensor presentations, uses the
existing exact pullback theorem, assembles the scalar/section comparisons, and
precomposes the existing `internal_scalar_mate_projection` equation with the inverse
of the given tensor comparison. Functoriality and the inverse/hom identity cancel
that comparison and give the exact requested tensor square. Every existing public
signature, definition body, and target statement is preserved. Local irreducibility
attributes keep Lean from expanding the geometric pullback and actual derived
comparison constructions while checking these equations.

The two new modules state, respectively, the scalar unit and its section comparison,
and the actual geometric comparison maps with their balanced and K-injective section
normalizations. The latter takes explicit map parameters with equations fixing them
to the actual constructions, so the combining proof need not unfold those constructions. These are steps 2 and 3--5 of the existing node, valid separately for
a single scheme and an arbitrary scheme map. Neither asserts the original full
conjunction or its final tensor square. The item node now records this reduction.

Validation: both new modules compiled in import order through `lcompile.py --all`.
The complete main proof compiled through `lcompile.py` in 32.7 seconds after the
comparison interfaces were made locally irreducible. The temporary profiler was
removed and the heartbeat explanation placed directly after its setting; the delivery
tool performs the final clean compilation and preflight.

## Proved and sorry left

Original holes closed: 2 of 2, by declaration name:

- `AlgebraicGeometry.ProEtale.QuotientChange.flatScalarCoefficientMap_linear` is proved
  directly, without any new holed dependency.
- `AlgebraicGeometry.ProEtale.QuotientChange.flat_coefficient_square_normalization`
  has a complete combining proof from the two named steps and existing declarations.
  This is a decomposition, not a complete proof of its mathematical content.

Holes added and remaining: 2, each an entire named public theorem body:

- `AlgebraicGeometry.ProEtale.QuotientChange.flat_scalar_unit_normalization`, node
  `lem-sfb-flat-scalar-unit-normalization`.
- `AlgebraicGeometry.ProEtale.QuotientChange.flat_scalar_geometric_coherence`, node
  `lem-sfb-flat-scalar-geometric-coherence`.

There is no sorry in the item module, any definition, or any private helper.
The raw delivery balance is two holes closed and two added; it is a decomposition.
No imported declaration is claimed proved by this packet. In particular, the
existing holed normalization and mate-projection dependencies retain their own
proof obligations; this packet does not count their holes as closed.

## No longer needed

Removed these unused private imports from the item module:

- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`

Their relevant mathematical inputs remain dependencies of the separate source steps;
no module or node is claimed globally pruned. The direct proof now needs the two new
step modules, `CondensedModulePullbackExact`, and the existing internal scalar
mate-projection theorem. Existing public
imports are retained to preserve the module's published interface. No blueprint unit
statement or step is bypassed.

The parent no longer directly uses the following proof-dependency nodes: the flat
sheaf-module definition (`def-pc-flat-sheaf-modules`), coefficient morphisms
(`sk-def-sfb-coefficient-morphisms`), derived scalar extension
(`sk-def-sfb-derived-extension-of-scalars`), right-derived-functor construction
(`def-sfb-right-derived-functor`), coefficient change (`sk-def-sfb-coefficient-change`),
derived pull comparison (`def-sfb-derived-pull-iso`), and ringed projection mate
(`lem-weil-pbc-ringed-projection-mate-exact`). Their data remain in the statement
interfaces or existing imported normalization/mate APIs. Flatness is proved directly
as exactness of tensorRight, and the final projection equation comes directly from
`internal_scalar_mate_projection`, so no separate use of these nodes is needed.
All other former proof dependencies remain in one or both new source-step nodes.
This reorganizes their obligations; it does not withdraw any source declaration.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The existing scalar normalization theorem supplies normalized
tensor/section data but does not state either the scalar adjunction-unit equation or
normalization of the actual `derivedPullIso`/`derivedComapLowerStarIso` maps. The two
separate steps make these missing bridges explicit; they do not follow merely by
projecting fields from that theorem. The latest blueprint rational proof paragraph (1)
is retained as the source route, with the original node's detailed expansion.

## New nodes

`lem-sfb-flat-scalar-unit-normalization` records the ordinary/derived scalar-unit
calculation and compatibility with the fixed section adjunction. Its single-scheme
statement takes the actual coefficient module map explicitly and pins its underlying
map to `coefficientMap`.

`lem-sfb-flat-scalar-geometric-coherence` records the equality of the actual derived
maps with their balanced/mate comparisons, and transports them to any normalized
section scalar models. The section direct-image comparison is pinned by its ordinary
identity on sections and its explicit K-injective computation-unit equation. The two
map parameters are pinned to the actual constructions by equality hypotheses; they
are not arbitrary substitute comparisons.

Change record: `coord/changes/flat-coefficient-square-local-proof-attributes.md`.
Preflight requested it for the local attribute commands. No existing statement or
definition was changed, and no other group's module was adapted.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
