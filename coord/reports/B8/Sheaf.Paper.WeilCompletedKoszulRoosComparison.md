## What changed

`AlgebraicGeometry.Scheme.completedKoszulFiniteComparison` is reduced, with its
statement unchanged, to two separate ingredients. The coefficient-only theorem
`completedKoszulCoefficientComparison` identifies the finite exterior complex with
the ordered tensor-dual complex, including power transitions and the degree-zero
unit; it has no arbitrary input complex. `completedCechTensorTransport` is the
general natural isomorphism commuting coefficient/site transport with total tensor,
including its unit formula specialized to the named Koszul unit; it contains no
exterior-to-dual identification or tower-transition requirement.
The original theorem composes these isomorphisms with the explicit componentwise
identity between the tower and its transposed-back complex. Naturality proves the tower
transition equation, and the total-tensor summand formula and explicit right unitor
prove its augmentation equation. This is a decomposition, not a claim that either
remaining ingredient has been proved.

The previously proved small-site, module, derived and scalar constructions move
verbatim into `Sheaf.Paper.WeilCompletedKoszulSite`, publicly re-exported by the
original module. This is necessary to avoid an import cycle between the finite
comparison and its two dependencies. A new actual morphism
`completedCechCoefficientUnit` is defined from the transported regular-module
section 1, with its naturality proved by preservation of 1 by restriction maps.
No existing declaration signature or mathematical object changes. The definition
has no unproved data or proof field.

Change record: `coord/changes/B8-completed-koszul-site-extraction.md`.

## Proved and sorry left

Closed the local hole in
`AlgebraicGeometry.Scheme.completedKoszulFiniteComparison`
(`lem-weil-pbc-completed-fiber-roos-comparison`) by composition of two named
statements and real Lean proofs of both required compatibility equations.
The item has zero textual holes after this change.

Added two public whole-proof holes:

- `AlgebraicGeometry.Scheme.completedKoszulCoefficientComparison`, node
  `lem-weil-pbc-completed-koszul-coefficient-comparison`, module
  `Sheaf.Paper.WeilCompletedKoszulCoefficientComparison`.
- `AlgebraicGeometry.Scheme.completedCechTensorTransport`, node
  `lem-weil-pbc-completed-cech-tensor-transport`, module
  `Sheaf.Paper.WeilCompletedTensorTransport`.

Thus one upper hole is closed and two strictly separate lower holes are added:
this packet is a decomposition, with net hole change +1, not a net proof closure.
The extracted site module has no sorry. All four packet modules compile through
`lcompile.py --all`; the item compiles without warnings. Each new hole has a source and complete
proof in words in its docstring and node. Neither merely renames the full
obligation: one removes arbitrary-complex totalization, the other removes the
entire exterior/tensor-dual Koszul calculation.

Edge cases checked in the mathematical statements: r=0 is the unit comparison;
zero/invertible generators require no division or regularity; the zero ring is
allowed; sheafification and the section-1 construction handle an empty site.
The tensor-transport statement permits arbitrary unbounded C and K because the
transport is an additive equivalence preserving the totalization coproducts.

## No longer needed

The item drops redundant private imports of `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.Paper.IntegralUniformCoefficient` and
`Sheaf.Paper.IntrinsicCompletionCompleted`; the site module supplies their needed
construction dependencies. No module is withdrawn or claimed globally pruned. No fixed blueprint unit route
is bypassed. The existing public imports are retained in the item and the moved
site declarations remain publicly available through it. The original proof plan
is factored at its actual coefficient-comparison and total-tensor steps.

The item proof now uses the coefficient-comparison and tensor-transport nodes
and `def-weil-pbc-ringed-koszul-system`. Its proved generic unit helper also uses
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients` privately. The former direct proof dependencies
`def-weil-pbc-bounded-constructible-complete`,
`def-weil-pbc-intrinsic-completion`, and `def-weil-sheaf-of-modules-category`
are used below the new nodes; they are not globally pruned. Site/scalar transport
belongs to the extracted definition node rather than the finite theorem node.
Products, limits, cones and derived localization are still proved by consumers;
none enters either new hole.

## Where the brief, the DAG or earlier work was wrong

The recorded proof dependencies provide definitions of the two Koszul models,
not a theorem identifying them or a tensor comparison for this composite
coefficient/site transport. Existing `mapBifunctorComparison` supplies generic
totalization machinery once the module tensor comparison is constructed;
`sliceTensorIso` treats equal-universe site restriction and does not directly
include inverse coefficient restriction and the prescribed round trip here.
There is no existing declaration to apply to obtain either missing ingredient.

Searches used LeanFinder, Loogle, LeanSearch and source grep. They found the
exterior degree-zero/one natural isomorphisms, general exterior bases, tensor
duality and total-tensor machinery, but no comparison of these actual complexes.
The current proper-base-change unit realized statements and steps are unchanged.

## New nodes

`def-weil-pbc-completed-cech-site-transport` records the existing constructions
moved to the lower module and the actual section-1 regular-module unit. It is
acyclic and contains no new hole.

`lem-weil-pbc-completed-koszul-coefficient-comparison` isolates the finite free
exterior/tensor-dual coordinate argument from Tag 0664 and Tag 0A0E, with the
power-transition and degree-zero augmentation equations, before tensoring with
an arbitrary complex.

`lem-weil-pbc-completed-cech-tensor-transport` isolates preservation of balanced
sheaf tensors and total coproducts by inverse coefficient restriction and site
equivalence. Its unit formula uses the actual identity-on-sections round trip.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
