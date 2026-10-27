## Worker report

The delivery states `CategoryTheory.stack_coarse_properties_etale_locality` in
`Sheaf.AlgebraicGeometry.StackCoarsePropertiesEtaleLocality`. Its only proof is `sorry`.
The second module defines the missing universal-homeomorphism predicate with real data
(a universally quantified proposition); it contains no postponed theorem or choice.
The item statement, source, proof and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Explicit universes `u v w z` implement
  def-weil-size-convention: endpoint categories use the common bound
  `BasedCategory.{max u v, max (u + 1) w} (Over S)`. This bound contains the scheme
  site and can be enlarged; it includes discrete schemes and all 2-fibre products used.
- The two DM stacks are `A B`, with exactly `hA : IsDeligneMumfordModuliStack A`
  and `hB : IsDeligneMumfordModuliStack B`. The arbitrary morphism is
  `f : BasedFunctor A B`. There is no representability, separation, finiteness,
  nonemptiness, inertia, or Noetherian assumption on f.
- The set-indexed scheme family is `(I : Type z) (W : I → Over S)` with maps
  `q i : BasedFunctor (discreteModuli (yoneda.obj (W i))) B`. Its index universe
  is independent; neither finiteness nor existence of a same-universe coproduct is assumed.
- Representability by spaces and étaleness are `hqrep` and `hqet`, using the recorded
  predicates `IsRepresentableByAlgebraicSpaces` and `IsEtaleModuliMap`. The latter
  uses `HasSpaceBaseChange` and `SpaceMapIsEtale`, hence actual scheme-chart Etale tests.
- Joint surjectivity is `hqsurj`: every point of B is the image of a point from some
  discrete W i. The point quotient is by arrows between field-valued objects, which
  generates common-field-extension/isomorphism equivalence; no geometric representative
  or lifting map is supplied as extra data.
- Separatedness is `ModuliSchemeTest @IsProper (moduliRelativeDiagonal f)`.
  Scheme tests carry the actual projection and an equivalence over the test scheme.
  For DM endpoints this is equivalent to a proper algebraic-space relative diagonal:
  the diagonal is unramified; a proper unramified space over a scheme is finite and
  therefore a scheme. This is the convention already used by
  def-sfb-dm-stack-morphism-properties, not source-chart properness (which is invalid).
- Quasi-compactness is the existing `IsQuasiCompactModuliMap f`. It asks that every
  affine scheme base change have a compact étale scheme atlas. For a DM stack, this
  is equivalent to compactness of its point space: the forward direction is the
  continuous surjective atlas map; conversely refine any étale atlas by affine opens,
  use openness of their images and compactness to retain finitely many, and take their
  finite disjoint union. Affine tests imply the node's tests on quasi-compact opens by
  a finite affine cover of each such open and the same finite compact-image argument;
  conversely take a test affine and its whole open. Thus no new quasi-compactness notion
  is introduced, and no finite-type or quasi-separatedness condition is imposed.
- Universal homeomorphism is `IsUniversalHomeomorphismModuliMap f`: every
  `IsAlgebraicModuliStack Z` and every `g : BasedFunctor Z G` are tested by
  `IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f))`. Z is not restricted to DM.
  The topology is the existing final topology of smooth surjective scheme atlases.
- The first three conjuncts are three separate iff statements, one for each property.
  Each local map is the actual projection `moduliTwoFiberFst (q i) f`. In the supplied
  construction the order is `W_i ×_B A`, canonically equivalent over W_i to the
  node's `A ×_B W_i`; the comparison is the specified isomorphism in the triple.
  These are not a single iff about the conjunction of all properties.
- The final conjunct quantifies over every DM stack B' and every `g : BasedFunctor B' B`.
  Its three separate implications preserve each property under this arbitrary base
  change. It does not require g to be étale, representable, surjective or finite type.

Dependency declarations read and used (public imports for statement interfaces):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsDeligneMumfordModuliStack`, `IsModuliStack`, `IsFibredInGroupoids`,
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`, `discreteModuli`,
  `SpaceMapIsEtale`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  its recorded representability/étaleness predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSchemeTest`,
  `moduliRelativeDiagonal`, `IsQuasiCompactModuliMap`, `ModuliPoints`, `moduliPointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack` and
  `IsSmoothModuliAtlas` for the arbitrary test stacks.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace`, the actual smooth-atlas topology on `ModuliPoints`,
  and `moduliSchemePointMap`. These definitions are owned by the landed definition node
  `def-sfb-stack-point-topological-space` (Q139, existing:true), not by the theorem node.
- The further statement dependencies above have been added to stmt_deps, so these
  shared interfaces are explicitly attached to their existing DAG nodes.

Proof imports retained for the DAG's stated proof plan:
`DMIsomSpaceUnramified.dm_isom_space_unramified`,
`AlgebraicSpaceFibreProductsEtaleCovers` (all three recorded statements),
`AlgebraicSpaceFlatProperFpLocality.flat_proper_fp_locality`,
`AlgebraicSpaceAffineEtaleCover.exists_affine_etale_cover_and_point_topology`,
`StackChartwiseSmoothEtaleCalculus.stack_chartwise_smooth_etale_calculus`,
`StackPointTopologyFlatLfpOpen.stackPointTopology_flat_lfp_open`,
`AlgebraicStackFibreProducts.algebraicStack_twoFiberProduct`,
`Scheme.fppfTopology`, `Scheme.isBasis_affineOpens`, and
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` / `PrimeSpectrum.compactSpace`.
The proof dependency lem-sfb-dm-etale-atlas-calculus has no recorded Lean declaration
or Mathlib match in the read clone, so there is no module of it to import. It is not
needed for elaboration of the statement, and its DAG proof dependency is retained.
The theorem docstring carries all eight original proof steps, including the common-field
point lifting, diagonal calculation, fppf descent, finite affine refinement and the
arbitrary algebraic-stack universal-homeomorphism test.

Edge cases checked before writing:

- Empty I is allowed; joint surjectivity then forces B to have no points. No
  nonempty-type or selected-index binder rules it out. The local universal quantifiers
  are vacuous, and the empty-target stack morphism has all three properties.
- Empty schemes, empty stack point spaces and empty opens are retained. IsHomeomorph
  of the empty projection is meaningful; proper/compact diagonal tests include empties.
- Identity maps and identity covering families recover each property individually.
- Arbitrary nonrepresentable DM morphisms, including gerbe-like maps, are retained;
  only their relative diagonals are tested by schemes.
- No quasi-compactness of W_i, finite cover, finite type, separation of B, or
  intersection condition on affine opens was added.
- Non-DM algebraic stacks remain valid tests for universal homeomorphism, including
  tests with positive-dimensional stabilizers. The definition's endpoint universe
  parameters are independent, so discrete scheme endpoints and enlarged stack sources
  coexist. The max bound prevents a smaller, potentially empty universe of tests.

Searches:

- `msearch.py ... leanfinder "Separated quasi compact universal homeomorphism morphisms
  of Deligne Mumford stacks etale local on target and stable under base change"`:
  eight scheme-level hits (Etale, scheme étale topology, separated Zariski locality);
  no algebraic-stack statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsSeparated, AlgebraicGeometry.QuasiCompact,
  Topology.IsHomeomorph"`: zero hits, unknown `Topology.IsHomeomorph`. The final code
  uses the existing unqualified `IsHomeomorph`; this exploratory query did not establish
  absence on its own.
- LeanSearch and LeanFinder queries for the missing universal-homeomorphism definition
  returned scheme universal injectivity/open maps, field-point classification and
  scheme homeomorphisms; none define algebraic-stack universal homeomorphisms.
  Their verbatim outputs are stored in the new node's mathlib_searches.
- `msearch.py ... grep 'IsUniversalHomeomorphism|UniversalHomeomorphismModuli'`:
  zero Mathlib hits. Direct rg of WeilConjectures finds scheme universal-homeomorphism
  material; direct rg of Sheaf finds no predicate for arbitrary algebraic-stack tests.
  Existing particular theorem statements sometimes expand the same universal quantifier;
  those are not a shared definition or the present locality statement.
- `rg -n 'lem-sfb-stack-coarse-properties-etale-locality' lean/WeilConjectures`:
  no match. Project interface searches found the existing DM quasi-compactness and
  proper-diagonal tests, which are reused rather than copied.
- Definition-node search for both stack and universal homeomorphism found no node
  defining the needed notion. `tools/blueprint_refs.py search 'universal homeomorphism'`
  returned 21 scheme/topos/convention results, with no algebraic-stack definition.
- Read local Stacks sources at Tags 04YW, 050F, 06TZ, 050U, 050V, 0DTL, 0CI7, 0CI8,
  0DTQ, and the common-field-extension and atlas-topology arguments in stacks-properties.

Validation: both delivered modules compile separately through scompile.py, including
both their sandbox and final library module names. The initial same-endpoint-universe
version failed when the target was a smaller discrete scheme; the definition now has
independent endpoint universes and a common test bound, and both files compile cleanly.
No statement correction or disputed statement is required.

## New nodes

`def-sfb-universal-homeomorphism-moduli-map` supplies exactly Stacks Tag 0CI7:
for every algebraic-stack base change, the actual projection is a homeomorphism on
existing point spaces. Its module is
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismModuliMap`, declaration
`CategoryTheory.IsUniversalHomeomorphismModuliMap`. Its dependencies are the existing
scheme/size conventions, algebraic-stack and 2-fibre-product definitions, and point
topology. The searches above, recorded verbatim in its node, found no shared predicate.
It uses real quantified data, with no axiom, arbitrary map, chosen topology, or
postponed construction. It is cited directly by the item's stmt_deps.

## Second reading by Q13

The dispatch explicitly prohibits starting other agents, so no independent second worker
has read this delivery; the maintainer's independent review remains necessary. The following
is a separate self-check against the node and both final modules, not a claim of independent
review: all three properties have individual iff clauses and individual preservation clauses;
there is no accidental representability assumption on f or g; scheme charts retain their
actual projections; arbitrary non-DM algebraic-stack tests appear in the new definition;
I has an independent universe and need not be nonempty; and the existing DM quasi-compactness
predicate matches the node by the finite affine/compact-image argument above. The universe
mismatch detected by the first compile was repaired by independent endpoint universes,
without imposing equality of their sizes. No correction to the mathematical node was made.


## Repair of returned head 1c350b01277a

H2 repaired exactly: replaced `lem-sfb-stack-point-topology-flat-lfp-open` by the landed
`def-sfb-stack-point-topological-space` in the item's stmt_deps and the new node's
stmt_deps. The new node's statement now cites that definition node for the point topology.
The theorem remains in the item's proof_deps, with all proof-step citations retained.
The new definition node still has empty proof_deps: its quantified predicate needs only
the topology construction, not a theorem proving topology properties.

Read the current definition node's full statement and existing:true Lean record, and the
full signatures/docstrings of `moduliSchemePointMap` and `moduliPointTopologicalSpace`
in `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`. This confirms the dependency
ownership in the return (Q139 landing 7b4e32de3, 2026-10-24). The module import already
provides exactly those definitions, so both delivered Lean files and their signatures
remain byte-identical to the returned delivery.

Compared the retained item with current main: only lean and stmt_deps differed; statement,
source, proof and proof_deps were identical. Applied this dependency repair to the retained
packet. The prescribed deliver2.py wrapper rebases the packet onto freshly fetched
origin/sheaf-dag and preserves all current main fields not owned by the delivery. No shared
repository file or other node is edited. This fixes the returned packet rather than
re-pushing its unchanged content.

Repair validation: both retained Lean modules compile cleanly through scompile.py against
its current published-server environment (sandbox and library module names). JSON assertions
confirm both stmt_deps cite the definition, neither cites the theorem, the new statement
cites the definition, and the item's proof_deps retain the theorem.
