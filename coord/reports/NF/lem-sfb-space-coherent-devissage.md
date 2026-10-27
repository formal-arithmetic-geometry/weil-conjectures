## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentDevissage` states
`AlgebraicGeometry.AlgebraicSpace.coherent_property_higher_rank_devissage`.
Its only theorem proof is `sorry`; there are no new definitions, instances or axioms.
Source read: Stacks Project, spaces-cohomology.tex, Tag 07UT,
`lemma-property-higher-rank-cohomological`, including the full proof. The node already
contains the necessary P(0) repair; no source-based statement correction is needed.

Clause-by-clause correspondence:

- Scheme S and algebraic space X over S: `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  `X.Modules` is the dependency's module-sheaf category on the small etale ringed site,
  in the existing section universe u, without identifying object and morphism universes.
- Noetherian X: `hln` says every etale chart scheme is locally Noetherian; `hqc` is
  `CompactSpace (Point X.obj.obj)`; `hqs` tests compactness of fibre products of pairs
  of affine scheme maps. This is the same diagonal test as the recorded coherent
  ideal filtration and closed-coherent-modules dependencies, with arbitrary base S.
- Coherent modules: `SheafOfModules.IsFinitePresentation`. On locally Noetherian
  algebraic spaces this is exactly quasi-coherence plus coherent pullbacks on every
  etale chart (07UB). This is the existing convention explicitly used in the recorded
  coherent-abelian, ideal-filtration and closed-coherent-modules declarations, not a
  replacement predicate. Every Z quantified in `hP_closed` is locally Noetherian by
  closed immersion into X; no additional hypothesis on Z is assumed.
- Isomorphism-invariant property of all module sheaves: `P : X.Modules → Prop` and
  `hP_iso`, for all module objects and actual isomorphisms. Applying to the inverse
  gives the reverse implication, so the directional form expresses invariance.
- (0) `hP_zero : ∀ F, IsZero F → P F` is P(0) independent of the choice of zero object.
  With `hP_iso`, it is equivalent to P of a chosen zero module.
- (1) `hP_extension` quantifies over `ShortComplex X.Modules`, its `ShortExact` proof,
  finite presentation of all three modules, and P of the two ends, concluding P of
  the middle. ShortExact supplies monicity, exactness and epimorphicity in module sheaves.
- (2) `hP_sum` uses natural `r` with `1 ≤ r`, which covers exactly the positive integers.
  The finite categorical product indexed by `Fin r` is the finite direct sum in this
  additive module category. It assumes coherent F and P of that sum and concludes P F.
- (3) `hP_closed` quantifies over every algebraic space Z and map i to X.
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` expresses
  representability by closed immersions on all scheme tests. The next hypothesis
  requires all etale chart schemes of Z to be reduced. `IrreducibleSpace (Point Z.obj.obj)`
  includes nonemptiness and topological irreducibility in the recorded atlas topology.
- The chosen G is coherent (`G.IsFinitePresentation`) and has full support
  (`moduleSupport G = Set.univ`), using the existing geometric-germ support definition.
- Every nonzero quasi-coherent ideal is `I : QuasiCoherentIdeal Z` with
  `¬ IsZero (I.val : Z.Modules)`. The existing subtype carries its ideal subobject,
  monic inclusion `I.val.arrow` and quasi-coherence; none of those conditions is omitted.
- The witness G' has actual inclusion `g : G' ⟶ G`, `Mono g`, and is quasi-coherent.
  Each of its sections maps into
  `idealPowerSubsheafSections I.val.arrow G (fun _ ↦ Set.univ) 1 T`.
  By that existing definition this is precisely IG, including sections that are finite
  sums of products only locally on a covering sieve. It does not require a global
  expression as a sum of global products.
- The quotient G/G' is an existential Q with q and `IsColimit (CokernelCofork.ofπ q w)`.
  Thus q really is a categorical cokernel, not an arbitrary map or quotient candidate.
  `IsClosed (moduleSupport Q)` and `moduleSupport Q ≠ Set.univ` say its support is
  proper closed in |Z|. Isomorphism uniqueness of cokernels makes this independent of
  the witness. `P ((moduleDirectImage i).obj G')` uses exactly the recorded canonical i_*.
- Conclusion: `∀ F : X.Modules, F.IsFinitePresentation → P F`, with no support restriction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`,
  `IsRepresentableWith`; read their full defining signatures and docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  and its slice sheafification instances; `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` (pqf-def-coherent): publicly exposes
  `RingedSpace.IsCoherent`, `SheafOfModules.IsQuasicoherent`, `IsFiniteType` and retains
  `Scheme.Modules.IsQuasiCoherentFiniteType`. Read the full finite-type-kernel definition
  in `WeilConjectures.AlgebraicGeometry.Coherent`; no lean-record repair needed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace` and
  its underlying `Point` classes; atlas topology retained.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage` and its
  normalized `ModuleDirectImageModel` section-limit universal property.
- Added already-landed definition dependencies `def-sfb-space-module-support`,
  `def-sfb-space-ideal-power-products`, `def-sfb-space-quasi-coherent-ideal` own respectively
  `AlgebraicSpace.moduleSupport` (AlgebraicSpaceModuleSupport),
  `idealPowerSubsheafSections` (AlgebraicSpaceArtinRees), and
  `QuasiCoherentIdeal` (AlgebraicSpaceQuasiCoherentIdeal). Their records and full sources
  were read. No node or definition is copied or created.

Proof-dependency imports are plain imports: AlgebraicSpaceCoherentAbelian,
AlgebraicSpaceCoherentIdealFiltration, AlgebraicSpaceClosedCoherentModules,
SpaceGenericMultipleEmbedding (all under Sheaf.AlgebraicGeometry). Their signatures
and proof docstrings were read. The remaining proof dependencies
lem-sfb-noetherian-space-topology, lem-sfb-space-noetherian-coherent-support, and
lem-sfb-space-closed-immersion-quasi-coherent-modules currently have no Lean record;
there is no module to import. They are not statement prerequisites, and the theorem
proof docstring retains the five-step proof using them. Nothing in the statement
needs a missing notion or a dependency interface repair.

Edge cases checked before writing: empty X (no nonempty irreducible Z; P of zero is
explicit); zero F; r = 1 (identity implication); r = 0 excluded exactly as in the node;
field-valued point (G has positive rank, unit ideal allowed); zero ideal excluded;
unit ideal allowed; nonreduced X allowed (only Z is reduced); reducible X allowed;
proper quotient support may be empty. Nilpotent thickenings and reducible supports
are handled by the recorded ideal-filtration proof plan. P is not assumed invariant
only on coherent modules: the node asks invariance on all module sheaves.

Searches for an existing declaration:

- msearch.py leanfinder: "A property of coherent sheaves on a Noetherian algebraic space
  follows by higher rank devissage" returned 8 scheme Noetherian and general finite-type
  declarations; no algebraic-space devissage.
- msearch.py loogle: `"AlgebraicSpace", "Coherent"` returned 0 hits.
- msearch.py grep: `coherent.*devissage|higherRank|coherentDevissage` returned 0 hits.
- msearch.py leansearch: "A property of coherent sheaves on a Noetherian algebraic space
  holds by higher rank devissage using full support sheaves on integral closed subspaces"
  returned 8 general quasi-coherence/finite-presentation and scheme Noetherian results;
  no exact match.
- rg of lean/WeilConjectures and lean/Sheaf for those names and for `07UT` found scheme
  devissage modules and the existing generic embedding input only. Read the scheme
  CoherentPropertyDevissage and CoherentSupportedPropertyDevissage declarations;
  their scheme category and hypotheses differ. The exact item-id search under
  WeilConjectures returned no match. The final declaration name is new.

No STATEMENT-DISPUTED flag and no statement correction. Sandbox-only edits;
all compilation is via the prescribed scompile.py. The finished module compiles cleanly.

## Second reading by NF

Self-check with the item and module open; no independent worker was started, as required
by the dispatcher brief. The maintainer's separate review remains independent.
Rechecked all clauses above against Tag 07UT and the already-repaired DAG statement.
The initial draft used unbundled monic quasi-coherent ideal data; it was replaced with
existing `QuasiCoherentIdeal` and its owning node added to stmt_deps, avoiding a parallel
interface. Checked that the actual local ideal-product definition supplies sheaf-local
membership, the quotient witness is universal, proper support means both closed and
not universal, and the finite sum is positive. No mathematical mismatch found. The
only node delta beyond lean is adding the three already-landed definition dependencies.
