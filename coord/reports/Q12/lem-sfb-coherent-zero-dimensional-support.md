## Worker report

States `AlgebraicGeometry.Scheme.Modules.coherent_zero_dimensional_support` in
`Sheaf.AlgebraicGeometry.CoherentZeroDimensionalSupport`. Its only proof is `by sorry`.
No definitions, dependency repairs, additional nodes, or statement changes are needed.

Source read: `literature/stacks-project/coherent.tex`, lines 2487–2509,
Tag 0B3J, `lemma-coherent-support-dimension-0`, including its proof. The DAG expands
the immediate zero-global-sections consequence and gives the flasque proof route.

Hypothesis and conclusion correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`, with explicit universe `u`.
- Locally Noetherian is `[IsLocallyNoetherian X]`, the recorded Mathlib class.
- An O_X-module is `(F : X.Modules)`, the project's sheaves of modules over
  `moduleRings X.toRingedSpace`.
- Coherent is `hF : RingedSpace.IsCoherent X.toRingedSpace F`: finite type and the
  finite-type-kernel condition, not merely quasi-coherence plus finite presentation.
- The support is exactly `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`. Stalks
  are the Mathlib stalks used by the recorded presheaf module stalk functor;
  no new support or stalk construction is introduced.
- Its dimension is `topologicalKrullDim` of that subtype with its subspace topology;
  `hdim` asserts `≤ 0`, allowing dimension minus infinity for empty support.
- The evaluation is `Sigma.desc (fun s : F.presheaf.obj (op ⊤) ↦
  homOfGlobalSection F s)`. Its domain is the coproduct of copies of O_X indexed
  by **all actual global sections**, not a chosen finite family. The existing
  `homOfGlobalSection` has source `Scheme.Modules.unit X` and sends a local
  coefficient r to r times the restriction of s. Thus this is precisely the map
  displayed in the node. `Epi` expresses surjectivity as a sheaf map (local
  surjectivity, not surjectivity on sections of every open).
- Higher cohomology vanishing is `∀ i : ℕ, 0 < i → IsZero
  ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)`, using the recorded
  right-derived functors of global sections in module sheaves.
- The final implication is `Subsingleton (F.presheaf.obj (op ⊤)) → IsZero F`.
  Since global sections form a module, subsingleton means that module is zero;
  `IsZero F` means the sheaf itself is a zero object.

Recorded statement dependencies read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; full class and documentation read.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly
  exposes `WeilConjectures.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`. Read both modules, including the
  current record's note explaining why its retained quasi-coherent-finite-type
  conjunction is not the coherence predicate.
- `def-weil-pbc-module-stalk`:
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj`; these bundle exactly
  the underlying Mathlib `F.presheaf.stalk x` used here.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, whose definition is `krullDim (IrreducibleCloseds T)`.
- `def-sc-ringed-space-module-cohomology`:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`; read its definition,
  `globalSectionsFunctor`, resolution comparison and docstrings.

The evaluation additionally uses existing
`WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`,
`AlgebraicGeometry.Scheme.Modules.homOfGlobalSection`, whose construction and
`homOfGlobalSection_app` formula were read. The coproduct is Mathlib's
`CategoryTheory.Limits.Sigma.desc`; no helper construction is copied.
All available proof-dependency modules are imported without `public` unless
already needed publicly. This includes the coherent finite-type equivalence,
scheme-theoretic support, closed immersion/immersion properties, the coherent
closed-immersion equivalence, the Artinian/discrete criterion, closed pushforward
stalks, flasqueness and module flasque acyclicity. Their proof roles appear in the
six-step theorem docstring.

Edge cases checked mathematically: empty X; zero F; empty support, whose dimension
is minus infinity; a one-point support; infinitely many isolated support points
on a non-quasi-compact scheme; no separation assumption; degree zero is excluded
from the vanishing assertion. Global sections always contain zero; the coproduct
index is their whole Type u, with no finiteness or nonemptiness assumption added.
For infinite support one glues with zero on the open complement, so neither
finite support nor a finite global generating family is silently asserted.

Searches for existing statements and notions (2026-10-24):

- `msearch.py ... leanfinder "A coherent sheaf with zero dimensional support on a
  locally Noetherian scheme is globally generated and has vanishing higher
  cohomology"`: eight hits, notably Mathlib locally Artinian criteria and
  `SheafOfModules.GeneratingSections.IsFiniteType`; none states this result.
- `msearch.py ... leansearch "coherent sheaf zero dimensional support generated
  global sections vanishing cohomology"`: eight hits about zero loci and
  algebraic module support dimension; no matching sheaf theorem.
- `msearch.py ... loogle "SheafOfModules, globalSections, generated"`: zero hits,
  with unknown identifier `globalSections`; not treated as evidence of absence
  by itself. Source searches below located the actual existing canonical map.
- `msearch.py ... grep
  "globallyGenerated|GloballyGenerated|evaluationMap|globalSections.*[eE]pi|[eE]pi.*globalSections"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of those patterns in `lean/WeilConjectures` and `lean/Sheaf`: found étale
  global-generation predicates and other evaluation maps, which concern different
  categories. The existing `FindGloballyGenerated` and `TensorGloballyGenerated`
  statements use generating sections but do not state this coherent-support result.
- `grep -rn "lem-sfb-coherent-zero-dimensional-support" lean/WeilConjectures`:
  no attachment. Source `rg` for global generation and sections found
  `homOfGlobalSection` and its exact local formula. Read Mathlib's sheaf
  `Generators.lean` and `Free.lean`: free sheaves are coproducts of unit sheaves.
- DAG search for generation/evaluation titles and source declaration names found
  `def-weil-pbc-generating-sections`, an already recorded general notion. No
  new definition node is needed: the theorem directly spells out the evaluation
  using existing coproduct and section-map APIs.

No mathematical dispute or node fault found. The example module requested by the
brief is now withdrawn; its node records the upstream compact-object declaration.
The delivery follows the required current module/public-import/expose conventions.

Validation: the prescribed `scompile.py` compiled both sandbox and library module
successfully, with no diagnostics. The final import list also includes the exact
Mathlib immersion module of the proof dependency; final compile and delivery
preflight results are recorded below.

## Second reading by Q12

Author's second reading (the dispatcher brief prohibits starting another agent;
the maintainer supplies the independent review). Reopened the node and Lean file
and checked each clause: arbitrary locally Noetherian X, coherent F in the recorded
category, the exact nonzero-stalk support subtype with dimension ≤ 0, evaluation
indexed by all F(X) sections, vanishing only in positive natural degrees for the
recorded module cohomology, and the zero-section implication. In particular,
`Sigma.desc` uses the actual canonical section maps, not arbitrary maps or a
sectionwise-surjectivity assertion. No properness, quasi-compactness, finite
support, separation, or nonempty hypothesis appears. No mismatch found and no
statement change made. The theorem docstring contains all six DAG proof steps.

Final validation: the final import list compiled cleanly in sandbox and library
module modes (1.5 s and 1.6 s). `deliver2.py Q12
lem-sfb-coherent-zero-dimensional-support --no-push` returned
`OK (dry run): commit 12fb2d63cf4 passes the preflight and compiles; nothing pushed`.
The node comparison confirmed that `lean` is the only changed field.
