## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFiniteTypeModuleDetection` states
`AlgebraicGeometry.Scheme.Modules.isFiniteType_iff_etale_extension`, with its proof
entirely `sorry`. The node statement, dependencies, proof plan, and all other
pre-existing fields are unchanged; only `lean` is added. No definitions, helper
nodes, dependency repairs, or statement corrections are needed.

Source checked directly: `literature/stacks-project/spaces-perfect.tex`,
`lemma-descend-finite-type`, Tag 08HD, lines 2863–2920. Its two numbered conditions
are precisely finite type of F and finite type of epsilon-star F, for any scheme
and any structure module. The declaration docstring carries all six DAG proof
steps and their named inputs, including both sheafification lifts and the
faithfully flat geometric-stalk argument.

Clause-by-clause statement correspondence:

- Any scheme X is `(X : Scheme.{u})`, with the explicitly declared universe `u`.
  There are no assumptions on X.
- Any sheaf of O_X-modules F is `(F : X.Modules)`. Mathlib's
  `Scheme.Modules` in `Mathlib.AlgebraicGeometry.Modules.Sheaf` is definitionally
  `SheafOfModules.{u} X.ringCatSheaf`; it places no quasi-coherence requirement.
- The canonical ringed-site tensor pullback is
  `(Classical.choose zariski_etale_functor_comparison_square X).extension`.
  The recorded comparison-square theorem first supplies a family of
  `ZariskiEtaleModuleContext`. Its two fields are solely the continuity proof for
  `gabberOpenEtale X` and the right-adjoint proof for the specified restriction.
  Its `.extension` unfolds to `zariskiEtaleModuleExtension X hc hp`, which uses
  `SheafOfModules.pullback (zariskiEtaleOpenRingMap X)`. The structural ring map
  is the canonical one from restriction of regular functions. All contexts are
  equal by proof irrelevance: no ring, module, functor or map can be arbitrarily
  selected here. The existence theorem determines this object uniquely. The
  theorem therefore has no extra context or adjoint-existence hypothesis.
- Finite type on the Zariski site is `F.IsFiniteType`; finite type on the small
  etale site is `SheafOfModules.IsFiniteType` applied to the displayed extension
  object. Both use Mathlib's existing predicate, not a duplicate. Its
  `exists_localGeneratorsData` requires a covering family and finite generating
  sections on each slice. `GeneratingSections.epi` is an epimorphism from the
  free structure module, and `GeneratingSections.IsFiniteType.finite` makes its
  rank finite. The local cover of the terminal object in this definition is
  equivalent to the statement's cover of every object: pull back the covering
  sieve to each object and restrict its generating sections. This works on
  both the Zariski and small etale sites, including the empty site case.
- The exact biconditional is `↔`; both implications are present. There are no
  quasi-coherence, Noetherian, quasi-compactness, nonemptiness, or positive-rank
  hypotheses.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; full structure signatures were read.
- `lem-trf-zariski-etale-functor-comparison-square`:
  `AlgebraicGeometry.Scheme.Modules.zariski_etale_functor_comparison_square`,
  `Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare`. Its complete signature
  and proof docstring were read. Its leading existential provides the context
  independently of any quasi-coherence assumption in its later clauses.
  The definitions of `ZariskiEtaleModuleContext`, `.extension`,
  `zariskiEtaleModuleExtension`, `zariskiEtaleOpenRingMap`, `smallEtaleModuleRing`,
  and `SmallEtaleModules` were also read in the imported
  `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`, publicly imported as recorded. Its
  transparent body is Mathlib's `SheafOfModules`; `X.Modules` and the etale
  module category are precisely specializations of that same definition. The
  `SheafOfModules` structure, linear morphisms and sheaf condition were read.
- The existing `SheafOfModules.IsFiniteType`, `LocalGeneratorsData`,
  `LocalGeneratorsData.IsFiniteType`, `GeneratingSections`, and
  `GeneratingSections.IsFiniteType` were read in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and publicly imported.
  The etale slice sheafification instances already supplied by the dependency
  module retain u-small module sections on the site whose objects have size
  u+1 and morphisms size u. No site-universe equality was imposed.

The stated proof-dependency modules and Mathlib matches are included as plain
imports. `lem-sfb-etale-zariski-module-geometric-stalk` has no recorded Lean
module in the read clone, so its import is deferred; it is a proof input only
and is not needed to state this equivalence. The maintainer can add that plain
proof import when its module lands. No statement prerequisite is missing.

Edge cases checked against the predicates and the source:

- Empty scheme: the empty covering family gives local finite type on either
  site; no inhabited index type is required.
- Zero module and zero local generators: the finite index type may be empty.
- A scheme that is not quasi-compact: the covering family is arbitrary and
  the finite number of generators may vary with its member.
- Non-Noetherian schemes and arbitrary non-quasi-coherent structure modules
  remain within the unrestricted binders. No finite-presentation condition is
  substituted for finite type.
- The universe `u` is arbitrary. On both sides the actual structure rings and
  module sections are u-small; the small etale object universe is still u+1.

Searches actually run before creating the declaration:

- `msearch.py ... leanfinder`, query: "Finite generation of an arbitrary sheaf
  of modules on a scheme is equivalent to finite generation of its tensor
  pullback to the small etale site". Eight hits, including
  `SheafOfModules.IsFiniteType` and the finite generating-section predicates;
  no change-of-topology detection equivalence.
- `msearch.py ... loogle`, query: `SheafOfModules.IsFiniteType`. Four hits: the
  predicate, its constructor and local-generator field, and finite presentation
  implying finite type; no detection theorem.
- `msearch.py ... leansearch`, query: "Finite type of an arbitrary structure
  module on a scheme is detected by tensor pullback from the Zariski topology
  to the small etale topology". Eight hits, including the finite-type predicate,
  small etale topology and unrelated finite-type scheme morphisms; no match.
- `msearch.py ... grep`, query: `IsFiniteType|finiteType`, restricted to
  `Algebra/Category/ModuleCat/Sheaf`. Ten reported hits in `Generators` and
  `Quasicoherent`, confirming the available local finite-generation notions.
- Direct `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`, for
  `IsFiniteType.*[Ee]tale|[Ee]tale.*IsFiniteType|isFiniteType.*[Ee]tale|[Ee]tale.*isFiniteType`
  and finite-type/Zariski combinations. The etale-module finite-type hits use
  constant coefficient ModuleCat sheaves and do not state this structure-module
  detection result. `FpqcFiniteTypeModuleDescent` assumes quasi-coherence and
  concerns scheme pullbacks, so it is not the present theorem.
- Direct search for the item id in the source library found no declaration;
  search for `isFiniteType_iff_etale_extension` in Mathlib, both project roots,
  and `dag/lean_names_upstream.json` found no prior declaration.

No statement dispute or node fault was found.

## Second reading by Q120

Final worker rereading, with the node, source lemma, file and the dependency
context definitions open; independent acceptance review is left to the
maintainer, as the dispatcher brief specifies. No second agent was started.
The two explicit binders match the two objects of 08HD. The left and right
predicates are the very same Mathlib local finite-generation predicate on their
respective ringed sites. The leading existential of the comparison-square
result has no quasi-coherence binder; consequently its context can be used for
this arbitrary F, despite the quasi-coherent clauses later in that theorem.
The choice of context cannot change the functor because all its fields are
proofs about specified constructions. This rules out an arbitrary-pullback or
extra-context hypothesis. Neither finite presentation nor global generation
has replaced local finite type. The free-module indices can be empty, and
there is no bound on the covering family or generator ranks. The only repair
found was an overlong source line; the signature was wrapped without changing
its meaning. All universes and variables are explicitly bound, and the only
postponed proof is the named theorem with this node's full proof docstring.

Validation: the final file was compiled separately in module mode through
`scompile.py`, both under the sandbox name and its intended library module name.
The final output was clean. The required `deliver2.py --no-push` preflight and
per-file compile are run before delivery.
