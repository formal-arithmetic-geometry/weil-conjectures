## Worker report

Item: `lem-coef-rigidification-equivalence-detection`; group NH; 2026-10-16 UTC.

The module `Sheaf.AlgebraicTopology.RigidificationEquivalenceDetection` states
`SSet.rigidification_equivalence_detection`. It introduces one theorem, with whole proof
`sorry`, and no definitions. Its docstring contains all eight proof steps from the node,
including the explicit cube calculation, the inner-horn replacement, the pinched comparison,
the coherent-inverse argument, the two-test argument, and the final two-out-of-three square.
Nothing is proved in this stage.

Source checked: [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Theorem the project server(W), printed page 89 (PDF page 107), and Proposition the project server,
printed pages 94–95. They supply the detection assertion and its testing formulation.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Simplicial sets S and T, with no fibrancy assumption | `{S T : SSet.{u}}` |
| Every simplicial map f : S → T | `(f : S ⟶ T)`; these are natural transformations |
| Small simplicial categories with arbitrary-object enriched functors | `CategoryTheory.CoherentNerve.SCat.{u}`, the codomain of `Pinched.rigidification`; inherited from the recorded interval-lifting module |
| Objects 0,…,n of the coherent simplex, for all n ≥ 0 | `SSet.Pinched.coherentSimplex.obj n` is `EnrichedCat.of SSet (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))` |
| Mapping simplicial set is the nerve of endpoint-containing subsets of [i,j], ordered by inclusion | Mathlib `SimplicialThickening.Path` has `I : Set J`, endpoint membership and interval bounds; its category is induced by inclusion of `I`; `SimplicialCategory.Hom` is `nerve (i ⟶ j)` |
| Empty mapping set when i > j | The same Path type is empty: its `Path.le` forces i ≤ j. Its nerve therefore has no simplices in any degree |
| Union composition and singleton identity | Mathlib `SimplicialThickening` comp uses `f.I ∪ g.I`, and id uses `{i.as}`; enriched composition is its nerve |
| Monotone maps act by image of subsets | `SimplicialThickening.functor a.toOrderHom.uliftMap`; its `functorMap` applies `f '' I.I` |
| Rigidification is the colimit over all simplices Δⁿ → S in sCat | Existing `SSet.Pinched.rigidification := SSet.stdSimplex.leftKanExtension coherentSimplex`; the pointwise left Kan extension is the colimit indexed by `CostructuredArrow stdSimplex S`, with the canonical action on arrows |
| Induced map C[f] | `Pinched.rigidification.map f`, rather than an arbitrary enriched map |
| Dwyer–Kan equivalence | `Bergner.dwyerKanEquivalences (Pinched.rigidification.map f)`; the recorded definition applies `CategoryTheory.DwyerKanEquivalence` to the underlying enrichments |
| Local weak homotopy equivalences and equivalence of π₀ categories | `DwyerKanEquivalence` asserts weak equivalence on every mapping set, and `PiZeroEquivalence`, which asserts bijections on all component hom sets and `PiZeroEssentiallySurjective` |
| If and only if | The theorem's `↔` |
| Every quasicategory Z in a sufficiently large universe | `∀ (Z : SSet.{max u v}), Z.Quasicategory → ...`; both `u` and the independent enlargement `v` are explicit |
| Restriction Fun(T,Z) → Fun(S,Z) | `(MonoidalClosed.pre (uliftFunctor.{v, u}.map f)).app Z`; the canonical degreewise lift places f in Z's universe |
| hFun(T,Z) → hFun(S,Z) is an equivalence of ordinary categories | `((hoFunctor.map ...).toFunctor).IsEquivalence` |

The testing expression is exactly the weak-equivalence expression in the recorded
`SSet.exists_joyal_model_structure`, with only the bound name C renamed Z. In particular the
older infrastructure's core-testing `CoherentNerve.IsCategoricalEquivalence` is not substituted
for the homotopy-category test specified by this node. `hoFunctor` is Mathlib's category
presented by vertices, edges, degenerate-edge identities and triangle relations.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`: `SSet`, the Mathlib match of
  `def-weil-pbc-simplicial-set`. Its related recorded `degenerate`, `nonDegenerate`,
  `Subcomplex`, and `SSet.Finite` signatures were also checked; the present theorem only needs
  `SSet` and its natural transformations.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, whose cocompleteness clause supplies the
  `SSet.Pinched.sCatColimits` instance used by rigidification. The category itself is the
  already shared `CategoryTheory.CoherentNerve.SCat` and `sCatCategory` from
  `Sheaf.CategoryTheory.CoherentNerveInfrastructure`.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, for the precise enlarged-universe testing interface.
- `Sheaf.AlgebraicTopology.SimplicialIntervalCellStability`:
  `SSet.Bergner.dwyerKanEquivalences`, `simplicial_interval_cell_stability`;
  this uses the shared `CategoryTheory.DwyerKanEquivalence`, `PiZeroEquivalence` and
  `PiZeroEssentiallySurjective` from `Sheaf.CategoryTheory.CoherentNerveComparison`.
- `Sheaf.CategoryTheory.PinchedRigidificationResolution`:
  `SSet.Pinched.coherentSimplex`, `rigidification`, `sCatColimits`,
  `sCatColimitsSmallHom`, and `pinched_rigidification_resolution`. The first two have real
  construction data and implement exactly the construction described in this item.
- The other stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` (`SSet.Enhanced` diagram and equivalence
  notions), `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
  (`SSet.Enhanced.enhanced_functor_cone_calculus`),
  `Sheaf.Topology.HomotopyGroupsBasepointChange`
  (`SSet.Enhanced.homotopyGroups_basepoint_change`),
  `Sheaf.CategoryTheory.InfinityMappingComposition` (`SSet.Enhanced.mapping_composition`),
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`
  (`SSet.KanQuillen.right_proper_kan_quillen`),
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits` (`SSet.realization_finite_limits`), and
  `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`
  (`CategoryTheory.SmallObject.functorialFactorizationData`). The proof dependency
  `lem-coef-infinity-full-essential-image` has no recorded Lean declaration or Mathlib match
  in the current DAG, so there is no module for it to import. Its mathematical use remains in
  the complete proof docstring; no missing notion from it is needed to type this statement.

The only DAG changes are the `lean` record and addition to `stmt_deps` of the already landed
`lem-coef-pinched-rigidification-resolution`. This is authorized by brief-stage2 §5, because its
actual rigidification construction is used in the signature. It was already a proof dependency.
There is no change to the natural-language statement, proof, or proof dependencies, no new node,
and no dependency-module repair.

Edge cases checked before writing:

- n = 0: the sole endpoint-containing subset is the singleton, yielding its identity mapping
  point. For i = j in any dimension the same observation supplies the identity.
- i > j: endpoint and interval requirements are inconsistent, yielding the required empty
  nerve, rather than a point.
- A monotone map can identify endpoints: taking images of subsets still gives a valid path,
  including the singleton identity. No injectivity assumption is imposed on the ordinal map.
- Empty S and T are allowed. The empty simplicial set has no simplices, so rigidification is
  the empty colimit. For empty-to-nonempty f, neither equivalence condition becomes vacuous:
  the DK side still requires essential surjectivity, and the right side tests all quasicategories.
- Identity maps and isomorphisms are included. The theorem does not require S or T to be
  nonempty, connected, Kan, quasicategories, or finite.
- Universe u is arbitrary, including 0. `max u v` contains the canonical lift of every input
  degree set; v is independently arbitrary and can enlarge the testing universe. There is no
  imposed equality of independent universes and no vacuous small-universe quantification.
- No local Kan hypothesis is attached to the simplicial categories C[S] or C[T].

Searches made (all required semantic and grep searches were run with `msearch.py`):

| Tool | Query | Result and assessment |
| --- | --- | --- |
| LeanFinder | A map of simplicial sets is a categorical equivalence if and only if its coherent realization is a Dwyer Kan equivalence | 8 hits: truncated homotopy category adjunction/equivalences, hoFunctor unitHomEquiv, nerveAdjunction, terminalIso, skeletalFunctor equivalence; none states detection |
| Loogle | SimplicialThickening, DwyerKanEquivalence | 0 hits, unknown indexed identifier SimplicialThickening; followed by a valid identifier query |
| Loogle | SSet.hoFunctor | 12 hits; the homotopy category functor, its action, product and terminal comparisons; confirms the hFun encoding but no rigidification criterion |
| LeanSearch | Coherent realization of simplicial sets detects categorical equivalences as Dwyer Kan equivalences | 8 hits: topological realization/singular adjunction, Kan complexes and Kan-model cofibrations; none states detection |
| msearch grep | rigidification\|DwyerKan\|CategoricalEquivalence, Mathlib/AlgebraicTopology | 0 hits |
| rg, upstream WeilConjectures | rigidification\|DwyerKan\|CategoricalEquivalence | Only unrelated rigidifications of Fourier/Picard line bundles; no coherent realization or detection theorem |
| rg, upstream WeilConjectures | lem-coef-rigidification-equivalence-detection | No hit |
| rg, project lean/Sheaf | rigidification, DwyerKan, coherent realization, SCat | Located the existing Pinched construction, infrastructure and DK predicate; no detection theorem |
| rg, Mathlib | SimplicialThickening, poset, subset, union in SimplicialNerve.lean | Read Path and its category, union composition, nerve enrichment, image functor, and the full thickening functor signature |
| rg, dag/lean_names_upstream.json | rigidification, isCategoricalEquivalence, rigidification_equivalence_detection | No hit |
| rg, Mathlib + upstream + project | rigidification_equivalence_detection | No pre-existing full-name collision |

Validation: prescribed `scompile.py NH lem-coef-rigidification-equivalence-detection` compiled
this delivered module cleanly, both as sandbox source and under its library module path.
The wrapper also compiled the required cell-stability and pinched-resolution overlay modules.
No warnings or errors were reported. Every variable and universe is explicitly bound and
`autoImplicit` is disabled. All lines are at most 100 characters.

No statement dispute or mathematical node fault was found.

## Second reading by NH

The node statement was read verbatim and matched clause by clause against
`Sheaf.AlgebraicTopology.RigidificationEquivalenceDetection` and its dependency
declarations.

* The objects are simplicial sets `S T : SSet.{u}` and a simplicial map
  `f : S ⟶ T`; these are exactly the node's objects, with no fibrancy,
  nonemptiness, finiteness, or characteristic hypothesis.
* The coherent simplex data (objects `0,...,n`, endpoint-subset nerves,
  empty maps for `i > j`, union composition, and image-of-subsets functors)
  is the recorded `SSet.Pinched.coherentSimplex` construction from
  `lem-coef-pinched-rigidification-resolution`, whose signature and source
  were reread.  Its `SSet.Pinched.rigidification` is the simplex colimit in
  the landed `CategoryTheory.CoherentNerve.SCat`; the theorem uses its
  canonical map `Pinched.rigidification.map f`, not an arbitrary enriched map.
* The left side is exactly the recorded
  `Bergner.dwyerKanEquivalences` predicate, hence mappingwise weak homotopy
  equivalences together with equivalence on component categories.  No local
  Kan condition is added.
* The right side is the node's universal testing clause:
  `∀ Z : SSet.{max u v}, Z.Quasicategory`, followed by equivalence of
  `hoFunctor` after restriction along the universe-preserving
  `uliftFunctor.{v,u}.map f`.  The expression is verbatim the categorical
  equivalence clause of `SSet.exists_joyal_model_structure`; `v` remains an
  independent enlargement.
* The final connective is `↔`, so both directions and all quantifiers are
  retained.  The theorem has no additional assumptions and no weakened
  conclusion.

Dependency rereading found the following.  `SSet.Bergner.simplicial_interval_lifting`
  supplies the same arbitrary-object enriched category, colimits, and interval
  generators used by the node.  `SSet.exists_joyal_model_structure` supplies
  exactly the enlarged-universe homotopy-category testing convention.
  `SSet.Bergner.simplicial_interval_cell_stability` uses the shared
  `CategoryTheory.DwyerKanEquivalence` and supplies two-out-of-three and cell
  stability.  `SSet.Pinched.pinched_rigidification_resolution` supplies the
  actual coherent simplex and rigidification constructions and was therefore
  added to `stmt_deps`; its definitions use real colimit and thickening data.
  No dependency module was repaired and no hollow definition was introduced.

Edge cases checked are `n = 0` (singleton endpoint path and identity), `i > j`
(empty mapping set), repeated endpoints under noninjective monotone maps,
empty simplicial sets, identity and isomorphism maps, arbitrary universe
`u` including zero, and arbitrary independent test enlargement `v`.  The
statement covers all of them and imposes no hidden Kan, quasicategory,
connectedness, or finiteness condition on `S` or `T`.

The semantic searches were repeated with LeanFinder, Loogle, LeanSearch,
`rg` in Mathlib, the upstream `WeilConjectures` tree, and the project
`lean/Sheaf` tree for rigidification, coherent realization, Dwyer--Kan
equivalence, categorical-equivalence detection, and the full declaration
name.  They found only the already recorded constructions and predicates;
no existing detection theorem or duplicate notion exists.  The prescribed
`scompile.py` check compiled the module and its overlay dependencies cleanly.
No mismatch was found, so no Lean or statement repair was needed beyond the
recorded `stmt_deps` addition for the canonical rigidification dependency.
