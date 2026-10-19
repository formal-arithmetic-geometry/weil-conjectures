## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition` states
`AlgebraicGeometry.Etale.properSupportSheafComposition`, with its entire proof `sorry`.
No definition, supporting theorem, new node, dependency replacement, or statement correction
is introduced. The node copy changes only `lean`.

The statement simultaneously specifies the proper-support functors `L f`, their natural
inclusions `ι f`, and the comparison isomorphisms. It uses an existential presentation of
these objects, rather than choosing functor data from an unproved existence statement.
There is no data-valued definition containing or choosing from `sorry`. The sectionwise
image property determines the subsheaf uniquely; its natural inclusion then determines
all maps and comparison maps. Thus an arbitrary isomorphic model is allowed, but its
inclusion and all comparison maps have the prescribed underlying-section behavior.
This represents equality of subsheaves by their canonical isomorphism over the ambient
sheaf, not by equality of arbitrary chosen sheaf objects.

Hypotheses and objects, clause by clause:

- A commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`.
  The module sheaf category is `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`,
  the encoding explicitly permitted by the recorded etale-sheaves dependency for the
  six-functor chapters. There is no torsion, finiteness, constructibility, or Noetherian
  condition on coefficients or schemes.
- Schemes are `Scheme.{u}`. Every scheme variable and universe is explicitly bound.
  The theorem is universe-polymorphic. Geometric fields lie in `Type u`, the same
  universe as the schemes and their residue fields; every point admits such a geometric
  point. They are separably closed, as required by `pointSmallEtale`.
- Each morphism in `L` and `ι` has `[IsSeparated f] [LocallyOfFiniteType f]`.
  In the composition clause these hypotheses are present for both `f` and `g`.
  Their composite satisfies them by the existing instances.
- `F` ranges over all module sheaves on the specified small etale site; `V : Y.Etale`
  ranges over all etale test objects. The existing pullback functor
  `MorphismProperty.Over.pullback @Etale ⊤ f` sends `V` to the scheme
  `pullback V.hom f` viewed as an etale object over `X`.
- The first conjunct says the map of sections of `ι f` is injective on every `V`.
  Hence `L f` is represented as a genuine subsheaf of the recorded ordinary direct image.
- Its image property is `(∃ t, (((ι f).app F).hom.app (op V)) t = s) ↔ ...`.
  The right side quantifies a closed subset `T` of that pullback. For every geometric
  point `v` of the pullback, membership `v default ∈ T` is equivalent to nonvanishing
  of the germ of `s`. The germ is the actual `pointSmallEtale.toPresheafFiber` at
  the pointed etale neighbourhood `Over.homMk v`, not a second stalk construction.
  Thus `T` is precisely the closed geometric-germ support specified by the node.
- The support is given its reduced induced closed structure by
  `(Scheme.IdealSheafData.vanishingIdeal T).subschemeι`. The condition is exactly
  `IsProper (...subschemeι ≫ pullback.fst V.hom f)`, proper over `V`, not merely
  quasi-compact support, a topologically proper map, or properness over `Y`.
- For proper `f`, `IsIso ((ι f).app F)` says that this subsheaf is the whole ordinary
  direct image. The comparison is the very same inclusion, hence identity on sections
  under this subsheaf identification, and is natural in `F`.
- For an open immersion, the existential natural isomorphism `o` has
  `o.hom ≫ ι f = openImmersionLowerShriekToLowerStar ... f`. This identifies the support
  subsheaf with extension by zero using the existing canonical map into ordinary direct
  image. Merely asking for an unspecified isomorphism is deliberately avoided.
- `c X Y Z f g : L f ⋙ L g ≅ L (f ≫ g)` is the composition identification. Its equation
  after the inclusion is precisely the composite of `ι g`, the pushforward of `ι f`,
  and the recorded `lowerStarComp`. This says equality as subsheaves of the composite
  ordinary direct image, with the ordinary pullback-pasting identification of sections.
- `e ... sq : L f ⋙ upperStar ... b ≅ upperStar ... a ⋙ L f'` is base change for any
  Cartesian square `sq : IsPullback a f' f b`. There is no property assumed of `a` or `b`.
  The typeclass hypotheses on `f'` are redundant consequences of `sq` and the hypotheses
  on `f`; they let the already bound family `L` be applied directly without hidden
  proof-valued let/have binders. This excludes no Cartesian square.
- The base-change equation composes `e.hom.app F` with the target inclusion. Its right
  side is `b` inverse image of the source inclusion followed by the ordinary comparison:
  the unit for `f'`, the inverse-image square compositor, and inverse image of the counit
  for `f`, pushed forward by `f'`. The square compositor is formed from the recorded
  `upperStarComp`, using `sq.w.symm` to identify the two composite scheme morphisms.
  Hence it asserts restriction of the ordinary comparison, not existence of some
  unrelated base-change isomorphism.
- The final equation quantifies two stacked Cartesian squares `sf`, `sg` and a Cartesian
  proof `sfg` for the outside rectangle, and states the two paths using `c` and `e` agree.
  The direct path is inverse image of `c` followed by `e` for the composite; the other
  path is `e` for `g`, pushforward by `L g'` of `e` for `f`, and target composition `c`.
  The outside rectangle is automatically Cartesian by pasting; quantifying its proof
  adds no geometric hypothesis, and all proofs of it are propositionally equal.
- Naturality is encoded by functors, natural transformations, and natural isomorphisms
  throughout. Every component is a morphism of module sheaves, so the section maps and
  all identifications are Λ-linear. No extra additive/linear structure is invented.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, with its
  inherited separatedness and local finite type; separatedness is `IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the canonical etale-sheaf dependency
  module. Its recorded note permits precisely the `Sheaf ... (ModuleCat Λ)` encoding.
  Its old source is still readable as `lean/Sheaf/AlgebraicGeometry/EtaleSheaves.lean`;
  the newer upstream module is absent in the local old source checkout but is available
  on the server, where the complete import set was compiled successfully.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`, `Etale.lowerStarComp`,
  `Etale.upperStarComp`; their full signatures and documentation were read.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`
  and `toPresheafFiber`; `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.pointSmallEtale`. The germ lands in the presheaf fiber, definitionally the
  sheaf fiber of this sheaf.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`; its actual vanishing-ideal
  construction supplies the reduced induced subscheme used in the properness condition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `IsPullback` for the Cartesian assertions.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`; `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`:
  `Etale.openImmersionLowerShriekToLowerStar`, the canonical open comparison.

Every recorded module for a stated proof dependency is imported without `public`, unless
already a statement import. This includes the zero-locus theorem, the two closed-support
properness modules, open stalk comparison, inverse-image germs, inverse-image compositors,
and the module inverse-image exactness theorem. The two proof nodes
`lem-cbc-closed-proper-support-locality` and `lem-cbc-proper-support-geometric-stalk` have no
Lean record yet, so there is no module to import for them. Mathlib proof dependencies use
Proper, ClosedImmersion, UniversallyClosed, Separated, and Adjunction.Mates.

Edge cases checked against the source and statement:

- Zero sheaf and zero section: all germs vanish, the unique support is empty, and its
  reduced closed subscheme is empty and proper over the test object.
- Empty schemes and empty etale test objects: there is no nonempty geometric support;
  all clauses allow these objects and impose no Nonempty hypothesis.
- Identity maps and maps both open and proper: support composition is over the same
  ordinary direct image, so it agrees with the proper and open specializations.
- Non-quasi-compact separated locally finite type morphisms are allowed. Properness is
  required only of the support; no quasi-compactness condition is imposed on `f` or `g`.
- Arbitrary coefficient ring, including the zero ring, and arbitrary characteristic.
  Base-change maps are unrestricted, including maps to geometric points.
- The two possible support-functor representations give the same subobject; the equations
  with inclusions prevent rescaling or unrelated comparison choices.

Searches for an existing statement:

- `msearch.py`, LeanFinder, query: "Composition and arbitrary base change of direct image
  of etale module sheaves with proper support". Eight hits, concerning stability of
  etale maps and Kaehler differentials; none gives this support-subsheaf statement.
- `msearch.py`, Loogle, query: "AlgebraicGeometry.Etale.lowerStar, AlgebraicGeometry.IsProper".
  No hits; the service reports the project-specific lowerStar name unknown.
- `msearch.py`, grep, query: `properSupport|proper.support|ProperSupport`. No Mathlib hits.
- `msearch.py`, LeanSearch, query: "Proper support direct image of etale module sheaves
  composes and commutes with arbitrary base change". Service unavailable (Internal Server
  Error); no mathematical conclusion drawn from that failure.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf`, same proper-support patterns:
  hits describe coherent-module supports, derived functors or pro-etale operations, not
  this underived etale support-subsheaf construction.
- `grep -rn` of the item id in upstream `WeilConjectures`: no hits.
- `rg` for `properSupportSheafComposition` in Mathlib, upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.
- Read the existing lower-star, upper-star, composition and extension-by-zero declarations,
  their docstrings, and the Stacks source `more-etale.tex` section-compact-support,
  lemma-f-shriek-separated, lemma-f-shriek-composition, lemma-base-change-f-shriek-separated,
  and remark-f-shriek-base-change-composition. No exact prior statement was found.

Validation: the delivered module compiled cleanly via `scompile.py` on the server,
including the canonical open comparison equation (1.9 seconds for this file, nice 19,
two threads, 60-second per-file limit). No local Lean compiler or global build was run.
No statement dispute or node correction was needed.

## Second reading by NS

I independently read the item node, its complete proof, its ten statement-dependency
nodes and their recorded signatures, and the delivered Lean module. I read
`more-etale.tex` section-compact-support and the full statements and proofs of
lemma-f-shriek-separated, lemma-separated-etale-shriek,
lemma-base-change-f-shriek-separated, lemma-f-shriek-composition and
remark-f-shriek-base-change-composition. The section assumes separated, locally finite
type morphisms, not quasi-compact or Noetherian schemes. Its abelian-sheaf construction
extends sectionwise to an arbitrary commutative coefficient ring as stated by this node.

Object/hypothesis/conclusion inventory and comparison (H3):

1. A commutative ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ]`. PASS. No finite,
   nonzero, torsion or characteristic assumption. This is the ModuleCat encoding explicitly
   permitted in the etale-sheaves dependency record for the six-functor chapters.
2. Schemes X, Y, Z and composable separated locally finite type maps f, g:
   `Scheme.{u}`, `(f : X ⟶ Y) (g : Y ⟶ Z)`, `[IsSeparated f]`
   `[LocallyOfFiniteType f]` and the corresponding g instances. PASS. I read the Mathlib
   class signatures: separated means closed diagonal; local finite type is the affine
   ring-map condition. There is no QuasiCompact hypothesis.
3. Every module sheaf F on X_et and every etale V over Y: `Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)` and `V : Y.Etale`. PASS. The object
   `(MorphismProperty.Over.pullback @Etale ⊤ f).obj V` is V times_Y X over X,
   canonically the node's X times_Y V. I read `lowerStar` and its section formula in
   UpperLowerStar/Defs.lean: no different direct image is being used.
4. The subsheaf of proper-support sections: the existential functor `L` and natural
   inclusion `ι`, sectionwise `Function.Injective`, and the image biconditional
   `(∃ t, (((ι f).app F).hom.app (op V)) t = s) ↔ ...`. PASS. The image is exactly the
   prescribed submodule, so the abstract representation does not weaken the subsheaf
   assertion; naturality also determines its action on sheaf morphisms.
5. Closed support exactly where geometric germs are nonzero: `∃ T :
   TopologicalSpace.Closeds ...`, followed by `v default ∈ T ↔ ... s ≠ 0` for all
   separably closed fields and geometric points v. PASS. I read `pointSmallEtale`,
   `Point.toPresheafFiber` and `Point.sheafFiber`: the germ is the colimit insertion
   at the actual pointed neighbourhood `(V times_Y X, v)`, with base point the composite
   into X. This is the dependency's stalk, not a substitute support notion.
6. The reduced support is proper over V: `IsProper
   ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ pullback.fst V.hom f)`.
   PASS. I read ReducedInducedClosedSubscheme.lean: precisely this ideal's subscheme is
   reduced, closed and has range T. Its structure map here goes to V, as required.
7. Composition equality inside ordinary pushforward, identity on underlying sections:
   `c : L f ⋙ L g ≅ L (f ≫ g)` and the equation after `(ι (f ≫ g)).app F`. PASS.
   The right side first includes the outer support sheaf, then pushes forward the inner
   inclusion, then uses `lowerStarComp`. I read that compositor's definition and its
   pullback-pasting orientation. Thus the equality is over the specified ambient sheaf,
   not just an unrelated natural isomorphism.
8. Proper specialization: `[IsProper f]` and `IsIso ((ι f).app F)`. PASS. The very same
   inclusion identifies the support sheaf with f_*F, naturally in F; properness supplies
   the separated and local finite type instances needed by L.
9. Open specialization: `[IsOpenImmersion f]` and `∃ o :
   openImmersionLowerShriek ... f ≅ L f`, with `o.hom ≫ ι f =
   openImmersionLowerShriekToLowerStar ... f`. PASS. I read the recorded extension
   functor and this canonical comparison from the adjoint triple. The equation fixes
   the identification inside f_*F exactly as in the source.
10. Arbitrary Cartesian square with projections a,b and map f': `sq : IsPullback
    a f' f b`, with no hypotheses on a,b, and `e : L f ⋙ upperStar ... b ≅
    upperStar ... a ⋙ L f'`. PASS. The explicit separated/local finite type instances
    on f' follow from the Cartesian square and do not remove a case.
11. Restriction of ordinary pullback comparison: the equation after `e.hom.app F`
    and the f' inclusion equals inverse image of the original inclusion, the f' unit,
    inverse-image square compositor and pushed-forward f counit. PASS. I checked the
    definitions of `upperStar`, `upperStarLowerStarAdjunction` and `upperStarComp`.
    The use of `sq.w.symm` identifies f' followed by b with a followed by f in the
    correct direction. This is exactly the ordinary adjunction comparison.
12. Compatibility with two stacked squares: the last universally quantified equation
    uses `sf`, `sg`, the outside rectangle `sfg`, the inverse image of c and exchange
    for the composite on one side; exchanges for g and f followed by target c on the
    other. PASS. The outside rectangle is automatically Cartesian by pasting, so
    quantifying its proof adds no restriction. Both sides have identical source and
    target. This is part (2) of the source remark, as requested by the node.
13. Naturality and Lambda-linearity: `L` is a functor, inclusions are natural
    transformations, and c,e,o are natural isomorphisms, all in module-valued sheaves.
    PASS. Their components and all section maps are Lambda-linear. The inclusion's
    naturality and injectivity also force L's maps to be the original maps restricted
    to support submodules; arbitrary nonlinear actions cannot satisfy the statement.

Edge cases: the zero sheaf, zero section and zero coefficient ring give empty support;
its reduced subscheme is empty and proper. Empty schemes and empty V are permitted;
there is no Nonempty binder. Identity maps and open/proper maps satisfy both respective
specializations through the same inclusion. Non-quasi-compact locally finite type maps
remain covered. There is no index-set or integer parameter, so empty index sets and
n = 0 impose no restriction. The characteristic is unrestricted. The universe u is
bound; all schemes share an arbitrary universe as in the dependency functors and can
be raised together. A separable closure of any residue field is available in Type u,
so the geometric-point test is not vacuous; larger fields add no different support
condition. Coefficient modules have the prescribed u+1 universe.

Independent H4 searches used different terms from the first report:

- LeanFinder via msearch: "sections of an etale sheaf whose support is proper over the
  base compose under pushforward". Eight hits about scheme section-map composition
  and ideal-sheaf maps; none states this theorem.
- Loogle via msearch: `"proper" "support"`. The service returned a query parser error;
  this gives no absence evidence.
- grep via msearch: `support.*proper|proper.*support|compactSupport`. The 25 hits
  concern function support, bump functions and topological compact support, not etale
  support pushforward.
- LeanSearch via msearch: "etale sheaf direct image with proper support composition
  base change". Service unavailable (Internal Server Error); no verdict inferred.
- Direct rg of Mathlib AlgebraicGeometry, upstream WeilConjectures and project
  lean/Sheaf for compact/proper support and shriek composition. I opened upstream
  LowerShriek/Defs.lean: `Etale.lowerShriek` requires `HasCompactification f` and is
  the chosen compactification composite, so it cannot replace this theorem for every
  separated locally finite type f. Existing open-immersion and derived comparisons
  likewise do not state the support characterization and all conclusions here.

H5-H9 and delivery audit: there is only one new theorem and its entire proof is sorry;
there are no data definitions, hidden proof helpers, local notation or private copies.
No new node, dependency module or statement correction is present, so H12/H13 and
correction-citer checks introduce no additional files to review. The module and theorem
have the source and exact blueprint id; the nine proof-docstring steps follow the node's
nine steps, including the proper-image support calculation, open specialization,
geometric-stalk comparison and mate pasting. All variables and universes are explicitly
bound. Every line is at most 100 characters. The recorded `lean.statement` was checked
by exact string comparison with the theorem signature and is identical.

Mismatches found: none. I left the Lean module and node unchanged and added this
independent reading only. Server validation via the required scompile.py completed
cleanly: ProperSupportSheafComposition.lean 1.8 seconds, nice 19, two threads, 60 seconds
per file; the script also refreshed EtaleSectionZeroOpen.lean in 1.4 seconds. No local
compiler or library build was run.
