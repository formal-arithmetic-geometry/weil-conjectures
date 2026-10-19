## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveNoetherianPerfectBaseChange` states
`AlgebraicGeometry.projectiveNoetherian_perfect_baseChange` with proof `sorry`.
The node statement is unchanged. No new definitions or nodes are needed.

Hypothesis and clause correspondence:

- Schemes X, S, T: `{X S T : Scheme.{u}}`, with an explicit universe u.
- S locally Noetherian: `[IsLocallyNoetherian S]`; there is no such hypothesis on T.
- The projective morphism f: `(f : X ⟶ S) [IsProjective f]`, using the recorded
  H-projective plus quasi-compact convention, not a new predicate.
- The coherent O_X-module G: `(G : X.Modules)` and
  `(hG : RingedSpace.IsCoherent X.toRingedSpace G)`.
- Flatness over S: `(hflat : Scheme.Modules.IsFlatOver G f)`.
- Arbitrary base change g: `(g : T ⟶ S)`, with no flatness, finiteness, or
  Noetherian restriction on g or T.
- X_T is the chosen categorical `pullback f g`; p is `pullback.fst f g` and f_T
  is `pullback.snd f g`. G_T is `(Scheme.Modules.tensorPullback p).obj G`.
- Modules enter the derived category through `DerivedCategory.singleFunctor ... 0`.
  The left endpoint is `derivedPullback g` applied to `schemeDerivedDirectImage f`
  of G in degree zero. The right endpoint is `schemeDerivedDirectImage f_T`
  applied to G_T in degree zero.
- Both endpoints are perfect: the first and second conjuncts are `Scheme.IsPerfect T`
  of those exact endpoints, independently of a choice of comparison morphism.
- The canonical comparison is invertible: the final conjunct universally quantifies
  a morphism φ with those endpoints and asserts
  `IsDerivedModuleBaseChangeMap f g G φ → IsIso φ`. This uses the existing
  characterisation of the canonical comparison; it does not replace canonical-map
  invertibility with existence of an unspecified isomorphism.
- The family of `HasDerivedCategory` instances chooses localizations at a common
  explicit universe w. Localized instances over T type the recorded perfectness
  predicate. The additive tensor-pullback instance types the canonical comparison;
  tensor pullback is a left adjoint, so this is structural data, not an extra
  geometric condition. These binders follow the existing canonical base-change
  statements in `PerfectDirectImageBaseChange.lean`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its docstring fixes the chosen
  pullback, projections and tensor module pullback. `Scheme.Modules.moduleBaseChange`
  is the further base change between bases over S, not the initial pullback here.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective` (extends `IsHProjective` and `QuasiCompact`).
  The extracted upstream module is absent from the older local source checkout;
  its original declaration was read in `Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`.
  The server resolves the recorded canonical upstream import successfully.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap`:
  `AlgebraicGeometry.IsDerivedModuleBaseChangeMap`, whose full definition pins φ to
  the derived square comparison followed by the derived-to-ordinary pullback counit.
- `def-pc-morphism-conventions` is a convention node with no declaration of its own.

All stated proof-dependency modules are imported without `public` when used only
for the future proof: ProjectiveSpace, ZariskisMainTheorem, Morphisms.Proper,
QuasicoherentFiniteTypeAffine, RelativelyFlatDerivedBaseChange,
FlatComplexDerivedPullback, and LocalizedPullbackPerfectModel. The proof dependency
`lem-pc-projective-noetherian-rf-perfect` has no Lean record in the supplied DAG,
so has no import to add yet. Its step remains fully documented in the theorem.
The relatively-flat base-change lemma currently records an unspecified isomorphism;
stage 3 must identify the canonical map as described in its proof, or apply the
already existing canonical-map theorem. This does not affect this statement's typing.

Edge cases checked before writing: G = 0 gives zero endpoints; the empty X and
empty T give the corresponding zero derived objects and vacuous local perfectness;
g = identity gives the expected comparison with Rf_*G. Nothing excludes a
non-quasi-compact locally Noetherian S or a non-Noetherian T. The strictly-perfect
model definition allows rank-zero summands and zero complexes. No finite cover of
T, bounds uniform across T, or affine hypotheses have been added. All variables and
both universes are explicitly bound; no let or hidden local notation occurs.

Searches:

- msearch.py, leanfinder: "derived direct image coherent relatively flat sheaf
  projective locally Noetherian arbitrary base change perfect" returned eight hits
  about flat scheme morphisms and inverse image, no exact theorem.
- msearch.py, loogle: "AlgebraicGeometry.IsProjective" returned zero hits and
  "unknown identifier" (project-defined notion, unavailable in that search index).
- msearch.py, grep: "perfect.*base.change|base.change.*perfect" in
  Mathlib/AlgebraicGeometry returned zero hits.
- rg in the source WeilConjectures tree for the item id and perfect/base-change
  patterns found no exact declaration. The upstream-name index associates the item
  with `Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange_of_isClosedImmersion`
  from the old source snapshot; that declaration/file is not in the local source
  checkout, and its Cech-model closed-immersion formulation is not this statement.
- rg in lean/Sheaf found `perfect_derivedDirectImage_baseChange` in
  `PerfectDirectImageBaseChange.lean`. Its full signature requires a proper morphism
  of finite presentation and a finitely presented module, and concludes perfectness
  before pullback and canonical-map invertibility. It does not state this node's
  coherent/projective/locally-Noetherian hypotheses or both pulled-back perfectness
  conclusions, so is not an exact existing statement.
- rg for the new declaration name across Mathlib, upstream, and lean/Sheaf found
  no collision.

Source checked: the entire node, its three proof steps and dependency records, and
its blueprint corollary file including proof. There is no statement correction or
STATEMENT-DISPUTED flag. Server scompile.py compiled the delivered module cleanly
(2.5 seconds, nice 19, two threads, 60-second limit).

## Second reading by NO

Read independently with the node JSON, blueprint source (order 674, statement and
entire proof), and delivered Lean open. Verdict: the statement is exact; no
mathematical or Lean repair is needed. The sole change is this second-reading report.
No statement_change, new definition node, dependency module, or disputed statement
is present or required.

Object, hypothesis, and conclusion checklist, in the order of the natural statement:

- Base S is a scheme, locally Noetherian: `{X S T : Scheme.{u}}` and
  `[IsLocallyNoetherian S]`. Exact. Read Mathlib Noetherian.lean: the class requires
  Noetherian rings on all affine opens, equivalent to the node's affine-cover form.
  There is no global quasi-compactness condition on S.
- X and projective f: `(f : X ⟶ S) [IsProjective f]`. Exact. Read the recorded
  projective dependency and the source declaration in
  `lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`: IsHProjective uses
  an existential natural n and a closed immersion into projective n-space, and
  IsProjective adds QuasiCompact. Stacks morphisms.tex, definition-projective
  (01W8), distinguishes H-projective from projective-bundle projective; the node
  explicitly fixes the former convention plus quasi-compactness, as does this Lean.
- Coherent O_X-module G: `(G : X.Modules)` and
  `(hG : RingedSpace.IsCoherent X.toRingedSpace G)`. Exact. Opened Coherent.lean:
  finite type and finite-type kernels for every map from finite free modules on
  every open. It is the same SheafOfModules carrier as the derived-category nodes.
  Quasi-coherence follows from local finite presentation; it need not be an
  additional hypothesis.
- Flat over S: `(hflat : Scheme.Modules.IsFlatOver G f)`. Exact. Read the full
  definition at upstream DirectImage/Basic.lean: affine U,V and f(U) contained in V,
  with Module.Flat after restriction along f.appLE. Read Stacks morphisms.tex,
  definition-flat and lemma-flat-module-characterize (01U3/01U4): this is equivalent
  to relative stalk flatness for quasi-coherent G. This does not assume f flat.
- Every scheme T and arbitrary g: `(g : T ⟶ S)`, with T among the scheme binders.
  Exact. No Noetherian, flatness, separatedness, or finite-presentation assumption
  on T or g occurs.
- Cartesian scheme and projections: `pullback f g`, `pullback.fst f g` to X and
  `pullback.snd f g` to T. Exact. Read BaseChangeConventions.lean and its recorded
  node; the projection names agree with the present corollary's p and f_T.
- G_T is ordinary p^*G: `(Scheme.Modules.tensorPullback
  (pullback.fst f g)).obj G`, embedded by `DerivedCategory.singleFunctor ... 0`.
  Exact. It is not derived pullback of G on the right-hand side.
- Left endpoint Lg^*(Rf_*G): `(derivedPullback g).obj
  ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor ... 0).obj G))`.
  Exact. Opened DerivedPullback.lean, SchemeDerivedDirectImage.lean and
  DerivedCategory.lean: these are the recorded unbounded derived functors and
  localization of all module sheaves, with G in degree zero, not D(QCoh).
- Right endpoint Rf_T,*G_T: `(schemeDerivedDirectImage (pullback.snd f g)).obj`
  applied to the degree-zero embedding of the ordinary pullback above. Exact.
- Canonical-map invertibility: `∀ φ : <left> ⟶ <right>,
  IsDerivedModuleBaseChangeMap f g G φ → IsIso φ`. Exact in the recorded relational
  encoding. Opened DerivedModuleBaseChangeMap.lean: φ is the derived square map
  followed by Rf_T,* of the derived-to-ordinary counit at G. Its existential counit
  witnesses a left-derived universal property, not an arbitrary map. Thus this
  clause concerns every representative of the canonical comparison; it does not
  replace it by existence of an unrelated isomorphism.
- Both sides perfect: the first two conjuncts are `Scheme.IsPerfect T` of the
  respective displayed endpoints. Exact, separately asserted even before choosing
  φ. Opened PerfectComplex.lean: perfect means every point has a neighbourhood with
  a strictly perfect representative, bounded with terms retracts of finite free
  modules; it does not impose uniform bounds or a finite covering.
- Structural binders: the family of HasDerivedCategory at common w supplies the
  existing localization models; the open-site family on T types IsPerfect. Read
  their signatures, rather than substituting HasDerivedCategory X.Modules (which
  uses a different category instance). These are model choices, not geometric
  restrictions. The Additive tensor-pullback binder is justified by its recorded
  left-adjoint property (also explicitly used in exists_derivedPullback), and
  likewise imposes no geometric condition. All schemes may be placed in a common
  arbitrary u; w remains arbitrary subject to localization existence, including
  the standard sufficiently large localization universe. There is no small-universe
  test-object quantifier that could make a geometric hypothesis vacuous.

Source cross-check: the corollary cites the blueprint itself, not a standalone
Stacks corollary. Read its full source file; it has precisely these hypotheses.
Also read Stacks perfect.tex, lemma-flat-proper-perfect-direct-image-general
(0B91), including clause (2) and proof, and lemma-base-change-tensor-perfect.
The latter inputs assume finite presentation and proper support, as implied here
locally over a locally Noetherian base; neither requires the new base Noetherian.
No ambient field, characteristic, or nonemptiness assumption is being inherited.

Edge cases: zero G and empty X are allowed and produce zero derived endpoints.
For empty T, perfectness is pointwise vacuous and the comparison is between zero
objects. Empty S forces X,T empty and remains covered. Projective dimension n = 0
is permitted by the natural-number witness in IsHProjective. Identity g is allowed;
nonflat g and non-Noetherian T are allowed. No index set is constrained to be
nonempty (the local definition of perfectness handles the empty cover of an empty
scheme). All characteristics and arbitrary universe sizes u are included.

Independent searches, using different wording from the first worker:

- msearch leanfinder: "cohomology base change coherent flat projective morphism
  perfect complexes": eight hits about flat base change and K-projectivity,
  no exact theorem.
- msearch loogle: "AlgebraicGeometry.Scheme.Modules.IsFlatOver": unknown identifier
  in the index (unavailable, not positive evidence of absence).
- msearch grep: "coherent.*flat|flat.*coherent": no hits.
- Direct rg on Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf for perfect/base-change patterns and the delivered declaration name.
  Read `perfect_derivedDirectImage_baseChange` in PerfectDirectImageBaseChange.lean:
  proper finite-presentation/finitely-presented-module hypotheses and perfectness
  before pullback, so it is a different theorem. Read upstream
  `exists_isFiniteFreeComplex_higherDirectImage` in FiniteFreeComplex.lean: it
  compares individual cohomologies by unspecified isomorphisms, not the canonical
  derived map. Neither is an exact existing declaration for this node. The audited
  old Cech-model name is absent from this source checkout and is a closed-immersion
  model formulation. No new definition or name collision was found.

H5/H6/H8/H9: the delivered file defines no data and states one named theorem with
proof exactly `sorry`. Its module and theorem docstrings cite the source and item.
The theorem docstring follows all three DAG proof steps (proper/separated and
coherent-to-quasi-coherent reduction; perfectness before pullback; bounded flat
local models and preservation of finite-projective splittings). The unstated
projective-perfectness proof dependency has no Lean module to import; the remaining
stated proof dependencies are present as proof imports. No local notation, private
copy, hidden let/show binder, or unbound variable/universe is present. Checked the
recorded lean.statement verbatim against the full signature and every line <= 100.

Validation: scompile.py independently compiled the only delivered module cleanly
on the server in 2.5 seconds, nice 19, two threads, 60 seconds per file. No warning
or error was printed. No mismatches were found; Lean and node are unchanged.
