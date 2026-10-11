## Worker report

The module `lean/Sheaf/AlgebraicGeometry/PerfectCutComplexDegreeZero.lean` states
`AlgebraicGeometry.exists_perfect_split_degree_zero`, with its sole theorem proof `by sorry`.
The auxiliary module defines `AlgebraicGeometry.degreeZeroFibreSurjective` in full;
no data or proof in this definition is postponed.

Hypothesis and conclusion correspondence:

- A scheme S is `(X : Scheme.{u})`. There are no restrictions on the scheme, its
  characteristic, separation, quasi-compactness, or Noetherianity.
- An object of D_QCoh(O_S) is `(K : schemeDerivedCategory X)` together with
  `(hKq : schemeDerivedQCohProperty X K)`. This is the full-subcategory property,
  for every integer cohomology sheaf, using the recorded definition.
- Perfectness is `(hKp : Scheme.IsPerfect X K)`, exactly the recorded predicate.
- Tor amplitude in [0,infinity) is `hKa`: for every O_X-module F and integer i < 0,
  `schemeDerivedTensorCohomologyVanishes X K F i`. There is no finite upper bound,
  restriction to quasi-coherent test modules, or extra bound imposed.
- The fixed point is `(s : X)`. The canonical map's surjectivity is
  `(hs : degreeZeroFibreSurjective X K s)`, realized by the new definition below.
- An open neighbourhood is `∃ U : X.Opens, s ∈ U ∧ ...`.
- P is an object of D(O_U): `∃ P : schemeDerivedCategory U.toScheme`.
- P is perfect: `Scheme.IsPerfect U.toScheme P`.
- P has Tor amplitude in [1,infinity): for every O_U-module F and integer i < 1,
  `schemeDerivedTensorCohomologyVanishes U.toScheme P F i`.
- The isomorphism is `Nonempty (... ≅ ... ⊞ P)`; the left side is derived exact
  restriction, first by `SheafOfModules.overFunctor`, then by the canonical
  `Scheme.Modules.overEquiv U`. The first summand is the same exact restriction
  applied to `(DerivedCategory.homologyFunctor _ 0).obj K`, embedded in degree zero
  by `DerivedCategory.singleFunctor _ 0`. Thus the right side is H^0(K)|_U ⊕ P
  in the derived category of modules on U, with no specified map or splitting added.
- All `HasDerivedCategory.{w}` binders specify the shared localization machinery
  on X, the localized sites, U, and the localized sites of U. They use Mathlib's
  own abelian instances. They impose no geometric hypothesis; the single common
  morphism universe is permitted to be large enough for all those localizations.
  Every variable and universe is explicitly bound (`autoImplicit false`).

Dependency declarations used, read in their source files:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Opens`,
  and `Scheme.Hom`. Its `local_affine` clause is the scheme definition.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` and
  `schemeDerivedQCohProperty`; the latter asks for quasi-coherence of every H^n.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`; local isomorphism
  to a strictly perfect module-sheaf complex, using exact over-site restriction.
- `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`:
  `schemeDerivedTensorCohomologyVanishes`, with K-flat representative and total tensor.
  This existing landed definition node is added to the item's statement dependencies.
- In the new definition, `Sheaf.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`; `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlat`; `Mathlib.AlgebraicGeometry.ResidueField`:
  `Scheme.residueField` and `Scheme.residue`. The latter is the quotient of the
  stalk local ring by its maximal ideal. `ModuleCat.extendScalars` is Mathlib's
  left-sided tensor extension, equivalent by tensor symmetry to the node's convention.
- Structural operations are Mathlib's `DerivedCategory.Q`, `homologyFunctor`,
  `singleFunctor`, `mapDerivedCategory`, cycles, cycle inclusion and homology-class
  map. `Equivalence.functor` is explicitly typed with the shared module categories
  to avoid introducing the separate category instance on `Scheme.Modules`.

The new definition's mathematical reading: choose a K-flat P representing K. Its
stalk complex C computes K_s and its scalar-extended complex D computes the derived
residue fibre (Stacks 06YB). The map alpha is constrained by its composite with
D.iCycles, so it is the unique canonical cycle map, not an arbitrary map. Requiring
`Epi (alpha ≫ D.homologyπ 0)` means surjectivity on residue-field modules. Since
C.cycles 0 → C.homology 0 is epi and scalar extension preserves epis, its image is
exactly the image of H^0(C) ⊗ κ(s) → H^0(D). Stalks preserve homology. Thus the
predicate expresses each side and the surjectivity of the map in the item. K-flat
replacement exists, so existential choice of P adds no hypothesis; the predicate
is invariant under the resulting canonical isomorphisms.

Edge cases checked before writing: the empty scheme has no s, so the pointed
statement is vacuous for the correct reason; K = 0 permits U = top and P = 0;
a complex concentrated in degree zero which meets the perfect/nonnegative
Tor hypotheses splits with P = 0; if H^0(K) = 0, surjectivity forces H^0 of the
residue fibre to vanish, yielding a positive-amplitude summand. The cutoff
`i < 1` includes degree zero and all negative degrees. Arbitrary positive
characteristic and arbitrary non-Noetherian schemes remain allowed. No independent
test-module universe can make the Tor tests vacuous: the module carrier is the
same `. {u}` as the recorded derived category (written without the space in Lean).

Sources read: the full statement and proof of Stacks Tag 0A1U at
https://stacks.math.columbia.edu/tag/0A1U (the local literature file is absent).
Its i = 0 splitting and positive perfect truncation give the local conclusion;
the item's nonnegative Tor hypothesis identifies the other truncation with H^0.
The node's three proof steps are reproduced in the theorem docstring.

Searches for the item: msearch leanfinder, query "perfect complex splitting degree
zero surjective residue field cohomology map", returned eight splitting/projective
or Hom-complex surjectivity results, none the scheme-level assertion. msearch loogle
"DerivedCategory, truncLE" returned zero hits (unknown identifier truncLE).
msearch grep "perfect.*split|split.*perfect|TorAmplitude" in AlgebraicGeometry
returned zero hits. rg over WeilConjectures finds tensor/Tor theory for étale
coefficients and finite-free semicontinuity, not this scheme-module splitting;
rg of the item id in WeilConjectures finds no result. rg over lean/Sheaf finds the
recorded tensor-vanishing definition and perfectness, but no existing assertion.
The declaration names were also checked against dag/lean_names_upstream.json,
WeilConjectures, and lean/Sheaf: no collision.

Validation: scompile of both modules together, in dependency order, compiled
cleanly on the server (4.4 seconds), with no errors or warnings. The two modules
use distinct explicit universe names so the combined compilation is valid.
No statement correction or disputed statement is needed.

## New nodes

`def-sc-degree-zero-fibre-surjective` defines exactly the surjectivity predicate
for the canonical map from degree-zero cohomology tensor the residue field to
the degree-zero cohomology of the derived residue fibre. Source: Stacks 0A1U,
i = 0 hypothesis, interpreted at a scheme stalk using 06YB. Its own module is
`Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective`. The complete definition uses
K-flat representatives, the recorded stalk functor, Mathlib scalar extension and
cycles, with an existentially specified unique canonical cycle map. There is no
hollow definition or named theorem in this module. Its dependencies are the
existing scheme, derived category, K-flat, stalk-functor, and residue-field nodes.

Searches: msearch leansearch "surjective cohomology base change map residue field
perfect complex" was unavailable (Internal Server Error); leanfinder "surjectivity
cohomology residue field base change map cycles" returned eight unrelated
surjectivity lemmas (the names are in mathlib_searches); grep
"residue.*homology|homology.*residue|fibre.*surject" found only three unrelated
Condensed/Light/Sequence hits. Source and Sheaf rg found strict-henselian étale
cohomology, minimal-free models and semicontinuity, no such definition. DAG searches
found the item and the affine cut statement, not a definition of the predicate;
`blueprint_refs.py search 'degree-zero fibre'` returned zero matching blueprint
nodes. It is therefore a new definition, rather than a private copy of one already
recorded. Its blueprint ancestry is thm-sc-theorem-of-cube. The via path is this item,
lem-sc-perfect-degree-zero-fibre-criterion, lem-sc-proper-flat-global-sections-criterion,
lem-sc-proper-flat-global-sections, and lem-sc-general-theorem-of-cube.

## Second reading by M1

I independently read the item node, both delivered modules, all seven recorded
notion dependencies and their declarations, and the Stacks TeX source. Local
literature is absent on this machine: the original more-algebra.tex,
cohomology.tex and sites-cohomology.tex were fetched from the Stacks repository
into this item's scratchpad. In particular I read the complete statement and
proof of `lemma-better-cut-complex-in-two` (0A1U),
`lemma-check-K-flat-stalks` (06YB), and `lemma-K-flat-resolution` (06YS).
0A1U assumes a ring, a prime and pseudo-coherence, not Noetherianity or a
characteristic condition. The node is its scheme-local specialization at i=0,
with perfectness and nonnegative Tor amplitude already explicitly in the node;
these identify the nonpositive truncation with H^0. No correction is necessary.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

- Arbitrary scheme S: `X : Scheme.{u}`. Mathlib's locally affine locally ringed
  space is the recorded `def-pc-scheme`. PASS; no base field, finiteness,
  separation or Noetherian instances.
- K in D_QCoh(O_S): `K : schemeDerivedCategory X` and
  `hKq : schemeDerivedQCohProperty X K`. I opened DerivedCategory.lean:
  the property quantifies quasi-coherence of every integer cohomology sheaf.
  PASS; this is membership in the full subcategory, not a different category.
- K perfect: `hKp : Scheme.IsPerfect X K`. I opened PerfectComplex.lean:
  each point has a neighbourhood on whose over-site the exact restriction is
  isomorphic to a bounded complex of summands of finite free module sheaves.
  PASS; the node's recorded notion, not an unrelated finiteness condition.
- Tor amplitude [0,infinity): `hKa` quantifies every sheaf of modules F and
  every `i : ℤ` with `i < 0`, requiring the recorded
  `schemeDerivedTensorCohomologyVanishes X K F i`. Its definition uses the
  total tensor with F[0] of an existing K-flat representative. PASS; no
  finite upper bound and no restriction of the test sheaves to QCoh.
- Fixed point: `s : X`. PASS, introduced after K and its hypotheses.
- Surjectivity of the canonical degree-zero residue map:
  `hs : degreeZeroFibreSurjective X K s`. The new definition uses the
  recorded `RingedSpace.moduleStalkFunctor`, `CochainComplex.IsKFlat`,
  `DerivedCategory.Q`, Mathlib's stalk residue quotient `X.residue s` and
  `ModuleCat.extendScalars`. PASS, with the canonical-map check below.
- Open neighbourhood: `∃ U : X.Opens, s ∈ U ∧ ...`. PASS; no affineness
  or smaller prescribed neighbourhood is demanded by the conclusion.
- Summand P in D(O_U): `∃ P : schemeDerivedCategory U.toScheme`. PASS.
- P perfect: `Scheme.IsPerfect U.toScheme P`. PASS, same notion as for K.
- P has Tor amplitude [1,infinity): every module sheaf F on U and every
  integer `i < 1` satisfies the same recorded tensor-vanishing predicate.
  PASS; degree zero is included, and no extra upper bound is introduced.
- Isomorphism K|_U = H^0(K)|_U direct-sum P: `Nonempty (... ≅ ... ⊞ P)`.
  I opened Mathlib's `Scheme.Modules.overEquiv`: its functor identifies
  modules on the over-site with modules on the open subscheme. The left
  side applies its composite with `SheafOfModules.overFunctor` through
  `mapDerivedCategory` to K. The right side applies the identical exact
  composite to `(DerivedCategory.homologyFunctor _ 0).obj K` and places
  the result in degree zero with `DerivedCategory.singleFunctor _ 0`.
  PASS; both summands lie in the same derived category, with the shared
  Mathlib category and abelian structures; no chosen map or canonical
  splitting is additionally required by the node.
- Localization infrastructure: the four `HasDerivedCategory.{w}` families
  supply X, X's over-sites, its open subschemes and their over-sites, as
  required by the dependency signatures. PASS; no geometric assumption,
  alternate Abelian instance, unbound variable or independent test-module
  universe. u and w are explicitly declared; w may be enlarged jointly.

New-node reading (H12): `def-sc-degree-zero-fibre-surjective` is a definition
node of exactly the i=0 map condition in 0A1U. Its own TeX introduces X, K, s,
the residue field and the equivalent K-flat/cycle description; all cited
notions are in its stmt_deps with usable recorded declarations. I read those
signatures, including the stalk module action and quotient residue map. The
module defines data fully, with no sorry or auxiliary theorem. In particular,
alpha is constrained by `α ≫ D.iCycles 0 = F.map (C.iCycles 0)`.
The cycle inclusion is mono, so this determines alpha uniquely; its existence
follows from the complex differential equation. The composite to H^0(D)
kills F of the boundaries and therefore factors through F(H^0(C)). Since
C.cycles 0 -> C.homology 0 is epi and F is right exact, that factor is
surjective exactly when the displayed composite is epi. ModuleCat epis are
surjective. Exact stalks identify H^0(C) with H^0(K)_s; 06YB makes the stalk
representative K-flat, and 06YS guarantees representatives exist. Thus the
existential representative neither strengthens nor weakens the condition.
The existential isomorphism to K introduces no arbitrary cohomology map:
surjectivity is invariant under its induced natural identifications.
The new node has the required source, creation, chapter/unit, ancestry,
empty proof, null mathlib_match and none audit fields. There are no delivered
dependency modules to review (H13). The existing tensor-vanishing node is
added as a landed dependency, permitted by STATE's STMT_DEPS MAY GAIN LANDED
NODES rule; it is not duplicated.

Edge cases: on the empty scheme no s exists, exactly as in the node. For K=0
both the fibre condition and the splitting permit P=0 and U=top. For a
perfect nonnegative-amplitude complex concentrated in degree zero, P=0 is
permitted. H^0(K)=0 imposes vanishing of the degree-zero derived residue
fibre, as it should. The cutoff 1 excludes all i<=0, while the input cutoff
0 excludes only negative i; n=0 is not accidentally omitted. No index-set
or rank binder excludes empty families. No characteristic or nonzero-base
ring hypothesis appears. Sheaf and module carriers share u, so Tor testing
cannot become vacuous by placing test modules in an unrelated smaller
universe; the localization hom universe w is independent and explicit.

Independent searches, with different queries from the worker:

- msearch leanfinder: `local direct sum decomposition of a perfect complex
  when cohomology base change is onto`. Eight hits: K-projectivity,
  cm5b factorization and derived fraction/single-functor results. None states
  this scheme-local perfect splitting or defines its fibre-map predicate.
- msearch loogle: `"homology", "surjective"`. Two hits:
  CochainComplex.HomComplex.CohomologyClass.mk_surjective and
  groupHomology.chains₁ToCoinvariantsKer_surjective. Neither is this map.
- msearch leansearch: `canonical map from cohomology tensor residue field
  to derived fibre cohomology is surjective`. Internal Server Error;
  unavailable, not evidence for absence.
- rg of Mathlib, WeilConjectures and lean/Sheaf for residue with cycles or
  homology, perfect with decomposition or splitting, and fibre/fiber
  surjectivity. Only unrelated perfect-field/topological/Lie results,
  etale projective-line residue comparison, semicontinuity and minimal-free
  models; no duplicate definition or theorem. Exact-name and item-id search
  of WeilConjectures and dag/lean_names_upstream.json found no collision.
- DAG search for `fibre map`, `fiber map`, and `degree-zero fibre` found
  the item, its affine cut proof dependency and its criterion citer;
  no existing definition of this predicate. The affine cut statement is
  over a ring, so it cannot be recorded as this scheme assertion.

H5/H6/H8/H9: no hollow definitions and nothing proved; the sole theorem
has `by sorry`. Both modules and both declarations cite their source and
own blueprint id. The theorem docstring reproduces all three node proof
steps and their dependencies in order. The signature in lean.statement
matches the file verbatim. No mathematical or Lean mismatch found; I left
both modules and node copies unchanged and added this independent reading.
Validation: scompile of both modules together in dependency order returned
exit code 0, compiled in 4.3 seconds, with no errors or warnings.

## Reviewer fix (R-pcz1520)

`degreeZeroFibreSurjective` hand-built the canonical map `H⁰(C) ⊗ κ(s) → H⁰(κ(s) ⊗ C)` from
cycles and three `let`s, a second construction of the map J1 landed today as
`ModuleCat.cohomologyBaseChange` (def-pc-module-cohomology-base-change, de3865f66), the form the
ring-level sibling lem-pc-affine-perfect-cut-degree-zero uses. The definition now requires
`Epi (ModuleCat.cohomologyBaseChange (B := IsLocalRing.ResidueField (X.presheaf.stalk s)) C 0)`
for the stalk complex `C` of a K-flat representative, with the terms written out (no `let`);
κ(s) is the STATE RESIDUE FIELD form (`rfl` to `X.residueField s`). The node statement follows;
it names def-pc-module-cohomology-base-change in words, since that node landed after this
delivery's base and the merge tool admits only base nodes in stmt_deps (lead: add it).
The item theorem is unchanged.
