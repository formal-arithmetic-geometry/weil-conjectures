## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleBaseChangeOpenClosed` states
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isOpenImmersion_of_isClosedImmersion`.
Its sole theorem has proof `by sorry`; no new definition or auxiliary theorem is introduced.
The node copy changes only `lean`.

The blueprint source was read on the project server at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-base-change-open-closed.md`.
Its statement agrees verbatim with the DAG statement. The theorem docstring carries all five
expanded DAG proof steps, including why the specified exchange is the identity under the
inside stalk comparisons and why complementary-open refinement annihilates outside germs.

Hypothesis and conclusion correspondence:

- Schemes and the four arrows in the displayed square are
  `{U' U Y X : Scheme.{u}} (p : U' ⟶ U) (h : U' ⟶ Y) (j : U ⟶ X) (g : Y ⟶ X)`.
- “Both an open and a closed immersion” is exactly `[IsOpenImmersion j] [IsClosedImmersion j]`.
  These are the recorded Mathlib definitions, with no properness, finiteness, separation,
  torsion, or étaleness assumption on `g`.
- The cartesian square is `sq : ChosenCartesianSquare p h j g`. Its chosen isomorphism
  `U' ≅ pullback j g` respects the projections. This represents the displayed fibre product
  `Y ×_X U` up to its canonical factor-swap identification; `p` goes to `U`, and `h` to `Y`.
  An arbitrary model with that identification includes the displayed pullback itself.
  This is the node's recorded cartesian-square notion, not an additional hypothesis on it.
- “Every abelian sheaf F on U_Et” is the unrestricted binder
  `(F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`, using the project's coefficient
  size convention.
- The actual map `g⁻¹ j_* F → h_* p⁻¹ F` is
  `(baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F`. The square orientation agrees
  with `baseChangeMap`'s source `j_* ⋙ g^*` and target `p^* ⋙ h_*`.
- “Is an isomorphism” is precisely `IsIso` of that morphism, not an existence of some
  isomorphism between its source and target.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`, `hom_fst`, `hom_snd`,
  and inherited `toCommSq`.
- `WeilConjectures.SixFunctors.BaseChange.Square` (publicly imported by the preceding module):
  `AlgebraicGeometry.Etale.baseChangeMap` and its docstring and adjoint/counit formula.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (transitive public import):
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, and `upperStarLowerStarAdjunction`.
  These define the functors in the actual exchange; there is no replacement canonical map.
- `Mathlib.AlgebraicGeometry.OpenImmersion` (transitive public import):
  `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Sites.Sheaf` and `Mathlib.AlgebraicGeometry.Sites.Etale`
  (transitive public imports): `CategoryTheory.Sheaf` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `Mathlib.Algebra.Category.Grp.Abelian` supplies the abelian coefficient category.

Proof-only imports include the recorded modules `Sheaf.Paper.InverseImageStalkGerm` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. Other recorded proof dependencies
are already transitively imported: open-immersion base-change stability and étaleness,
small étale sites, geometric stalks, and the direct/inverse image and exchange definitions.
`lem-kun-open-immersion-restriction` has no recorded Lean declaration in the supplied DAG;
it is a proof-only prerequisite, not needed to type this statement. It is cited in the
proof docstring and no import for its nonexistent recorded module is invented.

Edge cases checked mathematically before writing:

- Empty `U`: the direct image and both exchange stalks are zero; the unrestricted scheme
  binders allow this case.
- Empty `Y` (and hence empty `U'`): stalk conservativity is vacuous and the exchange is
  invertible; no nonemptiness hypothesis occurs.
- Identity `j`, or any isomorphism `j`: only the inside case remains and exchange is
  canonically invertible. The statement does not exclude these immersion instances.
- Zero sheaf: exchange is the unique map between zero sheaves.
- Disconnected schemes and a union of clopen components: the two stalk cases apply
  independently on every component. No connectedness or quasi-compactness is assumed.
- Arbitrary characteristic and arbitrary `g`: no finite coefficient or torsion hypothesis
  is used in this underived clopen argument.

Searches made with the prescribed launcher wrapper:

- LeanFinder: `For an open and closed immersion of schemes the canonical underived base
  change map for every abelian etale sheaf is an isomorphism`. Eight hits: étale
  base-change stability, open-immersion scheme-module restriction/pullback comparisons,
  ringed-space pullback projections, and different module pullback comparisons. None has
  this abelian small-étale exchange statement.
- Loogle: `"baseChangeMap", "IsIso"`. Zero hits.
- Mathlib grep in `CategoryTheory/Sites`:
  `baseChangeMap.*[Oo]pen|baseChangeMap.*[Cc]losed|isIso.*[Bb]ase[Cc]hange`. Zero hits.
- LeanSearch: `Base change for direct image of abelian etale sheaves along an open and
  closed immersion`. Service unavailable with Internal Server Error. No absence
  conclusion is drawn from that service.
- Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf`:
  `underivedExchange|underived.*[Ee]xchange|baseChange.*open|baseChange.*closed`;
  inspected the existing exchange definition and proper/finite/open-extension comparisons.
  These do not state this result with both immersion hypotheses and arbitrary abelian F.
- Direct `rg` in those trees and `dag/lean_names_upstream.json`:
  `lem-kun-base-change-open-closed|isIso_baseChangeMap.*[Oo]pen|isIso_baseChangeMap.*[Cc]losed`.
  No exact match.
- Direct `rg` in Mathlib, upstream, the side library and the upstream name inventory for
  the proposed full theorem basename: zero hits, so its name is fresh.

Validation: the prescribed `scompile.py Q08 lem-kun-base-change-open-closed` compiled both
sandbox and library-path forms of the sole delivered file cleanly (4.1 s and 3.8 s), with
no errors or warnings. Every variable and the sole universe `u` is explicitly bound.
No statement dispute, statement correction, missing statement dependency, new node, or
dependency repair was needed. The second reader supplies the independent reading.

## Second reading by Q08

I independently read the sandbox node and Lean file, all seven statement-dependency
nodes and the declarations implementing them, and the recorded proof dependencies.
I read the original blueprint node on the server at its recorded source path (the
literature files are absent from this local mirror). Its statement agrees with the
node verbatim. I also read the unit's `_section.md` and the cited Stacks `.tex` source
places: schemes 01HE, 01HK, 01IO and 01JY; etale-cohomology 03PY, 03Q1, 04FX,
03PU and 0F70. These places assume arbitrary schemes and the stated immersion;
there is no ambient field, Noetherian, finite-type, torsion or invertibility condition
for this lemma. The unit's separate Kunneth hypotheses are not hypotheses of this
standalone clopen lemma.

Object, hypothesis and conclusion inventory, matched item by item:

1. Schemes `U`, `X`, `Y` and `U' = Y ×_X U`: `{U' U Y X : Scheme.{u}}`.
   Verdict: exact, with `U'` an arbitrary chosen model of the fibre product.
2. Morphism `j : U → X`: `(j : U ⟶ X)`. Both required hypotheses are present,
   `[IsOpenImmersion j] [IsClosedImmersion j]`. Verdict: exact. I opened
   Mathlib's `IsOpenImmersion` (the underlying locally ringed space open immersion)
   and `IsClosedImmersion` (closed embedding and surjective stalk maps).
   These are the recorded scheme immersion notions, not just assertions about the
   topological image. The locally-generated-kernel condition in Stacks' general
   locally ringed space definition imposes no extra condition here: for an open
   immersion the kernel is locally zero on the image and the whole structure sheaf
   on its open complement.
3. Arbitrary morphism `g : Y → X`: `(g : Y ⟶ X)`, with no instance on `g`.
   Verdict: exact; no etaleness, separation, properness or finiteness restriction.
4. Cartesian square with projection `p : U' → U` and `h : U' → Y`:
   `(p : U' ⟶ U) (h : U' ⟶ Y)` and
   `(sq : ChosenCartesianSquare p h j g)`. Verdict: exact. I read the full
   dependency structure in `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
   `isoPullback : U' ≅ pullback j g`, `hom_fst` identifies `p`, `hom_snd`
   identifies `h`, and inherited `CommSq` supplies `p ≫ j = h ≫ g`.
   The factor order `U ×_X Y` differs from the displayed `Y ×_X U` only by
   the canonical swap; arbitrary chosen models include the displayed square.
   This binder supplies the recorded Cartesian data rather than strengthening it.
5. Every abelian sheaf on the small etale site of `U`:
   `(F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   Verdict: exact. I opened Mathlib's `Sheaf` (the full subcategory of presheaves
   satisfying the sheaf condition), `smallEtaleTopology` and its jointly-surjective
   covering characterization. There is no constructibility or torsion condition.
6. The specified exchange `g⁻¹ j_* F → h_* p⁻¹ F`:
   `(baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F`.
   Verdict: exact. I opened `Etale.lowerStar`, `upperStar` and
   `upperStarLowerStarAdjunction` in the recorded upstream `UpperLowerStar.Defs`:
   direct image is precomposition with etale base change and inverse image is its
   sheafified left Kan extension left adjoint. In `BaseChange.Square`, the
   `baseChangeMap` signature is `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`; substituting
   `(g', f', f, g) = (p, h, j, g)` gives exactly the required source and target.
   Its mate definition and `upperStar_map_baseChangeMap_app_counit` give the
   specified square comparison followed by the pulled-back counit, as the node
   requires. No arbitrary morphism or unrelated isomorphism replaces this map.
7. Conclusion: `IsIso` of that component. Verdict: exact, for every `F` after
   fixing the square. The theorem does not assert a stronger derived comparison.

Edge cases: all four scheme binders admit empty schemes. If `U` is empty both
sides have zero stalks; if `Y` is empty there are no geometric points and
conservativity applies vacuously. If `X` is empty the available arrows force
`U` and `Y` empty too. The identity immersion, an isomorphic model of it, and
arbitrary unions of clopen components are admitted. The zero abelian sheaf is
admitted. No index set, cohomological degree or integer `n` is introduced, so
there is no empty-index or degree-zero restriction hidden in a binder. There is
no characteristic restriction. The arbitrary universe `u` and coefficient size
`u + 1` match the recorded abelian-etale-sheaf convention and the upstream
functors; no additional universe equality or implicit size instance is assumed.

Independent searches (queries differ from the first worker's):

- Launcher LeanFinder: `Beck Chevalley exchange for pushforward from a clopen
  subscheme is invertible on abelian small etale sheaves`. Eight hits, primarily
  scheme-module restriction/pullback adjunctions and topological sheaf functors;
  none states this small-etale abelian exchange result.
- Launcher Loogle: `"baseChangeMap", "Immersion"`. No hits.
- Launcher grep: `clopen|Beck.Chevalley` in `CategoryTheory/Sites`. No hits.
- Launcher LeanSearch: `The canonical exchange for direct image from a clopen
  subscheme and inverse image by any scheme morphism is invertible on abelian
  etale sheaves`. Internal Server Error; recorded as unavailable, with no absence
  inference from it.
- Direct `rg` on the upstream and project Lean trees searched clopen, Beck-Chevalley,
  immersion and exchange/base-change combinations. I opened the closest upstream
  declarations: `isIso_baseChangeMap_of_isFinite` requires `[IsFinite f]` and
  asserts invertibility of the whole transformation for general coefficient
  categories; `isIso_baseChangeMap_of_isProper` requires properness and uses
  module-valued coefficients. They are related general results, not this exact
  clopen/abelian statement. Open-immersion lower-shriek base change concerns
  extension by zero. The project's `split_clopen_baseChange` concerns splitting
  a finite etale scheme. None duplicates this theorem. The full proposed name
  and blueprint id have no declaration match in the upstream inventory or trees.

No mismatch was found. The module and node record remain unchanged; only this
independent reading is appended. There are no new definition nodes or dependency
modules to review, no statement correction or citer audit to perform, and no
statement dispute. The module's five proof paragraphs follow the node's five
steps, including the unit-compatible germ computation for the actual exchange
and complementary-open refinements outside the image. Its only postponed proof
is the named theorem with `by sorry`; it introduces no definition or axiom.
The recorded signature was compared mechanically with the file and is verbatim
equal. All variables and the universe are explicitly bound, every Lean line is
at most 100 characters, and the docstrings supply the source and blueprint id.

Second-reader validation: `deliver2.py Q08 lem-kun-base-change-open-closed --no-push`
printed `OK (dry run)` after the prescribed single-file compiler checked both
sandbox and library-path forms and the delivery preflight passed. Compilation
was clean, with no non-sorry warning. The delivery contains exactly the module,
its node record and this report.
