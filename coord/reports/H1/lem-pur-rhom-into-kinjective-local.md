## Worker report

The module `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal` states
`CategoryTheory.rhom_into_kinjective_local`. Every theorem proof is `sorry`.
The node copy changes only `lean`. No statement correction, new definition node,
or replacement dependency module is needed.

Source read: https://stacks.math.columbia.edu/tag/0A94, Lemma 21.34.6.
The local `literature/stacks-project/sites-cohomology.tex` is absent, so the
published source was opened. Its proof first identifies the zeroth cohomology
with localized homotopy-category morphisms and then uses K-injectivity of the
restricted target. This is exactly the node's three-step proof, reproduced in
the declaration docstring. The node uses the representatives directly, so no
extra choice of objects of the global derived category is necessary.

Hypotheses and clauses, individually:

- The site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
- The sheaf of commutative rings is `(R : Sheaf J CommRingCat.{r})`.
  `R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R` forgets
  commutativity only for the module-category interface; it uses the same rings.
- The chosen object is `(U : C)`. The localized site is `J.over U` on `Over U`,
  and its restricted ring sheaf is `R₀.over U`.
- `[J.HasSheafCompose ...]` supplies the ring-forgetting functor. The explicit
  `HasSheafify` and `WEqualsLocallyBijective` instances on `J` and `J.over U`
  are Mathlib's infrastructure for the usual abelian categories of module
  sheaves in the chosen section universe `w`. They impose no geometric,
  boundedness, or injectivity condition. They ensure the abelian structures
  use the existing canonical preadditive structure. Every ordinary small site
  is covered by taking a sufficiently large section universe; all site,
  morphism, ring, section and derived-morphism universes are explicit and
  independent. `[HasDerivedCategory.{t} ...]` chooses the localization and
  its morphism universe, as the recorded derived-category dependency requires.
- The complexes are `(L I : CochainComplex (SheafOfModules.{w} R₀) ℤ)`.
- The target hypothesis is exactly `[I.IsKInjective]`. There is no hypothesis
  that its restriction is already K-injective, nor termwise injectivity or
  boundedness assumption on either complex.
- `H := homComplex L I` is the recorded sheaf-valued Hom complex. `π` is
  selected from the specification theorem used to define this very Hom
  complex, using `Classical.choose (Classical.choose_spec homComplex_exists)`.
  It is not an independently chosen product or a new Hom-complex definition.
- `S` is `H` evaluated at `op U`, followed by forgetting scalar multiplication
  to `AddCommGrpCat`, degree by degree. The composite of `SheafOfModules.forget`
  and `PresheafOfModules.evaluation` is the body of the existing
  `SheafOfModules.evaluation` functor. It is written unfolded so Mathlib can
  find its zero-preservation instances. Thus `S` is precisely
  `Γ(U, Hom•(L,I))`, not derived sections and not sections of sheaf cohomology.
- `res` is the existing `SheafOfModules.overFunctor R₀ U` applied degreewise
  with `mapHomologicalComplex`. Its objects are exactly `L|U` and `I|U`.
- `Q` is `DerivedCategory.Q.{t}` for module sheaves over `R₀.over U`, hence
  the node's `Q_U`, localizing at quasi-isomorphisms.
- Degree-zero cocycles are the underlying elements of `S.cycles 0`.
  `∃ e : S.cycles 0 ≃ (res.obj L ⟶ res.obj I)` states their correspondence
  with morphisms of restricted complexes in both directions.
- The following equation, for every `z`, integer `p`, and localized-site
  object `W`, fixes that correspondence to the canonical one:
  `((e z).f p).val.app W =
  (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W`.
  The projection extracts the degree-`p` localized linear map from the
  section of the product; `S.iCycles 0` includes the cocycle into degree zero.
  In particular the equivalence cannot permute or change those maps.
- The domain of `φ` is the underlying group of `S.homology 0`, exactly the
  node's `H⁰(Γ(U, Hom•(L,I)))`.
- Its codomain is exactly `Q.obj (res.obj L) ⟶ Q.obj (res.obj I)`.
- `∀ z, φ (S.homologyπ 0 z) = Q.map (e z)` is the formula `[f] ↦ Q_U(f)`.
  Existential quantification over `φ` together with this equation expresses
  well-defined descent through the cohomology-class map. It forces equal
  cohomology classes to have equal localized images. It determines the map,
  since every degree-zero cohomology class is represented by a cycle.
- `Function.Bijective φ` is precisely the concluding bijectivity clause.

The named auxiliary theorem `CategoryTheory.module_overFunctor_preservesZero`
supplies the missing registered zero-preservation instance for restriction.
It concerns the same restriction in the node's proof; its docstring gives the
pointwise proof and source, and its proof is `sorry`. The main statement uses
it with `letI`, rather than adding zero preservation as an assumption or
redefining restriction. No definition contains `sorry` data.

Dependency declarations read and used:

- `def-pc-cochain-complex-modules`: `CochainComplex`, from
  `Mathlib.Algebra.Homology.HomologicalComplex`; specialized to sheaves of
  modules, integer degrees, with Mathlib chain-map morphisms.
- `def-pur-kinjective-complex`: `CochainComplex.IsKInjective`, from
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`; its complete class
  signature says every map from an acyclic complex is null-homotopic.
  Its `mathlib_match` is sufficient, although the node has no `lean` record.
- `def-pur-hom-complex`: `CategoryTheory.homComplex`,
  `CategoryTheory.homComplex_exists`, and the defining selection
  `CategoryTheory.homComplexFunctor`, from
  `Sheaf.Algebra.Homology.HomComplex`. The full specification was read:
  product projections, differential with `n.negOnePow`, and functoriality.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`, from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the source records the
  localization instance at `HomologicalComplex.quasiIso`. Again the
  `mathlib_match` is the usable declaration, not a missing dependency.

Other existing notions used are `SheafOfModules.overFunctor` (the restriction
functor in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`),
`SheafOfModules.homObj` (transitively imported by the recorded Hom complex),
`HomologicalComplex.cycles`, `iCycles`, `homology`, `homologyπ`, and
`Functor.mapHomologicalComplex`. No private copy of these notions is written.

Edge cases checked before writing:

- Zero `L` or zero `I`: the cocycle group, cohomology, and the relevant Hom
  group reduce to the expected zero objects/groups. The equivalence and
  localization formula still state the correct singleton correspondence.
- No lower or upper degree bound is imposed; products are over all integers.
- `U` is arbitrary, including an initial object when the site has one; there
  is no nonemptiness or nonzero-section condition. If `C` is empty there is
  no `U`, so the universally quantified assertion has no excluded case.
- The zero ring sheaf, positive characteristic and characteristic zero are
  all allowed; there are no characteristic or nontriviality hypotheses.
- The cocycle identification is checked on every object of `Over U`, not
  just its terminal object. Its components are linear morphisms, not merely
  arbitrary functions or global morphisms on the original site.

Searches made (logged by the required msearch tool in `searches.jsonl`):

- LeanSearch query: `The zeroth cohomology of sections of sheaf Hom complex
  into K injective equals morphisms in localized derived category`.
  Service unavailable (`Internal Server Error`), recorded as unavailable;
  no negative mathematical verdict is inferred from this failure.
- LeanFinder query: `Hom complex into K-injective computes localized derived
  morphisms on a site`. Eight results, including
  `CochainComplex.IsKInjective.Qh_map_bijective`; these are abstract
  homotopy/derived comparison results, not the sheaf-section statement.
- Loogle query: `CochainComplex.IsKInjective`. Twelve results, including the
  K-injective class and the abstract HomComplex cocycle lemmas; none states
  the localized sheaf-valued section-to-derived-morphism comparison.
- Mathlib grep query: `Qh_map_bijective|homComplex`, restricted to
  `Algebra/Homology`. Results cover the abstract group-valued Hom complex,
  not the needed sheaf-valued Hom-complex theorem.
- Local `rg` of `homComplex|rhomIntoKInjectiveLocal`, and later
  `homComplex|KInjective|derived.*[Hh]om`, in project and upstream homology
  sources found the existing Hom-complex definition, but no matching lemma.
  `grep -rn 'lem-pur-rhom-into-kinjective-local'` in upstream Lean found none.
- Declaration-name searches for `module_overFunctor_preservesZero` and
  `rhom_into_kinjective_local` in Mathlib, upstream Lean, project Lean, and
  `dag/lean_names_upstream.json` found no collisions.

Validation: server compilation succeeded with exit code 0 and no errors or
warnings. The missing zero-preservation registration and an instance mismatch
from arbitrary abelian-structure binders were repaired; the final statement
uses Mathlib's canonical abelian instances. No statement dispute or node fault
was found.

## Second reading by H1

I independently compared the node's objects, hypotheses, and conclusion with
`CategoryTheory.rhom_into_kinjective_local` in
`lean/Sheaf/Algebra/Homology/RhomIntoKInjectiveLocal.lean`.

* The site is rendered by `{C : Type u} [Category.{v} C]` and
  `J : GrothendieckTopology C`; the commutative ring sheaf is rendered by
  `R : Sheaf J CommRingCat.{r}`, with `sheafCompose` supplying its underlying
  `RingCat` sheaf `R₀`.
* The chosen object `U : C`, localized site `J.over U`, and restricted ring
  sheaf `R₀.over U` are introduced explicitly. The four sheafification and
  locally-bijective typeclass hypotheses are infrastructure for the module
  sheaf categories and do not impose geometric, finiteness, boundedness, or
  characteristic assumptions.
* `L I` are exactly integer-indexed cochain complexes of `SheafOfModules R₀`,
  and `[I.IsKInjective]` is the sole hypothesis on the target complex. No
  termwise injectivity or boundedness is added.
* `H := homComplex L I`, `π` is selected from `homComplex_exists`, and `S` is
  evaluation at `op U` followed by forgetting to additive commutative groups;
  this is precisely the node's global sections of the sheaf Hom complex.
  `res` is the existing module restriction functor transported degreewise by
  `mapHomologicalComplex`, and `Q` is the derived localization on modules over
  `R₀.over U`.
* The first conclusion clause gives an equivalence
  `e : S.cycles 0 ≃ (res.obj L ⟶ res.obj I)`. Its following equation is
  quantified over every cocycle, integer degree, and `W : (Over U)ᵒᵖ`, and
  identifies each component with the canonical projection of `π`; hence it
  fixes the intended cocycle-to-chain-map correspondence.
* The second clause existentially supplies `φ : S.homology 0 → ...`, states
  `φ (S.homologyπ 0 z) = Q.map (e z)` for every cycle, and requires
  `Function.Bijective φ`. This is exactly the node's well-defined bijection
  `[f] ↦ Q_U(f)`, with the same quantifier order.

No mismatch was found and no statement or dependency was changed. The
auxiliary `module_overFunctor_preservesZero` theorem registers the zero
preservation needed by the existing restriction functor; it adds no assumption
to the main statement and has only a `sorry` proof. All declarations carry the
source and blueprint docstrings. Edge cases checked are zero complexes,
arbitrary (including empty) sites and objects, all integer degrees including
zero, the zero ring, and arbitrary characteristic; none is excluded by the
Lean binders. Searches in Mathlib, the upstream project, and this repository,
plus LeanFinder/Loogle/LeanSearch, found no existing localized sheaf-valued
statement or name collision.

## Reviewer fix (R-rkl1403, stage 2)

The statement was restated in the large-site universes of the landed Hom-complex
users (G1 `CochainComplex.isKInjective_homComplex_of_isKFlat`, 846abea62; M1
`homComplex_tensorTotal_iso`, 0e8e9db2e): `{C : Type u} [Category.{v} C]`,
`R : Sheaf J CommRingCat.{max u v}`, complexes in `SheafOfModules.{max u v}`,
sections in `ModuleCat.{max u v}`, restriction `SheafOfModules.overFunctor.{max u v}`.
In these universes Mathlib synthesizes `HasSheafify` and `WEqualsLocallyBijective`
for `AddCommGrpCat.{max u v}` on `J` and on `J.over U`, so the four instance binders
and `[J.HasSheafCompose ...]` were removed (imports
`Mathlib.CategoryTheory.Sites.LeftExact`, `...Sites.LocallyBijective`,
`Mathlib.Algebra.Category.Grp.FilteredColimits` added). `homComplex` and
`homComplex_exists` are applied with `(R := R)` and explicit universes. The
hypotheses (`[I.IsKInjective]`, `[HasDerivedCategory.{t}]` on `R₀.over U`) and all
conclusion clauses are unchanged. The auxiliary
`module_overFunctor_preservesZero` keeps its general universes.
