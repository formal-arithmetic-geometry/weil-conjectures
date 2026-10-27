## Worker report

The module `Sheaf.CategoryTheory.Sites.EpimorphicFamilyCoverLifts` states
`CategoryTheory.site_epimorphic_family_iff_cover_lifts`. Its sole theorem has
proof `sorry`; there are no new definitions, auxiliary theorems, new nodes,
dependency repairs, or changes to the natural-language statement.

I read the entire item's statement and four-step proof, its four statement
dependencies and their recorded interfaces, the two proof dependencies, and
Stacks `sites.tex` at lemma-quasi-compact (0D06) and
lemma-covering-surjective-after-sheafification (00WT). Tag 0D06 supplies the
forward covering and summand lifts before invoking quasi-compactness; Tag 00WT
supplies the converse cancellation argument. The theorem docstring spells out
all four accepted proof steps, including the injection-preserving isomorphism
between the labelled coproduct model and the chosen categorical coproduct.

Clause-by-clause correspondence:

- A small site is `{C : Type u} [Category.{v} C]`, `J : Precoverage C`, and
  `_hJ : J.IsSiteForCoverings`. Its sheaves use `J.toGrothendieck`, exactly the
  recorded site convention; no global pullback or stronger composition class
  is assumed. The underscore only suppresses an unused-variable warning in
  the postponed proof; the hypothesis remains a theorem argument.
- The common universe is `max u v w`. Objects have universe `u`, arrows `v`,
  and the original index set `I : Type w`. Section sets and the covering index
  type `A` lie in the common universe, which contains all three. The explicit
  universes fulfill `def-weil-size-convention`; no universe equalities are added.
- For every site object `T`, the representable in that universe is
  `uliftYoneda.{max u w}.obj T`. Its sections are `ULift (V ⟶ T)` with
  label-free precomposition restriction maps. `ULift.up` is the canonical
  equivalence from arrows to these sections and adds no mathematical data.
  The theorem uses its instance at the quantified `U : C`.
- The sheafified representable `H_U` is exactly
  `(presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
  (uliftYoneda.{max u w}.obj U)`.
- The unit `eta_U` is `toSheafify J.toGrothendieck
  (uliftYoneda.{max u w}.obj U)`. This is the unit of the recorded
  sheafification adjunction, with target the underlying presheaf of `H_U`.
- The arbitrary family is `F : I → Sheaf J.toGrothendieck
  (Type (max u v w))`, and `p : ∀ i : I, F i ⟶ H_U`.
- The induced map from the sheaf coproduct is `Sigma.desc p`; `Sigma.desc`
  is `colimit.desc` for the discrete diagram, not a pointwise presheaf sum.
  `Sites.Limits` supplies sheaf colimits and the existing sheafification API
  supplies its instance. No existence hypothesis is added.
- The specified cancellation condition is `Epi (Sigma.desc p)`. Mathlib's
  `Epi.left_cancellation` quantifies over every sheaf target and two maps out
  of `H_U`, cancelling this very induced map.
- The words “if and only if” are `↔`, retaining both directions.
- The covering family is existential data `A : Type (max u v w)`, `V : A → C`,
  `a : ∀ b : A, V b ⟶ U`, with `Presieve.ofArrows V a ∈ J U`.
- The labelling function is existential `ι : A → I`.
- Its sections are existential `s : ∀ b : A, (F (ι b)).obj.obj (op (V b))`.
- For every member, the final equality is
  `(p (ι b)).hom.app (op (V b)) (s b) =
  (toSheafify J.toGrothendieck (uliftYoneda.{max u w}.obj U)).app
  (op (V b)) (ULift.up (a b))`. This is exactly the image of the given arrow
  under the sheafification unit. It does not identify a representable with
  its sheafification or assume that the site is subcanonical.

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (full signature and
  docstring read).
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `CategoryTheory.toSheafify`, and their
  defining `CategoryTheory.sheafificationAdjunction` (signatures and
  docstrings read).
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `colimit.desc`, `Cocone`, and `IsColimit`; the discrete specialization is
  `CategoryTheory.Limits.Sigma.desc` from `Limits.Shapes.Products`.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  explicit `u v w` and their common maximum render the needed size conditions.
- Plain proof import `Mathlib.CategoryTheory.Sites.LocallySurjective` gives
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`, the mathlib_match of
  `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`.
- Plain proof import `Sheaf.CategoryTheory.Sites.SmallSheafCoproductLabels`
  gives `CategoryTheory.small_sheaf_coproduct_labels` (full signature and
  docstring read), which provides the local-label clause used in step 2.
- The auxiliary public imports `Sites.Limits`, `Yoneda`, and
  `Limits.Shapes.Products` provide the actual sheaf coproduct instances,
  universe-lifted representable, and its induced coproduct arrow.

Edge cases checked before writing:

- Empty `I` is allowed. Existence of `ι : A → I` forces `A` empty, so the
  right side is precisely the empty-cover condition at `U`. On the left,
  the initial sheaf maps epimorphically to `H_U` exactly in this case.
- Empty coverings are allowed. The sections and lift equations are vacuous;
  separatedness on an empty cover still gives the cancellation in the proof.
- A singleton family, including the identity of `H_U`, admits the identity
  cover with its unit identity section. No finite or nonempty constraint
  occurs on either index type.
- An empty site has no `U` and the assertion has no instances, as intended.
- A non-subcanonical site is included: all arrow sections enter `H_U` via
  the displayed unit. There is no injectivity assumption on that unit.
- Object and morphism universes may differ, and `w` can exceed both. The
  common maximum retains large section and label types without extra
  `HasSheafify` or `HasCoproduct` assumptions; the actual server elaboration
  verifies the existing instances at these universes.

Searches for an existing statement (2026-10-24):

- `msearch.py` LeanFinder query: “A coproduct of sheaves maps epimorphically
  to the sheafification of Hom(-,U) if and only if a covering of U has
  sections lifting into individual summands”. Eight hits, including
  `Sheaf.isLocallySurjective_iff_epi`, `Sheaf.epi_of_isLocallySurjective'`,
  and `SheafOfModules.GeneratingSections.ofEpi`; none states this equivalence
  with individual summand sections over a covering of the representing object.
- `msearch.py` Loogle query: `"yoneda", "epi"`. Nine hits, including
  `Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda` and projective
  and injective Yoneda criteria; none is the present sheaf-coproduct criterion.
- `msearch.py` grep query:
  `(yoneda|representable).*(epi|surject)|(epi|surject).*(yoneda|representable)`
  in `CategoryTheory/Sites`. Eighteen hits. The existing local-surjectivity
  equivalence is reused as a proof dependency; the
  `ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map`
  result concerns a coproduct of presheaf representables, without the arbitrary
  sheaf summands and sheafification-unit lift equation required here.
- `msearch.py` LeanSearch query: “An epimorphic family over a sheafified
  representable admits a covering of the site object with sections lifting
  to individual summands”. Eight hits, principally `EffectiveEpiFamily` and
  its constructors, plus local-surjectivity; no exact match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, and the required item-id grep of upstream:
  no existing declaration of this statement or proposed name.
  Related `SheafSubcategoryComparison` uses a private local-surjectivity
  criterion for families inside a generating subcategory; it is not this
  public criterion and does not state the covering-lift equivalence at `U`.
  `SiteQuasicompactSheafificationCriterion` is the parent finiteness theorem,
  not this extracted statement. No new notion is needed.

Validation: the prescribed `scompile.py` compiled the delivered statement in
sandbox and library module modes, each in 1.6 seconds, with no errors or
unexpected warnings. The final delivery dry run recompiles the final file.
No node fault or statement dispute was found.

## Second reading by Q19

This is a separate worker rereading of the node and final signature; the
maintainer performs the independent review after delivery. I checked the
four statement-dependency records against the concrete terms and checked
both sides of the equivalence. In particular, `Sigma.desc p` is a sheaf
coproduct map, `Epi` cancels against all sheaf targets, and the right side
requires membership in the original covering precoverage, not merely a
covering sieve in its generated Grothendieck topology. The family objects,
label function, dependent sections, and unit-image equality occur as
existential data exactly as in the node. All universes are bound explicitly;
`max u v w` includes both site universes and `I`. Neither `I` nor `A` has a
nonemptiness binder. I rechecked the empty-cover and non-subcanonical cases
against the use of separatedness and the sheafification universal property.
There is no hidden replacement of `eta_U(a)` by `a` itself. The proof docstring
contains all four accepted steps and every postponed proof is the item's
single named theorem. No mismatch or statement change was needed.
