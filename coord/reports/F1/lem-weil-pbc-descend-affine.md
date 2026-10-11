## Worker report

The module `Sheaf.AlgebraicGeometry.DescendAffine` states
`AlgebraicGeometry.exists_isAffineHom_baseChange_of_isLimit`, with proof `sorry`.
No definition is introduced, no dependency record is replaced, and the item's statement
is unchanged. The remote compiler accepted the module without warnings (1.6 seconds).

Hypothesis and clause correspondence:

- The directed set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The chosen index `0 ∈ I` is `(i₀ : I)`; it supplies nonemptiness without an extra assumption.
- The inverse system of schemes is `(D : Iᵒᵖ ⥤ Scheme.{u})`. For `hi : i₀ ≤ i`,
  `D.map (homOfLE hi).op` is exactly the transition `Sᵢ → Sᵢ₀`.
  The functor laws express the identity and composition laws of the inverse system.
- Affine transition morphisms are the binder
  `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- The specified limit `S` with its compatible projections is `(c : Cone D)` with
  `(hc : IsLimit c)`. Its underlying scheme is `c.pt`, and its projection to `S₀`
  is `c.π.app (op i₀)`. This states the property for any specified limit cone;
  the recorded limit-existence theorem supplies such a cone when needed.
- `S₀` is `D.obj (op i₀)`; its quasi-compactness and quasi-separatedness are
  `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`.
- The schemes `X₀` and `Y₀` are bound explicitly, and each has both `CompactSpace`
  and `QuasiSeparatedSpace` binders. On a scheme these are exactly the qcqs properties.
- The morphism over `S₀` is `(f₀ : X₀ ⟶ Y₀)` with `(h : Y₀ ⟶ D.obj (op i₀))`.
  The structure map of `X₀` is `f₀ ≫ h`. This parametrizes every morphism over
  `S₀`: its source structure map is necessarily that composite. No condition on
  `f₀` beyond being a morphism over the base is added.
- For any base map `p : T ⟶ S₀`, the induced morphism is
  `pullback.map (f₀ ≫ h) p h p f₀ (𝟙 T) (𝟙 S₀) ... ...`.
  Its domain is the chosen `X₀ ×[S₀] T`, its codomain the chosen `Y₀ ×[S₀] T`.
  The two supplied equality terms are just identity-composition laws for this
  map, not additional hypotheses or auxiliary theorem proofs.
- The hypothesis that `f` is affine is `(hf : IsAffineHom (...))`, with
  `p = c.π.app (op i₀)` and `T = c.pt` in that same `pullback.map`.
- The conclusion is `∃ (i : I) (hi : i₀ ≤ i), IsAffineHom (...)`, with
  `p = D.map (homOfLE hi).op` and `T = D.obj (op i)`.
  Thus it asserts exactly that some base change at an index `i ≥ 0` is affine,
  and does not strengthen this to an eventual statement.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. Read their structure signatures and docstrings.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`. Its field tests every affine target
  open and requires its inverse image to be affine, exactly the node's notion.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition`,
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`. Read the full signature and
  proof docstring. Import this module for the affine-transition limit setup.
  Its existence assertion is an input to constructing a limit cone, not an
  additional constraint on the cone quantified over here.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration
  or module of its own. Use its specified Mathlib meanings directly:
  `CompactSpace`, `QuasiSeparatedSpace`, and `IsAffineHom`. Read the
  `QuasiSeparatedSpace` signature and `quasiSeparatedSpace_iff_quasiSeparated`
  to check the scheme interpretation.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and the induced
  morphism `pullback.map`. Read both full signatures and docstrings, with the
  chosen projections and universal lifting operation. Scheme pullbacks are
  supplied by Mathlib, as recorded in the dependency's match.

Edge cases checked before writing:

- Empty `I` admits no `i₀`, matching the node's choice of an element.
- There is no strict inequality in the conclusion, so `i = i₀` is permitted.
  A singleton directed set and identity transitions are included.
- Empty schemes are permitted. If `Y₀` is empty so is `X₀`; the finite affine
  cover may be empty and the natural-language proof chooses `i₀`.
- No nonemptiness, reducedness, finite presentation, separatedness, or field
  characteristic is assumed. Only the three specified schemes are assumed qcqs;
  no unnecessary qcqs hypothesis is placed on every stage.
- `Preorder` includes directed preorders, in accordance with the directed-set
  convention. All universes and all variables are explicitly bound. The common
  universe follows the recorded limit dependency; any set-sized diagram can be
  placed in a common sufficiently large universe. There is no quantification
  over test schemes in a smaller independent universe.

Source check: the local `literature/stacks-project/limits.tex` is not present on
this machine. Read the original source online instead:
[Stacks 01ZN](https://stacks.math.columbia.edu/tag/01ZN) and
[Stacks 081D](https://stacks.math.columbia.edu/tag/081D).
The latter supplies exactly the qcqs assumptions on `S₀`, `X₀`, `Y₀` and the
base-change setup. The former gives the affineness implication. The docstring
carries the node's six proof steps and their dependency IDs.

Searches made (all repository and source searches were read-only):

- `msearch.py ... leansearch`: query "If a base change of a morphism to an inverse
  limit of schemes with affine transition maps is affine then it is affine at
  some stage". Unavailable: Internal Server Error; no verdict assigned.
- `msearch.py ... leanfinder`: query "affine morphism base changed to inverse limit
  of qcqs schemes descends to a finite stage". Eight hits, including
  `Scheme.exists_isAffine_of_isLimit`, `isAffineHom_π_app`,
  `exists_isAffineOpen_preimage_eq`, and finite-type factorization results.
  None is affineness descent of the specified morphism.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.IsAffineHom, CategoryTheory.Limits.IsLimit, CategoryTheory.Limits.pullback`.
  Successful search, zero hits.
- `msearch.py ... grep` in Mathlib `AlgebraicGeometry`:
  `01ZN|exists.*[Aa]ffine.*[Bb]ase|[Aa]ffine.*[Dd]escend`.
  Seven unrelated effective-epimorphism and faithfully-flat descent hits.
- `rg` in Mathlib's `AffineTransitionLimit.lean`: inspected `IsAffineHom` uses,
  the limit projection result and `Scheme.exists_isAffine_of_isLimit`.
  There is no morphism-affineness descent result (the scheme-affineness theorem
  is the node's stage-3 proof input, not this statement).
- `rg` over `WeilConjectures/` and `lean/Sheaf`:
  `descend.*affine|affine.*descend|lem-weil-pbc-descend-affine`.
  Hits concern fpqc descent, finite presentation of objects, and other unrelated
  results; no exact existing declaration or blueprint ID match.
- `rg` over `dag/lean_names_upstream.json`, `WeilConjectures/` and `lean/Sheaf`:
  `exists_isAffineHom_baseChange_of_isLimit|lem-weil-pbc-descend-affine|01ZN`.
  No collision with the chosen declaration name or existing exact statement.

No statement dispute or node fault was found. No new nodes or dependency modules
are needed. The second reading is intentionally left to the independent reader.

## Second reading by F1

Independently opened the item JSON, the delivered Lean module, all five statement
 dependency nodes, and the source declarations they record. Read Stacks Limits
`limits.tex` directly from the upstream Stacks repository, from
`\label{situation-descent-property}` through the proof of
`\label{lemma-descend-affine-finite-presentation}`; also checked the tag pages
[081D](https://stacks.math.columbia.edu/tag/081D) and
[01ZN](https://stacks.math.columbia.edu/tag/01ZN). The situation supplies exactly
qcqs for S₀, X₀, Y₀; the lemma assumes affineness only after base change.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. Directed index set I: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)]`. A preorder is permitted by the project's directed-set
   convention; no totality or least-element hypothesis is introduced.
2. Inverse system of schemes Sᵢ with compatible transition morphisms:
   `(D : Iᵒᵖ ⥤ Scheme.{u})`. Functoriality gives the transition identities and
   composition laws. `Scheme` and `Scheme.Hom` are the dependency's Mathlib
   schemes and locally ringed-space morphisms, not another category.
3. Every transition affine: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j),
   IsAffineHom (D.map a)]`. Read `IsAffineHom.isAffine_preimage`: it tests every
   affine target open, precisely `pqf-def-affine-morphism`.
4. Specified inverse limit S and its projections: `(c : Cone D)
   (hc : IsLimit c)`, with S = `c.pt` and p₀ = `c.π.app (op i₀)`.
   Read `exists_limit_affine_transition` in the imported dependency module:
   it constructs such a cone with affine projections, open restriction limits,
   and the affine-spectrum identification. This item's arbitrary limiting cone
   uses the same categorical limit notion; no stronger condition is imposed.
5. Chosen index 0 ∈ I: `(i₀ : I)`. S₀ = `D.obj (op i₀)`.
6. S₀ qcqs: `[CompactSpace (D.obj (op i₀))]
   [QuasiSeparatedSpace (D.obj (op i₀))]`. The convention dependency defines
   no extra notion. Read `quasiSeparatedSpace_iff_quasiSeparated` identifying
   the topological condition with quasi-separatedness over the terminal scheme.
7. X₀, Y₀ qcqs schemes: `{X₀ Y₀ : Scheme.{u}}` with `CompactSpace` and
   `QuasiSeparatedSpace` for each. Neither affine nor Noetherian is assumed.
8. f₀ a morphism over S₀: `(f₀ : X₀ ⟶ Y₀)
   (h : Y₀ ⟶ D.obj (op i₀))`. The source structure map is `f₀ ≫ h`.
   Every commuting morphism over S₀ has this form, so eliminating that redundant
   source structure map does not lose any data or add a hypothesis.
9. Xᵢ, Yᵢ and fᵢ are the specified fibre products and induced map:
   `pullback.map (f₀ ≫ h) p h p f₀ (𝟙 T) (𝟙 S₀) ... ...`, with
   T = `D.obj (op i)` and p = `D.map (homOfLE hi).op`.
   Read `pullback`, both projections, `pullback.lift`, and `pullback.map`
   in `HasPullback.lean`: the map goes from `pullback (f₀ ≫ h) p` to
   `pullback h p`, with first component f₀ and second component the identity.
   Scheme pullbacks exist by `HasPullbacks Scheme`. The equality arguments are
   composition-with-identity equations, not mathematical assumptions.
10. X, Y and f are the same base change to S: the identical `pullback.map`
    with T = `c.pt` and p = `c.π.app (op i₀)`.
11. f affine: `(hf : IsAffineHom (...))` tests exactly this map.
12. Conclusion: `∃ (i : I) (hi : i₀ ≤ i), IsAffineHom (...)` tests exactly
    fᵢ. The witness i is chosen after the system, base morphism and affineness
    hypothesis; hi supplies its transition to i₀. No eventualness clause is added.

Edge cases: an empty I has no chosen i₀, exactly as in the node; a singleton
system and i = i₀ are admitted. Empty schemes and empty affine covers are
admitted (the docstring explicitly takes i₀ for an empty cover). Zero rings and
all characteristics are admitted through Mathlib schemes; there is no field,
nonzero, or nonempty-scheme condition. No numerical n is bound. The common
universe u follows the dependency and admits every set-sized system in a
sufficiently large common universe; there is no smaller-universe test-object
quantifier. Every variable and universe in the signature is explicitly bound.

Independent searches used different phrasing from the worker:

- LeanFinder: "affineness of a map between base changed schemes is detected at
  a stage of an inverse system". Eight hits: limit projections, scheme-affineness
  at a stage, affine opens at a stage, and base-change/fpqc descent tools.
  Opened `Scheme.exists_isAffine_of_isLimit`: its conclusion is
  `∃ i, IsAffine (D.obj i)`, not this morphism statement; no exact match.
- Loogle: `"IsAffineHom", "IsLimit"`: successful, zero hits.
- LeanSearch: "A morphism of quasi compact quasi separated schemes becomes
  affine at a finite stage if affine over the inverse limit": unavailable
  (Internal Server Error), recorded without assigning a verdict.
- `rg` across Mathlib AlgebraicGeometry, upstream `WeilConjectures/`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, using
  `01ZN|[Aa]ffine.*(isLimit|[Dd]escen)|[Dd]escen.*[Aa]ffine|exists_isAffineHom`.
  Inspected all `IsAffineHom` occurrences in the upstream extended
  `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` as well.
  Hits concern transition maps, affine objects, finite-presentation descent,
  and fpqc descent; none states this affineness implication at a finite stage.
  No existing exact theorem or name collision found.

No mismatch found, and no Lean or node repair was needed. No new definition
nodes, dependency modules, or statement corrections are present or required.
There is one theorem with proof `sorry`, no new definition and no hollow data.
The module and declaration docstrings carry the source and blueprint ID, and
all six DAG proof steps and their dependencies are present in the declaration
proof narrative. Header, namespace, topic path, import, and line widths follow
project conventions. The dependency import supplies the affine-transition-limit
setup and its underlying Mathlib definitions. The node's `lean.statement` was
checked literally equal to the file signature through the conclusion before
`:= by`. Remote `scompile.py` accepted the unchanged module in 1.7 seconds,
exit code 0, with no diagnostics. The only change is this independent report.
