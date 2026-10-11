## Worker report

The module `lean/Sheaf/CategoryTheory/Abelian/HorseshoeResolutions.lean` states
`CategoryTheory.InjectiveResolution.exists_horseshoe_resolutions`, with its only
proof `sorry`. No definition, additional hypothesis, or statement correction is needed.
The item's JSON changes only in `lean`.

Hypothesis and clause correspondence:

- An arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  Object and morphism universes are explicitly bound and independent.
- Enough injectives is `[EnoughInjectives C]`.
- The input sequence `0 → A → B → C → 0` is `(S : ShortComplex C)
  (hS : S.ShortExact)`. Its objects are `S.X₁`, `S.X₂`, `S.X₃`; its maps
  are `S.f` and `S.g`. `ShortExact` includes exactness, monicity of `f`,
  and epicity of `g`, while `ShortComplex` supplies their zero composite.
- The three resolutions and augmentations are the existentially quantified
  `IA : InjectiveResolution S.X₁`, `IB : InjectiveResolution S.X₂`, and
  `IC : InjectiveResolution S.X₃`, with complex fields `.cocomplex` and
  augmentation fields `.ι`. Mathlib's structure supplies injectivity in every
  degree and a quasi-isomorphism from the single complex in degree zero.
- Vanishing in all negative degrees is rendered by Mathlib's natural-number
  indexing, as in the dependency's `mathlib_match` and the landed prescribed-end
  horseshoe lemma. These complexes are interpreted by extension by zero to
  integer degrees; no negative term or extra cohomology is allowed.
- The complex maps are the existential binders `α` and `β`.
- The square `α⁰ ∘ s_A = s_B ∘ f` is
  `IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι`.
- The square `β⁰ ∘ s_B = s_C ∘ g` is
  `IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι`.
  These complex-map equalities are equivalent to the required degree-zero
  equalities: in positive degrees the source is zero.
- Short exactness in every `n ≥ 0` is `∀ n : ℕ` followed by
  `((ShortComplex.mk α β hαβ).map
  (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact`.
  The existential `hαβ : α ≫ β = 0` records the zero composite that the
  degreewise exact rows already require, rather than adding an extra condition.
- The parenthetical choice of middle terms as biproducts with inclusion and
  projection is `∃ e : IB.cocomplex.X n ≅ IA.cocomplex.X n ⊞ IC.cocomplex.X n,
  α.f n ≫ e.hom = biprod.inl ∧ β.f n = e.hom ≫ biprod.snd`.
  The isomorphism is the categorical identification with the direct sum,
  including identification of both row maps. It is not merely an abstract
  split exactness assertion. This is the form accepted for the sibling
  `lem-sp-horseshoe-prescribed-resolutions`.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, signature and docstring at lines
  103–116. Its finite products, kernels, cokernels and normal mono/epi classes
  give the node's abelian-category structure.
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, lines 38–55,
  including the `.cocomplex`, `.injective`, `.ι`, and `.quasiIso` fields.
  `CategoryTheory.Injective` and `CategoryTheory.EnoughInjectives` were also
  read in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, lines 28–65.
  Both dependency nodes are Mathlib leaves and need no `lean` record.
- `CategoryTheory.ShortComplex.ShortExact`,
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, lines 37–42.
  The single import `Mathlib.CategoryTheory.Abelian.Injective.Resolution`
  brings these definitions and the biproduct and evaluation notation into scope.

Edge cases checked before writing: `n = 0` is included, with precisely the
augmentation compatibility required; all positive degrees have zero source in
these squares; negative degrees are extension by zero. If any of the three
objects is zero, no nonzero-object hypothesis prevents applying the statement.
A split input sequence and the zero category are included. No finite-generation,
Grothendieck, smallness, or prescribed-resolution assumption is added.

Searches (2026-10-11):

- `msearch.py leansearch`, query "A short exact sequence in an abelian category
  with enough injectives has injective resolutions forming a degreewise split
  short exact sequence": service unavailable, Internal Server Error.
- `msearch.py leanfinder`, query "In an abelian category with enough injectives
  a short exact sequence admits compatible injective resolutions forming a
  degreewise split short exact sequence": eight hits, including
  `ShortExact.splittingOfInjective`, `InjectiveResolution.exact₀`, `exact_succ`,
  `ofCocomplex_exactAt_succ`, `cocomplex_exactAt_succ`, `of_def`, `of`, and
  `CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective`;
  none states this simultaneous-resolution existence theorem.
- `msearch.py loogle`, query
  `CategoryTheory.InjectiveResolution, CategoryTheory.ShortComplex.ShortExact`:
  zero hits.
- `msearch.py grep`, query `horseshoe|ShortExact|biprod` in
  `CategoryTheory/Abelian/Injective`: eight hits, for an injective presentation's
  short exact sequence and injective dimension, not the horseshoe statement.
- `rg` in `WeilConjectures/CategoryTheory` for short exact sequences and
  injective resolutions found existing derived-functor and dimension-shifting
  material, no compatible simultaneous-resolution theorem. The requested
  `grep -rn 'lem-weil-pbc-injective-resolution-ses' WeilConjectures` had no hits.
- `rg` in `lean/Sheaf` for `horseshoe` found
  `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions`, whose full
  theorem and docstring were read. Its outer resolutions are prescribed input
  data, while this item existentially quantifies all three. Thus it is a related
  stronger theorem, not the same signature; no existing record is substituted.
- `rg` for `exists_horseshoe_resolutions` in Mathlib, WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no name collision.

Source check: local `literature/stacks-project/derived.tex` is absent on this
machine. Read the official [Stacks Tag 013T](https://stacks.math.columbia.edu/tag/013T)
(Lemma 13.18.9): specialize to complexes concentrated in degree zero; part (2)
gives the bound and Step 2 gives biproduct terms. The source supports the
unchanged node statement.

Node proof fault (not a statement fault): the first proof step's second
"pushout" of `P → C` along `C ↪ I_C` is not the claimed construction.
Instead the injective subobject `I_A → P` splits, giving `P ≅ I_A ⊞ C`,
which embeds into `I_A ⊞ I_C`. This valid version is written explicitly in
Step 1 of the docstring; the subsequent cokernel induction and verification
are stated step by step. No node proof field was changed. The final proof step's
word "functorial" is not a clause of the statement, and no strict functoriality
of arbitrary choices is asserted in Lean.

Validation: `scompile.py M1 lem-weil-pbc-injective-resolution-ses` compiled the
module on the server in 1.1 seconds, exit code 0, without warnings. Delivery
dry run is the final gate; the independent second reader will supply their own
reading and deliver.

## Second reading by M1

I independently read the item JSON, its full Lean module, both statement-dependency
nodes and their Mathlib declarations, and the full related prescribed-resolution
module. No statement correction, new definition node, or dependency module is present
or needed. The original Lean and node record are retained unchanged.

Object/hypothesis/conclusion checklist (H3):

1. Object: an arbitrary abelian category, rendered by `{C : Type u}`,
   `[Category.{v} C]`, `[Abelian C]`. Verdict: exact. Independent explicit universes
   `u` and `v` admit large categories and arbitrary morphism universes. The dependency
   `def-sp-abelian` matches `CategoryTheory.Abelian`: the finite-product formulation
   derives zero objects and finite biproducts, and normal mono/epi means kernel/cokernel.
2. Hypothesis: enough injectives, rendered by `[EnoughInjectives C]`. Verdict: exact.
   I read `Injective.factors`, `InjectivePresentation`, and `EnoughInjectives.presentation`
   in Mathlib's `Preadditive/Injective/Basic.lean`: every object embeds into an injective.
   No Grothendieck or smallness assumption is added.
3. Objects: A, B, C and f, g in a short exact sequence, rendered by `(S : ShortComplex C)`
   with `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g`. Hypothesis: `(hS : S.ShortExact)`.
   Verdict: exact. I read `ShortComplex.ShortExact`: exactness, mono first map, epi
   second map; `ShortComplex` already stores zero composite. This bundles rather than
   restricts the arbitrary input data; the category binder named C is not the third object.
4. Conclusion: three injective resolutions and their augmentations, rendered by
   existential `IA : InjectiveResolution S.X₁`, `IB : InjectiveResolution S.X₂`,
   `IC : InjectiveResolution S.X₃`, with fields `.cocomplex` and `.ι`. Verdict: exact.
   I read `def-sp-injective-resolutions` and Mathlib's structure: its `.injective`
   fields give injective terms, and `.quasiIso` gives the prescribed object in degree-zero
   cohomology and vanishing higher cohomology. `.hasHomology` is automatic in an abelian
   category, not an extra hypothesis.
5. Conclusion: all terms zero below zero, rendered by the same Mathlib resolutions'
   `CochainComplex C ℕ` indexing, interpreted by extension by zero to ℤ. Verdict: exact
   for these zero-bounded resolutions; no shift or negative cohomology is admitted.
   This is also the dependency record's and prescribed-resolution sibling's convention.
6. Conclusion: complex morphisms α and β, rendered by the existential morphisms
   `α : IA.cocomplex ⟶ IB.cocomplex` and `β : IB.cocomplex ⟶ IC.cocomplex`.
   Verdict: exact; their types include commutation with all differentials.
7. Conclusion: α⁰ s_A = s_B f, rendered by
   `IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι`. Verdict: exact.
   Composition is written in categorical order. Positive-degree components of the source
   are zero, so equality of complex maps adds no condition beyond degree zero.
8. Conclusion: β⁰ s_B = s_C g, rendered by
   `IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι`. Verdict: exact,
   for the same degree-zero reason; the directions and original maps are correct.
9. Conclusion: short exact rows in each n ≥ 0, rendered by `∀ n : ℕ` and
   `((ShortComplex.mk α β hαβ).map
   (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact`.
   Verdict: exact. The existential `hαβ : α ≫ β = 0` is necessary to bundle the
   sequence, but already follows componentwise from the asserted rows; it does not
   strengthen the conclusion. No preselected resolutions are required: all three
   are quantified after S and hS and before the morphisms and degreewise conditions.
10. Conclusion: the optional biproduct choice with inclusion and projection, rendered by
    `∃ e : IB.cocomplex.X n ≅ IA.cocomplex.X n ⊞ IC.cocomplex.X n`,
    `α.f n ≫ e.hom = biprod.inl`, and `β.f n = e.hom ≫ biprod.snd`.
    Verdict: exact categorical identification with both specified maps, not only an
    isomorphism of objects or an unconnected splitness predicate. Literal chosen-object
    equality is immaterial to the mathematical direct-sum choice.

Source check: the local Stacks .tex is absent. I read the raw authoritative
[derived.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex),
including `section-injective-resolutions`, its definition, and the complete statement
and proof at `lemma-injective-resolution-ses`, and cross-checked
[Tag 013T](https://stacks.math.columbia.edu/tag/013T). There is no standing ring,
field, characteristic, finiteness, or geometric assumption. Specializing to the
three single-degree complexes gives this node. The source supplies the zero bound
and its proof constructs the middle terms as direct sums. Part (3)'s prescribed
first resolution is an additional available refinement, not a requirement of this node.

Edge cases: n = 0 is included and both augmentation squares have their intended
nonzero component there. All negative terms are zero under the indexing convention.
Any or all input objects may be zero; split input rows and the zero category are
covered. An empty category cannot be abelian, since it has a zero object. There is
no varying index family here, hence no empty-index assumption to impose. An empty
scheme's sheaf category is covered whenever it has the stated category structures;
no scheme or characteristic appears in the abstract theorem. Object and morphism
universes are bound independently; no extra `SmallCategory` instance is assumed.

Independent H4 searches, with words different from the first reader's:

- `msearch.py leanfinder "compatible injective resolutions with split exact rows and
  commuting augmentations"`: eight hits, all individual resolution comparison maps
  (`descFSucc`, `descFOne`, `descFOne_zero_comm`, `descHomotopyZeroZero`,
  `desc_commutes_zero_assoc`, `descHomotopyZeroSucc`, `desc_commutes_assoc`,
  `descHomotopyZeroOne`), none the simultaneous-existence statement.
- `msearch.py loogle "CategoryTheory.InjectiveResolution, CategoryTheory.ShortComplex"`:
  no hits.
- `msearch.py leansearch "Simultaneously resolve a short exact triple by injective
  cochain complexes with biproduct middle terms"`: unavailable, Internal Server Error;
  no inferred verdict for this failed service.
- `msearch.py grep "ShortComplex|biprod" "CategoryTheory/Preadditive/Injective"`:
  eleven hits about injective-object biproduct instances and exactness of one resolution,
  none this theorem.
- Direct `rg` in Mathlib's CategoryTheory and Algebra/Homology, in all
  `WeilConjectures`, and in the repository's `lean/Sheaf`, using `horseshoe`,
  `compatible.*resolution`, `resolution.*short.?exact`, and `short.?exact.*resolution`:
  only related comparison, derived long-exact-sequence, projective/free-resolution,
  and prescribed-end horseshoe material. I opened the full prescribed-end theorem:
  its IA and IC are input binders, rather than existential conclusions, so it is
  not exactly this node's statement. The source's derived long-exact-sequence file
  states `exists_rightDerived_δ_exact`, a different theorem using distinguished
  triangles, not simultaneous compatible-resolution existence. No exact existing declaration
  warrants dropping the new module. Direct declaration-name/upstream-index searches
  found no collision.

Mismatches and changes: no H3 mismatch found; no Lean or JSON change made.
The existing docstring correctly avoids the node proof's invalid second pushout:
P is split using injectivity of I_A, then embedded in I_A ⊞ I_C. Its next step uses
quotient maps followed by embeddings, rather than claiming arbitrary lifts define
compatible differentials. I checked this construction independently. The node's
last proof step mentions choices and functoriality but its statement does not assert
strict functoriality; Lean correctly does not assert it. All four proof steps have
usable natural-language counterparts in the docstring, with the source and blueprint
id. There is one named theorem with `sorry`, no definition or hollow data, and no
proved helper. The single import provides every notion used; namespaces, line lengths,
and all explicit binders/universes satisfy the conventions.

Validation: independently compiled the unchanged module with `scompile.py`; the
recorded `lean.statement` was checked against the file's complete signature.
