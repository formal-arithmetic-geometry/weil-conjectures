## Worker report

The module states `AlgebraicGeometry.isOpenImmersion_of_fpqcPrecoverage_pullback`,
the descent direction of Stacks Project, Descent, Lemma 35.23.18 (Tag 02L3).
Its proof is `sorry`. The local `literature/stacks-project/descent.tex` checkout is
absent on this machine; I read the Stacks Project's Tag 02L3 page instead:
https://stacks.math.columbia.edu/tag/02L3 .

Statement correspondence, clause by clause:

- Schemes `Y` and `T`, with `φ : Y ⟶ T`, are `{T Y : Scheme.{u}} (φ : Y ⟶ T)`.
- The arbitrary index set and the scheme family `T_i` are `{I : Type v}` and
  `(T' : I → Scheme.{u})`; the arrows `h_i : T_i ⟶ T` are `(h : ∀ i, T' i ⟶ T)`.
- The family being an fpqc covering is
  `(hh : Presieve.ofArrows T' h ∈ Scheme.fpqcPrecoverage T)`. Mathlib's
  `fpqcPrecoverage` is the matched notion for the dependency's Stacks covering.
- Each chosen fiber product `Y_i` is `(Y' : I → Scheme.{u})`; its two projections
  are `(p : ∀ i, Y' i ⟶ Y)` and `(φ' : ∀ i, Y' i ⟶ T' i)`.
- `(hp : ∀ i, IsPullback (p i) (φ' i) φ (h i))` states commutativity and the
  universal property of each chosen square. It permits any choice of fiber product.
- The hypothesis that every `φ_i` is an open immersion is
  `(hφ' : ∀ i, IsOpenImmersion (φ' i))`; the conclusion is `IsOpenImmersion φ`.

Dependency declarations used: `AlgebraicGeometry.Scheme` and its categorical
hom from `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme.fpqcPrecoverage`
from `Mathlib.AlgebraicGeometry.Sites.Fpqc`; `CategoryTheory.IsPullback` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs` (equivalent to
the chosen `CategoryTheory.Limits.pullback` and its projections); and
`AlgebraicGeometry.IsOpenImmersion` from `Mathlib.AlgebraicGeometry.OpenImmersion`.
The two direct imports expose these declarations.

Edge cases checked: `I` may be empty. When `T` is empty, its empty family can
cover it and the result is consistent: any scheme over empty `T` is empty, so
its map to `T` is an open immersion. An empty family cannot cover a nonempty
`T`. Empty `Y` is allowed, and its map to `T` is an open immersion. No affine,
Noetherian, characteristic, or nonemptiness hypothesis is added. The universe
`v` is arbitrary for the index type.

Searches for an existing declaration:

- `msearch.py leanfinder "if all base changes along an fpqc covering family of
  schemes are open immersions, the morphism is an open immersion"`: eight hits,
  including `IsOpenImmersion.of_openCover_source`, none the fpqc family theorem.
- `msearch.py loogle "IsOpenImmersion.DescendsAlong, Scheme.fpqcPrecoverage,
  Presieve.ofArrows"`: no hits; the first identifier was not recognized by Loogle.
- `msearch.py grep "descendsAlong_isOpenImmersion|fpqcPrecoverage|
  of_isPullback_of_ofArrows_mem_fpqcTopology" AlgebraicGeometry`: nine hits;
  `FlatDescent` has the single morphism descent instance, not this family form.
- `rg` over Mathlib `AlgebraicGeometry`: `FlatDescent.lean` has descent along a
  single surjective, flat, quasi-compact morphism; no exact family statement.
- `rg` and `grep -rn` over `WeilConjectures`: found the general descent lemma
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`, but no open-immersion
  specialization and no occurrence of this node id.
- `rg` over the project's `lean/Sheaf`: no matching declaration.

The generic source lemma uses membership in the generated fpqc topology and
extra property instances; it is not itself the statement of this node, whose
hypothesis is membership in the fpqc precoverage.

## Second reading by H1

Independent reading of the node statement, its source place, the dependency records,
and `lean/Sheaf/AlgebraicGeometry/Morphisms/FpqcOpenImmersionDescent.lean`:

- The morphism of schemes `φ : Y ⟶ T` is rendered by `{T Y : Scheme.{u}}`
  and `(φ : Y ⟶ T)`. Verdict: exact objects and category; no added assumptions.
- The index set and covering family `I` and `T_i` are rendered by
  `{I : Type v}` and `(T' : I → Scheme.{u})`. Verdict: arbitrary index universe,
  including the empty index type.
- The covering arrows `h_i : T_i ⟶ T` are rendered by
  `(h : ∀ i, T' i ⟶ T)`, and the fpqc hypothesis by
  `(hh : Presieve.ofArrows T' h ∈ Scheme.fpqcPrecoverage T)`. Verdict: exact
  Mathlib fpqc precoverage notion; no stronger singleton or affine assumption.
- The fibre-product schemes `Y_i` and projections `p_i : Y_i ⟶ Y`,
  `φ_i : Y_i ⟶ T_i` are rendered by `(Y' : I → Scheme.{u})`,
  `(p : ∀ i, Y' i ⟶ Y)`, and `(φ' : ∀ i, Y' i ⟶ T' i)`. Verdict: exact
  family of chosen fibre products.
- The pullback/commutativity and universal-property clause is rendered by
  `(hp : ∀ i, IsPullback (p i) (φ' i) φ (h i))`. Verdict: exact categorical
  pullback condition, with no omitted square condition.
- The premise that every `φ_i` is an open immersion is rendered by
  `(hφ' : ∀ i, IsOpenImmersion (φ' i))`. Verdict: exact universal quantifier.
- The conclusion that `φ` is an open immersion is rendered by
  `: IsOpenImmersion φ`. Verdict: same conclusion, with no weakening or
  strengthening and the same quantifier order.

Edge cases: `I` may be empty (then the stated covering hypothesis controls when
the case is possible); `Y` and `T` may be empty schemes; no nonemptiness,
Noetherian, affine, quasi-separated, characteristic, or finiteness assumption is
introduced; and `u` and `v` remain independent universes. The zero/empty source
case is represented by the ordinary scheme morphism and `IsOpenImmersion`.

Searches were independently checked with `rg` over the project and source trees,
Mathlib's `FlatDescent.lean` and `OpenImmersion.lean`, and the recorded
LeanFinder/Loogle searches. The only nearby result is
`AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`,
which is the single-morphism property instance, not this fpqc covering-family
statement. No exact declaration exists in Mathlib or `WeilConjectures`.

Mismatch review: no mathematical or typing mismatch was found, so the theorem
signature and node `lean.statement` were left unchanged. The only repair was
replacing this handoff marker with this independent item-by-item reading.
