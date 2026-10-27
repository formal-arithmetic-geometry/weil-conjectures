## Worker report

The module `Sheaf.Paper.ChartCartesianDomain` states
`WeilConjectures.PurityFiniteSetting.chartCartesianDomain`, with its proof `sorry`.
Its accompanying real definition `ChartCartesianDomainConclusion` writes the entire
conclusion with canonical Mathlib scheme pullbacks and their maps. It has no
postponed proof or chosen data. The main theorem has no let binders in its signature;
local names in the definition's body unfold normally when proving it.
No node statement, dependency list, or proof was changed. No new or repaired nodes
are required. There is no STATEMENT-DISPUTED issue.

I read the current source at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md`,
Step 1, and the node's seven expanded proof steps. The source identifies the
inverse image of the affine-space diagonal with U×_A U and removes precisely its
off-diagonal component. The conclusion implements that construction, including
its scheme structure and the graph factorization, rather than just a pointwise
inverse-image equality. The expanded finiteness and relative-dimension checks
are retained. The recorded source is the earlier snapshot of this same proof.
There is no repair note for this item.

Hypotheses are rendered as follows:

| Node hypothesis | Lean rendering |
| --- | --- |
| k is the fixed algebraic closure of F_q | `P : PurityFiniteSetting.{u}`, with `P.field.k` from `FiniteFieldDatum` |
| ell is prime and distinct from char(k) | the recorded `P.coefficients` datum |
| n≥1, finite coefficients, E=Q_ell | `P.level`, `P.level_pos`, and `_hE : P.extension = ⊥`; the bottom intermediate field expresses exactly E=Q_ell |
| X,Y finite type over k | `aY : Y ⟶ Spec (.of P.field.k)` with `LocallyOfFiniteType aY` and `QuasiCompact aY`; X's structure map is `f ≫ aY`, finite type by the assumed finite type of f |
| f smooth, separated, finite type, pure relative dimension d≥0 | `d : ℕ`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `[SmoothOfRelativeDimension d f]`; the last class includes smoothness |
| j:U↪X open | `U : X.Opens`, with canonical open immersion `U.ι` |
| A=A^d_Y and its projection p | `AffineSpace (ULift.{u} (Fin d)) Y` and its existing canonical structure map `A ↘ Y` |
| e:U→A étale over Y | `(e : U.toScheme ⟶ AffineSpace ... Y) [Etale e]` and `w : e ≫ p = U.ι ≫ f` |
| h=fj=pe | the local name `h := U.ι ≫ f`, and w; composition is written left to right in Lean |
| every affine open V⊂Y | `∀ V : Y.Opens, IsAffineOpen V → ...` in the conclusion |

Conclusion clauses, in the order of the node:

| Node clause | Lean rendering in `ChartCartesianDomainConclusion` |
| --- | --- |
| Y,X,U,A Noetherian | `∀ T ∈ [Y, X, U.toScheme, A], IsNoetherian T` |
| h and e separated of finite type | each has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` conjuncts |
| indicated open inclusions quasi-compact and finite type | `QuasiCompact` and `LocallyOfFiniteType` for `U.ι`, `V.ι`, `jV`, the three pullback first projections (X_V⊂X, U_V⊂U, A_V⊂A), the clopen diagonal in Z, and `O.ι` |
| X_V=f⁻¹V, U_V=U∩X_V | `XV := pullback f V.ι`, `UV := pullback h V.ι`; `jV` is the canonical induced map UV→XV |
| A_V=A^d_V | `AV := pullback p V.ι`, the canonical base-change presentation of affine space supplied by def-sbc-affine-space and `AffineSpace.isPullback_map` |
| restricted coordinate map | `eV` is `pullback.map` of e and identity maps, with commutativity obtained directly from w and category identity equalities |
| W=U_V×_V U_V, W_A=A_V×_V A_V | `b := eV ≫ pV`, `W := pullback b b`, `WA := pullback pV pV`; pullback.map's second-projection identity gives b=hV, so these are the stated products |
| V,X_V,U_V,A_V and both products separated finite type over k | the `Over.mk` list has exactly their specified structure maps, each with `IsSeparated T.hom ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom` |
| all specified maps to V and both projections smooth of dimension d | the seven `SmoothOfRelativeDimension d` conjuncts for fV,hV,pV and the two projections of W and of WA |
| no absolute separatedness assumption on Y | there is no `IsSeparated aY` or `Y.IsSeparated` hypothesis |
| Z=U_V×_{A_V}U_V⊂W | `Z := pullback eV eV`, `z := pullback.mapDesc eV eV pV`, and `IsClosedImmersion z` |
| diagonal U_V→Z clopen | `IsOpenImmersion (pullback.diagonal eV)` and `IsClosedImmersion (pullback.diagonal eV)` |
| its off-diagonal complement closed in W | `IsClosed (z '' (Set.range (pullback.diagonal eV))ᶜ)` |
| O is its complementary open neighbourhood of the diagonal | `∃ O : W.Opens` with carrier exactly `(z '' (Set.range (pullback.diagonal eV))ᶜ)ᶜ`, and `∃ δ` with `δ ≫ O.ι = pullback.diagonal b` |
| q=(e_V×e_V) restricted to O étale | `ee` is the canonical product map, and `Etale (O.ι ≫ ee)` |
| displayed diagonal square Cartesian as schemes | `IsPullback δ eV (O.ι ≫ ee) (pullback.diagonal pV)` |
| p_U the first projection, smooth separated finite type of dimension d | the four property conjuncts for `O.ι ≫ pullback.fst b b` |
| closed section Δ_U | `IsClosedImmersion δ` and `δ ≫ (O.ι ≫ pullback.fst b b) = 𝟙 UV` |
| factorization changes second coordinate, then first | r and s are the two canonical `pullback.map` arrows and `O.ι ≫ ee = (O.ι ≫ r) ≫ s` |
| first arrow is étale over U_V | `Etale (O.ι ≫ r)` and the explicit equality of its first projection with p_U |
| second arrow is the base change of e_V | `IsPullback (pullback.fst b pV) s eV (pullback.fst pV pV)` |
| inverse image of graph u↦(u,e_Vu) precisely Δ_U | `graph := pullback.lift (𝟙 UV) eV ...` and `IsPullback δ (𝟙 UV) (O.ι ≫ r) graph` |
| all local schemes separated finite type over k | the same `Over.mk` list also includes Z and the intermediate product M; the final three conjuncts give these properties for O |

The equality fixing O's carrier specifies the exact complement from the source.
The diagonal factor δ is unique because O.ι is an open immersion. Both IsPullback
assertions express universal properties in Scheme, including nilpotents, rather
than assertions only about points. All maps in the factorization are prescribed
by canonical pullback constructions. There is no arbitrary comparison-map input
and no Nonempty choice used to manufacture data.

Dependency interfaces read and used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, its recorded finite-field and coefficient
  datum, level and intermediate field. The surrounding functor conventions are
  not additional hypotheses of this geometric lemma.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, and the canonical `Scheme.Opens.ι`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`, `pullback.mapDesc`,
  `pullback.lift`; diagonals and `CategoryTheory.IsPullback` come through the
  scheme pullback API. Products are taken in Scheme, not in topological spaces.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with
  null declaration/module. Its listed notions use their recorded nodes below.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `Smooth` and `SmoothOfRelativeDimension`; the latter is used for every dimension assertion.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-sbc-affine-space` is a Mathlib leaf: its `mathlib_match` is `AffineSpace`,
  `Mathlib.AlgebraicGeometry.AffineSpace`. `ULift.{u} (Fin d)` has exactly d coordinates,
  retaining the scheme's universe; no AffineSpace notion is redefined.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  using its recorded `IsSeparated` notion (closed-immersion diagonal).
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
  Finite type is precisely their conjunction, not just local finite type.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `IsLocallyNoetherian`; the conclusion uses `IsNoetherian`, which also includes
  quasi-compactness, as required by the node.

The proof-plan imports include the recorded
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
(`AffineSpace.smoothOfRelativeDimension_over`),
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
(`smooth_and_fibre_dimension_zero_of_etale`), and
`Sheaf.AlgebraicGeometry.UnramifiedMorphism` (`IsUnramified`).
All remaining proof dependencies are Mathlib matches or their already imported
statement modules. Explicit additional imports cover Affine, QuasiCompact,
QuasiSeparated, FinitePresentation, Separated and Immersion. The seven natural-language
proof steps in the theorem docstring follow all seven steps of the DAG proof,
with the same dependency names.

Edge cases checked before and after writing:

- d=0: the coordinate type is empty and affine space is canonically the base;
  a separated étale cover may have several sheets. Its off-diagonal Z components
  must be removed. The carrier formula removes them, rather than silently taking
  O=W, so the Cartesian square still holds.
- U empty or V empty: the pullbacks and diagonal domains are empty. The exact
  complement still defines an open subscheme, and no nonempty/inhabited hypothesis
  is introduced. Empty affine opens are permitted by `IsAffineOpen`.
- e an open immersion: Z is its diagonal and the off-diagonal complement is empty,
  so O is all of W, as in the source.
- Non-separated Y: e.g. a finite-type doubled-origin base is allowed. Finiteness
  gives Noetherianity globally; absolute separation is asserted only after choosing
  an affine V. No global absolute-separatedness assumption has slipped in.
- Nonreduced schemes and arbitrary universes: the geometry uses scheme pullbacks
  and IsPullback, not products of underlying sets; the universe u is arbitrary,
  and the coordinate lift does not restrict it.

Searches (all against the prescribed read-only live source/Mathlib):

- `msearch.py ... leanfinder "An etale separated morphism has a cartesian diagonal
  square on the complement of the off-diagonal component of its fibre product"`:
  8 hits, including `FormallyUnramified.isOpenImmersion_diagonal`,
  `IsSeparated.isClosedImmersion_diagonal`, and scheme étale pullbacks. None states
  the complete neighbourhood construction or the chart-domain conclusion.
- `msearch.py ... loogle "pullback.diagonal, IsPullback, IsOpenImmersion"`:
  0 hits (the remote Loogle index does not recognize `pullback.diagonal`).
- `msearch.py ... grep "diagonal.*[Ee]tale|[Ee]tale.*diagonal" AlgebraicGeometry`:
  6 hits in Etale and WeaklyEtale. These concern diagonal properties, not the node's
  complete statement.
- `rg -n 'cartesian.*[Dd]iagonal|diagonal.*[Nn]eigh|chartCartesian|chart_cartesian|lem-pur-chart-cartesian-domain'
  lean/Sheaf lean/WeilConjectures`: found the downstream chart proof reference and
  unrelated diagonal-neighbourhood text, no existing declaration of this result.
- `grep -rn 'lem-pur-chart-cartesian-domain' lean/WeilConjectures`: no matches.
- `rg -n 'ChartCartesianDomainConclusion|chartCartesianDomain'` on Mathlib,
  upstream WeilConjectures, project Sheaf and `dag/lean_names_upstream.json`:
  no existing declaration or name collision.

Validation: the first server `scompile.py` pass compiled both the sandbox and its
library module cleanly. After trimming unnecessary local Noetherian conjuncts,
the compiler identified an unused XV name; it was made explicit in fV's type.
The final version compiled cleanly in both server presentations (4.2 s and 6.2 s).
`deliver2.py --no-push` passed the preflight and its per-file compile, printing
`OK (dry run)` for commit `4f17c1c7281`. Only the lean field differs from the base
node; the recorded theorem signature matches the module verbatim, and every Lean
line is at most 100 characters. The only sorry is the named main theorem.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
