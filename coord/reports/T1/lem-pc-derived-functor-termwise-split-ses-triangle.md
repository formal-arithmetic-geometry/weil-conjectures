## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle` states
`AlgebraicGeometry.RingedSpace.derivedModuleDirectImage_termwise_split_ses_triangle`.
Its only theorem has proof `sorry`. Three data definitions give the identity-resolution
comparison, the localized shift comparison, and the triangle appearing in the conclusion;
they contain no postponed proof or arbitrary choice of comparison maps.

Hypotheses and clauses, in the order of the node:

- A morphism of ringed spaces is `g : X ⟶ Y`, for `X Y : RingedSpace.{u}`.
  The categories are `SheafOfModules.{u} (moduleRings X)` and the analogous category on Y.
  The explicit `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wY}` binders allow chosen
  morphism universes for both localizations. `moduleDirectImage g`, its
  `mapHomologicalComplex (ComplexShape.up ℤ)`, and `derivedModuleDirectImage g` are precisely
  the recorded direct and derived images, not newly defined functors.
- The complex sequence is `S : ShortComplex (CochainComplex ... ℤ)`.
  Its maps i and p are `S.f` and `S.g`; the zero composite is part of `ShortComplex`.
  `hS : S.ShortExact` says it is short exact, equivalently degreewise short exact.
  `_hSplit` asserts `Nonempty` of the evaluated short complex's `Splitting` for each
  integer n. This asks for existence degreewise, not for compatible chain-map splittings.
- All three complexes are K-injective through `[S.X₁.IsKInjective]`,
  `[S.X₂.IsKInjective]`, and `[S.X₃.IsKInjective]`.
- Q is `DerivedCategory.Q`; delta is the recorded `DerivedCategory.triangleOfSESδ hS`.
  It has codomain `(Q.obj S.X₁)⟦1⟧`, rather than `Q.obj (S.X₁⟦1⟧)`; the formula therefore
  explicitly uses Q's inverse shift comparison before applying phi of the shifted complex.
- `derivedModuleDirectImageKInjectiveIso g K` is phi_K: it is the inverse of
  `rightDerivedFunctorUnit` at the homotopy class of K, composed only with the existing
  `quotientCompQhIso` and `mapHomotopyCategoryFactors` identifications. The unit is an
  isomorphism on K-injectives, so this is exactly computation by the identity resolution.
  It does not choose an unrelated isomorphism from the dependency's `Nonempty` theorem.
- The conclusion first supplies `hImage` proving short exactness of the termwise image
  sequence, then degreewise existence of `Splitting` for this same sequence.
- The next conjunct is `(S.X₁⟦(1 : ℤ)⟧).IsKInjective`. Mathlib supplies this shift instance,
  so phi of the shifted complex is already well typed without an extra hypothesis.
- The shift equality of complexes is rendered by the canonical `commShiftIso` having
  identity components in every degree. The shift differential is the negative original
  differential; the additive termwise functor commutes with it. The node's equality is
  thus represented by its canonical identity-component isomorphism, without demanding
  equality of category objects that Mathlib implements up to isomorphism.
- The next two equalities say `Rg(Qi) ≫ phi₂.hom = phi₁.hom ≫ Q(g_*i)` and the analogous
  equality for p, with Lean's left-to-right composition convention.
- The third equality says `Rg(delta) ≫ Rg(Q.shift.inv) ≫ phi_{I₁[1]}.hom ≫ beta.hom =
  phi₃.hom ≫ delta'`, where delta' is `triangleOfSESδ hImage` and beta is
  `moduleDirectImageLocalizedShiftIso`. Beta consists of Q applied to the termwise shift
  isomorphism followed by Q's shift isomorphism. These are exactly the canonical shifts
  suppressed in the node's notation, with no use of an unspecified shift on Rg.
- `derivedModuleDirectImageSplitTriangle g S hS` is the triangle whose first two maps
  are `Rg(Qi)` and `Rg(Qp)` and whose third map is the previous left-hand composite
  followed by `(shiftFunctor _ 1).map phi₁.inv`. This is the stated transported third map.
- The existential `e` is an isomorphism of this triangle to `triangleOfSES hImage`;
  three equalities fix its components to phi₁, phi₂ and phi₃, respectively.
  The final conjunct puts this precise triangle in `distTriang`. This includes the
  connecting-map conclusion of the node, rather than just existence of some triangle.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `AlgebraicGeometry.RingedSpace.moduleDirectImage`, its additive instance,
  `derivedModuleDirectImage`, and its K-injective computation semantics.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`,
  `Qh`, `quotientCompQhIso`, and the shift/triangulated instances (mathlib match of
  `def-weil-abstract-derived-category`).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` (recorded
  `def-pc-cochain-complex-modules`).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`
  and its shift instance (mathlib match of `def-pur-kinjective-complex`).
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: `triangleOfSESδ`, `triangleOfSES`
  (recorded `lem-weil-pbc-complex-ses-triangle`).
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`, `distTriang`
  and triangle isomorphism closure (mathlib match of `def-weil-triangulated-category`).
- The comparison uses `CategoryTheory.Functor.rightDerivedFunctorUnit` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, already
  imported by the recorded direct-image module, and Mathlib's `mapHomotopyCategoryFactors`.

Edge cases checked: the zero sequence gives the zero triangle and zero connecting map;
a sequence split as complexes has zero connecting map, while merely degreewise split
sequences need not. No boundedness, termwise injectivity, exactness of g-star, or chain-map
splitting is imposed. Empty ringed spaces and arbitrary integer degrees remain allowed.
The morphism g need not preserve acyclic complexes: K-injectivity is used for the derived
comparison, and only split exactness is used to preserve the sequence. The canonical
cone sign is inherited from Mathlib's `triangleOfSESδ`, not independently selected.

Sources opened: https://stacks.math.columbia.edu/tag/0152 (canonical natural boundary with
cone map -p) and https://stacks.math.columbia.edu/tag/079V (unbounded derived direct image
computed by K-injective resolutions). The local Stacks TeX is absent on this machine.
No statement correction, disputed statement, new node, or dependency module is needed.
The module docstring contains all three proof steps and their cited DAG nodes.

Searches made:

- `msearch.py leanfinder`: "right derived direct image identifies the triangle and connecting
  morphism of degreewise split short exact K-injective complexes". Eight hits, including
  `triangleOfSESδ`, `triangleOfSESIso`, and single-object triangles; none gives this comparison.
- `msearch.py loogle`: `DerivedCategory.triangleOfSESδ, CochainComplex.IsKInjective`:
  zero hits.
- `msearch.py leansearch`: "right derived functor preserves connecting morphism of split exact
  complexes": service unavailable, Internal Server Error.
- `msearch.py grep`: `rightDerived.*(triangle|SES)|triangleOfSES.*map|DegreewiseSplit` in
  `Algebra/Homology`: 17 hits, notably the degreewise split boundary and SES naturality,
  but no right-derived comparison of this sequence.
- `rg` of `lem-pc-derived-functor-termwise-split-ses-triangle|termwise.split|degreewise.split`
  in the project's Lean and upstream `WeilConjectures`: no upstream match; related project
  declarations include `rightDerived_triangle_connecting`, which concerns bounded-below
  resolutions of a sequence of objects and cohomological delta functors, not this statement.
  Its full signature was read; it cannot be used as an existing record for this item.
- Read the recorded dependencies' signatures and docstrings, and searched Mathlib's
  homotopy/derived category sources for the quotient and shift comparison maps. These
  supply all the structures required, so no duplicate notion was introduced.

Validation: server single-file compile succeeded with exit code 0, no warnings.

## Second reading by T1

I independently read the node statement and the complete Lean signature. The objects and their rendering are as follows, with verdicts:

- The ringed-space morphism and coefficient categories are rendered by `g : X ⟶ Y`,
  `X Y : RingedSpace.{u}`, and `SheafOfModules (moduleRings X/Y)` with the two
  `HasDerivedCategory` binders. This is the same object and no extra geometric
  hypothesis is imposed: pass.
- The direct and derived images are the recorded `moduleDirectImage g` and
  `derivedModuleDirectImage g`; the termwise image is its
  `mapHomologicalComplex`. No private direct-image notion is introduced: pass.
- The short exact complex sequence is `S : ShortComplex (CochainComplex ... ℤ)` with
  `hS : S.ShortExact`; its maps are `S.f` and `S.g`. The hypothesis
  `_hSplit : ∀ n, Nonempty ((S.map (HomologicalComplex.eval ... n)).Splitting)` is
  precisely degreewise splitting, with no chain-level splitting added: pass.
- The three K-injective hypotheses are the independent typeclass binders
  `[S.X₁.IsKInjective]`, `[S.X₂.IsKInjective]`, and `[S.X₃.IsKInjective]`, exactly as
  required: pass.
- `DerivedCategory.Q`, `triangleOfSESδ hS`, and
  `derivedModuleDirectImageKInjectiveIso` render the localization, connecting map,
  and the identity-resolution comparison `φ_K`. The latter is defined from the
  recorded right-derived unit and quotient identifications, not an arbitrary
  isomorphism: pass.
- The existential `hImage` gives short exactness of the termwise image sequence, and
  the following `∀ n, Nonempty (...Splitting)` gives its degreewise split property.
  These are the first conclusion clauses, with the same quantifier order: pass.
- `(S.X₁⟦(1 : ℤ)⟧).IsKInjective` is the required shifted K-injectivity clause. The
  displayed `commShiftIso` component equality records the canonical identity
  components implementing `g_*(I₁[1]) = (g_*I₁)[1]`; it introduces no additional
  mathematical assumption: pass.
- The next two equalities are exactly naturality for `i` and `p`, with Lean’s
  left-to-right composition convention. The third is the connecting-map equality,
  using `moduleDirectImageLocalizedShiftIso` to expose the canonical shift
  comparison: pass.
- The existential triangle isomorphism fixes its three components to `φ₁`, `φ₂`, and
  `φ₃`, and the final membership in `distTriang` states distinguishedness. Together
  these are the consequence and connecting-map clauses of the node: pass.

Edge cases checked: the zero sequence and zero complexes are admitted; an empty
indexing situation does not occur (the degree index is all of `ℤ`); degree `n = 0`
and arbitrary integer degrees are included; no characteristic, finiteness,
Noetherian, boundedness, or nonempty-space hypothesis is present; and the two
universes are not artificially restricted beyond the common universe required by
`RingedSpace.{u}` and the explicit localization universes. Merely degreewise split
sequences are allowed, while compatible chain splittings are not silently assumed.

I searched Mathlib and the project for direct-image/derived-functor triangle and
termwise-split declarations (LeanFinder/Loogle/grep and `rg` in `WeilConjectures`
and `lean/Sheaf`). Only the recorded direct-image, derived-category, K-injective,
short-exact-triangle, and triangulated-category declarations were found; no existing
statement duplicates this node. The Stacks source places (Tags 0152 and 079V) support
additivity/naturality of the connecting morphism and K-injective computation.

No mismatch was found in the worker module or node copy. The module compiled cleanly
with `scompile.py` (exit code 0, no warnings), and no definition is hollow. The only
repair in this second reading is documentary: this section records the independent
item-by-item verification required for delivery; Lean and the node statement remain
unchanged.

## Reviewer fix (R-tst)

Two conjuncts were removed as tautological (brief: no tautological conjunct). `(S.X₁⟦1⟧).IsKInjective`
is closed by `inferInstance` (Mathlib's shift instance, HomotopyCategory/KInjective.lean), and the
`commShiftIso` component equality `... .f n = 𝟙 _` is Mathlib's `rfl` lemma
`Functor.mapHomologicalComplex_commShiftIso_hom_app_f`; even the object equality
g_*(I₁[1]) = (g_*I₁)[1] holds by `rfl`. The node's two clauses are therefore library facts, used
implicitly (the comparison for `S.X₁⟦1⟧` and `moduleDirectImageLocalizedShiftIso`); the theorem's
docstring says so. The remaining statement is unchanged.
