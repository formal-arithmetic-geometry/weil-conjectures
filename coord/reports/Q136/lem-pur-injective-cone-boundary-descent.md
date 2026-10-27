## Worker report

The module `Sheaf.CategoryTheory.InjectiveConeBoundaryDescent` states
`CategoryTheory.Functor.exists_injectiveConeBoundaryDescent`, with one `sorry`.
Its five helper definitions construct the derived-unit comparison, cone coordinates,
cohomology of the signed roof, diagonal cone map, and a predicate packaging the
row-level assertions. They use real data and existing canonical constructions.
No new node, dependency repair, or statement correction is needed.

Hypotheses and clauses, matched against the node:

| Node text | Lean rendering |
| --- | --- |
| Commutative ring A | `{A : Type r} [CommRing A]`; coefficients are `ModuleCat.{m} A`. |
| Abelian C with enough injectives | `{C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]`. |
| Chosen derived categories / size convention | Independent `[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{z} (ModuleCat.{m} A)]`; no equalities between ring, module, object, morphism or localization universes. |
| Three additive functors | `S F G : C ⥤ ModuleCat.{m} A` and the three `.Additive` instances. Left exactness is not imposed. |
| Natural u,v and vu=0 | `ι : S ⟶ F`, `π : F ⟶ G`, `w₀ : ι ≫ π = 0`. Lean composition is in diagram order. |
| Short exact on every injective object | Hypothesis `h`, quantified over `J` with `[Injective J]`, says the corresponding `ShortComplex` is `.ShortExact`. No split or objectwise exactness assumption on all of C. |
| Bounded-below injective complex I; functors termwise | `I : CochainComplex.Plus C`, `[∀ n : ℤ, Injective (I.obj.X n)]`, and the recorded `injectiveBoundaryRow S F G ι π w₀ I`. |
| P is Cone(u), coordinates (b,a), differential (db+u(a),-da) | Mathlib `CochainComplex.mappingCone R.f`, `injectiveConeVector R n b a`, and the first conjunct of `InjectiveConeRowProperties`. Mathlib stores the shifted S summand first; the helper explicitly writes the F coordinate first as in the node. |
| q(b,a)=v(b); negative projection | Second conjunct of `InjectiveConeRowProperties`: `descShortComplex` evaluates to `R.g.f n b`, and the third cone-triangle arrow evaluates to `-a` through the actual shift-coordinate isomorphism. |
| q is a quasi-isomorphism | Third conjunct, `QuasiIso (CochainComplex.mappingCone.descShortComplex R)`. |
| Roof (-pr) q inverse | The existing `DerivedCategory.triangleOfSESδ hR`, defined in Mathlib as `inv (Q.map q) ≫ Q.map triangle.mor₃ ≫ (Q.commShiftIso 1).hom.app _`. No arbitrary morphism replaces the roof. |
| Natural RG to RS[1] on D+ | Existential `β : G.rightDerivedFunctorPlus ⟶ S.rightDerivedFunctorPlus ⋙ shiftFunctor (DerivedCategory.Plus (ModuleCat A)) 1`. A natural transformation includes naturality for every derived morphism. |
| Descent by right-derived-unit identifications | `injectiveConeModelIso` is the quotient comparison followed by the actual `rightDerivedFunctorPlusUnit` and `RT.mapIso e`. The third main conjunct requires the β/roof comparison for every injective I, every K, and every specified `e : Q.obj I ≅ K`. This universal normalization gives independence of representatives, including changes of resolution. |
| Cohomology equals normalized injective snake boundary | Existential `δ`, `InjectiveBoundaryNormalized S F G ι π w₀ h δ`, the next conjunct identifying δ with the shifted cohomology of β, and the row equality `injectiveConeHomology R hR n = hR.δ n (n+1) rfl`. |
| Every integer n and every cycle c has a lift b | Final conjunct of `InjectiveConeRowProperties`, with arbitrary `n : ℤ`, `c`, cycle equation `hc`, and existential b. |
| For every lift b there is a unique a with u(a)=db; a is closed | `∃! a, R.f.f (n+1) a = R.X₂.d n (n+1) b`, followed by an explicitly quantified a with that equation and `∃ ha'` asserting its cycle equation. |
| Positive formula [c] maps to [a] | Equality applying `injectiveConeHomology` to `homologyπ (cyclesMk c ...)`, with RHS `homologyπ (cyclesMk a ...)`, without a minus sign. |
| Independence of lift and cocycle representative; A-linearity | The formula holds for every b and a satisfying the equations and factors through Mathlib's actual homology modules. `injectiveConeHomology` is a `ModuleCat` morphism, hence A-linear and defined on cohomology classes; boundaries have the same image. |
| Chain h induces diagonal cone map | `injectiveBoundaryConeMap` uses Mathlib `mappingCone.map` with `S(h)` and `F(h)` and the naturality of ι. The fourth main conjunct states its coordinate action. |
| Commutes with q and negative projection | Next two equalities of chain maps in the fourth main conjunct; the target of the third triangle arrow is the actual shifted S complex. |
| Cohomology boundary square commutes | The `∀ n` equality in that same conjunct, between `homologyMap G(h) ≫ boundary` and `boundary ≫ homologyMap S(h)`. |
| Comparisons depend only on homotopy class | For every homotopic b', `Nonempty (Homotopy (coneMap b) (coneMap b'))` and equality of their images under `DerivedCategory.Plus.Q`. The recorded functorial homotopy and homology lemmas apply to S,F,G and the displayed chain squares. |
| Every derived morphism between represented objects lifts, uniquely up to homotopy | Last main conjunct, for arbitrary I,J,K,L,e,e',f: existence of b with `Q.map b ≫ e'.hom = e.hom ≫ f`, and a homotopy to every other b' satisfying that equation. |

Dependency declarations used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-sp-injective-resolutions`, `def-sp-enough-injectives`:
  `CategoryTheory.Injective`, `EnoughInjectives` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`; injective models here are
  bounded-below complexes of injectives, without choosing an extra resolution.
  `InjectiveResolution` in `.Resolution` is the dependency's object-resolution notion.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. The node assumes additivity only.
- `lem-weil-pbc-right-derived-plus-injective`: `Functor.rightDerivedFunctorPlus`
  and `rightDerivedFunctorPlusUnit` in
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, with unit
  invertibility on injective complexes supplied by `.DerivabilityStructureInjectives`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  The signed cone convention is `CochainComplex.mappingCone.triangle` in
  `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone` and `.Pretriangulated`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus` in
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`; its Q and homology
  interfaces are in `.Plus`.
- `lem-pur-derived-injective-boundary`: import
  `Sheaf.CategoryTheory.DerivedInjectiveBoundary`; use its actual
  `injectiveBoundaryRow`, `injectiveBoundaryRow_shortExact`,
  `InjectiveBoundaryNormalized`. The auxiliary `injectiveConeModelIso` is the
  derived-object comparison whose homology is its `injectiveHomologyModelIso`.
  Its existing `exists_injectiveBoundary` supplies the normalized cohomology target.

Proof dependencies are imported through the recorded modules:
`CochainComplex.mappingCone.quasiIso_descShortComplex` in
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact` (publicly reached via
`.DerivedCategory.ShortExact`); `ShortComplex.ShortExact.δ` and
`homology_exact₁/₂/₃` in `.HomologySequence` (reached via the dependency module);
`Homotopy.homologyMap_eq` and `Functor.mapHomotopy` in `.Homotopy`;
`DerivedCategory.Plus.exists_injective_nonempty_iso` in
`.DerivedCategory.DerivabilityStructureInjectives`;
`CochainComplex.IsKInjective.Qh_map_bijective` and
`DerivedCategory.Plus.Qh_map_bijective_of_isKInjective` in
`.DerivedCategory.KInjective` and `.Plus`. The theorem docstring includes all six
proof steps, including the cone homotopy `(F(k),-S(k))`.

Searches (2026-10-22; the msearch receipts are in sandbox `searches.jsonl`):

- Loogle via msearch: `"mappingCone", "homologySequenceδ"` returned
  `CochainComplex.mappingCone.homologySequenceδ_triangleh`, a cone cohomology
  component, without the functor-row descent theorem.
- LeanFinder via msearch: “A short exact row of additive functors on injective
  objects has signed mapping cone connecting map with positive cocycle lift
  formula descending naturally to bounded below derived category” returned eight
  cone/derived-triangle/K-injective components, including `DerivedCategory.triangleOfSESδ`.
- Mathlib grep via msearch: `homologySequenceδ_triangleh|descShortComplex|triangleOfSESδ`
  in `Algebra/Homology` found 19 component hits. These canonical definitions are reused.
- LeanSearch via msearch: “Signed mapping cone boundary for a row of additive
  functors exact on injective objects descends to bounded below derived category
  with positive lift formula” returned eight mapping-cone component declarations,
  including `mappingCone`, `liftCochain`, and `mapTriangleIso`; no whole theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `injective.cone|injectiveCone|ConeBoundary|coneBoundary` found related specialized
  support/internal-Hom cones, not this abstract theorem. Exact node-id grep in
  `lean/WeilConjectures` gave no match. Exact searches for all six new names in
  both library roots and `dag/lean_names_upstream.json` gave no match.

Edge cases checked mathematically before finalizing:
zero coefficient ring, zero functors and zero row; S=0 or G=0 (zero boundary);
a nonsplit short exact module row (no splitting assumed); all integer degrees,
including negative ones and the lower bound; shifted injective representatives;
distinct coefficient/module/category/localization universes. For the sign,
`(b,-a)` is the closed cone representative and negative projection gives `+a`.
Changing b by u(t) changes a by dt; changing c by de can be lifted by changing b
by df. The formula therefore has exactly the required quotient independence.

Validation: scompile.py compiled both its sandbox module and the named library
module cleanly (8.5 s and 10.8 s), with no warnings. The only source edits needed
by compilation were replacing two non-definitional successor equalities in
`cyclesMk` with `ComplexShape.next_eq' _ rfl`.

No statement dispute or node fault found. The node copy changes only `lean`.

## Second reading by Q136

Reread the source node, the complete Lean module, the recorded boundary module,
and the Stacks 014Z/070I/070J text. The dispatcher prohibits spawning another
agent; this is the worker's second pass, and the maintainer's independent review
remains separate. The table above checks every hypothesis and clause.

Particular checks: no left-exactness or split-row hypothesis was added; the row
is exact only on injectives. The normalization quantifies over every specified
injective representative, rather than only a chosen one. The main conclusion
is a derived natural transformation as well as its cohomology transformations.
The canonical roof is Mathlib's actual negative-projection roof. The component
formula has positive [a], and the cone coordinates explicitly reverse Mathlib's
stored summand order. Linear maps of genuine homology modules render both
linearity and independence of representatives. The final universal lift clause
includes uniqueness up to homotopy. No mathematical mismatch was found; the two
successor-equality elaboration repairs change no mathematical content.
