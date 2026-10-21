## Worker report

The module `Sheaf.SixFunctors.FiniteProperClassicalAmplitude` states
`AlgebraicGeometry.ProEtale.finiteProper_classical_amplitude`. Its only new declaration
is a theorem with proof `sorry`; it introduces no definitions, instances or assumptions
of derived functor properties. The node changes only in `lean`. There is no statement
correction, dependency repair, new node or mathematical dispute.

### Hypotheses and every conclusion clause

| Node text | Lean rendering |
| --- | --- |
| Finite commutative coefficient ring with its discrete topology | `(A : Type u) [CommRing A] [Finite A]`. The canonical constant-sheaf construction supplies exactly discrete coefficients: there is no alternative coefficient topology or continuity hypothesis. |
| A morphism of schemes, proper | `{X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]`. |
| Natural uniform fibre bound | `(e : ℕ)` and `_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T), topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)`. This quantifies over every base change and every point, not only geometric fibres or the original base. |
| Ordinary constant-A module sheaves and their unbounded derived categories | `Scheme.proEtaleDerivedCategory X A` and `Scheme.proEtaleDerivedCategory Y A`. The abbreviation unfolds to `DerivedCategory (SheafOfModules …)` over the sheafified constant ring, with `HasDerivedCategory.standard`; there is no completion, boundedness or constructibility restriction. |
| Total K-injective direct image G | `Scheme.proEtaleConstantDerivedDirectImage f A`, definitionally `(Scheme.proEtaleConstantModuleDirectImage f A).rightDerivedFunctor`. Underived pushforward is the existing canonical sectionwise pushforward through the constant-section scalar map. |
| Common universe and all small indexing families | Scheme universe `u`, coefficient/module universe `u+1`, and independently quantified family universe `w`. The pro-etale site's object universe is `u+1` and its morphism universe is `u`; neither is collapsed. Countable families at any universe shrink to countable sets. Coproduct preservation is asserted for every existing ambient coproduct indexed by `I : Type w`, with no demand for nonexistent larger coproducts. In the stipulated common universe the standard sheaf/derived coproducts exist. |
| Integer shifts | `Nonempty ((Scheme.proEtaleConstantDerivedDirectImage f A).CommShift ℤ)`. This is coherent shift compatibility, not isolated arbitrary object isomorphisms. |
| Triangulatedness | `(Scheme.proEtaleConstantDerivedDirectImage f A).IsTriangulated`, with the canonical right-derived `CommShift` instance exported by the existing right-derived triangulated module. |
| Countable products, including canonical projections | `Nonempty (HasCountableProducts …)` for both derived categories and `∀ (I : Type w) [Countable I], PreservesLimitsOfShape (Discrete I) G`. Mathlib preservation means that every limiting cone remains limiting after applying G; its legs are literally G of the original projections. It therefore gives exactly the canonical product comparison. Product existence is a conclusion, not a hypothesis. |
| Every integer a, every L, lower bound preserved | `∀ (a : ℤ) (L : Scheme.proEtaleDerivedCategory X A), L.IsGE a → (G.obj L).IsGE a`. No classicality or upper bound is imposed. |
| Every integer b, every classical-cohomology L, sharp upper bound | `∀ (b : ℤ) (L : Scheme.proEtaleDerivedCategory X A), IsClassicalModuleComplex L → L.IsLE b → (G.obj L).IsLE (b + 2 * (e : ℤ))`. There is no lower bound, bounded representative or essential-image restriction on L. |
| Higher small-etale images of every module sheaf, q > 2e | `∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} (ULift.{u+1,u} A))) (q : ℤ), 2 * (e : ℤ) < q → IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj ((Etale.rightDerivedLowerStarPlus … f).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))`. This is precisely the recorded definition of `R^q f_* F`, not merely global cohomology. |
| Standard t-structure inequalities | `DerivedCategory.IsGE` and `DerivedCategory.IsLE`, defined from `DerivedCategory.TStructure.t`; `isGE_iff`/`isLE_iff` identify these with the required cohomology-sheaf vanishing. |
| No quasi-compactness of Y or ground-field bound | There are no base-field, `CompactSpace Y`, `QuasiCompact (𝟙 Y)` or cohomological-dimension hypotheses. |
| Total etale direct image E on unbounded constant-A modules | `Etale.rightDerivedLowerStar (ModuleCat.{u+1} (ULift.{u+1,u} A)) f`, the existing total K-injective right derived functor. |
| Every small ambient coproduct with canonical components | `∀ I : Type w, PreservesColimitsOfShape (Discrete I) E`. Its image cocone has legs `E.map` of the original coprojections, so the induced comparison from the coproduct of the images to E of the coproduct is canonical and invertible. The index type can be empty and all complexes are unbounded ambient objects. |

The same canonical coefficient lift `ULift.{u+1,u} A` occurs on both sites:
`Scheme.proEtaleDerivedCategory` already uses this lift in its definition. It therefore
uses the identical coefficient ring as the etale `ModuleCat` presentation, rather than
an unrelated ring or a new universe equality. A finite ring in any larger universe
can be represented in the chosen universe; no finite ring or characteristic is excluded.

### Recorded dependency declarations used

- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Its locally-finite-type formulation
  is the node's finite-type formulation because universal closedness implies
  quasi-compactness, as its record explains.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  Its recorded convention identifies the scheme base change with `Limits.pullback`
  and the structure projection with `pullback.snd`; those are the operations used
  in the fibre-bound hypothesis. Its `moduleBaseChange` declaration concerns the
  additional module clause of that dependency and is not substituted for a scheme.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`. Its codomain is exactly `WithBot ℕ∞`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
  exports `finiteCoefficientRingSheaf`, `FiniteCoefficientModules` and
  `FiniteCoefficientDerivedCategory`. Their construction was read; the present node
  explicitly asks for ordinary constant-ring modules. It uses the existing
  `Scheme.proEtaleDerivedCategory`, with the finite discrete comparison identified
  in proof step 1, instead of making a second continuous-function or module category.
- `sk-def-sfb-derived-categories`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
  As its existing record specifies, in these Grothendieck categories the upstream
  `rightDerivedFunctor` is the same total K-injective construction with its canonical
  universal unit. The existing constant derived direct image uses that construction.
- `sk-def-pe-classical-definition`: `AlgebraicGeometry.ProEtale.IsClassicalModuleComplex`
  (and `IsClassicalModuleSheaf`), `Sheaf.SixFunctors.ClassicalDefinition`.
  It checks every derived cohomology sheaf using the underlying set-sheaf continuity
  predicate. It is not replaced by boundedness or an etale-complex realization.
- `def-sbc-standard-tstructure-derived-category`: Mathlib match
  `DerivedCategory.TStructure.t`, `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  with `DerivedCategory.IsLE`, `DerivedCategory.IsGE` and their cohomology equivalences.
- `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` reexports
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the Mathlib derived categories,
  single functors and homology functors on sheaves valued in `ModuleCat.{u+1}`.
  The statement uses exactly that encoding, with the same canonical lifted ring.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`,
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The latter module also supplies the total `rightDerivedLowerStar` used for E.
- Canonical pro-etale G:
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
  This existing interface is the canonical direct image of
  `def-weil-pbc-proetale-operations`; it needs no arbitrary coefficient identification.

Every recorded proof-dependency module is directly imported. For the Mathlib-only
`lem-pc-separated-quasi-separated`, its match
`AlgebraicGeometry.IsSeparated.instQuasiSeparated` is supplied by the explicit
`Mathlib.AlgebraicGeometry.Morphisms.Separated` proof import. The eight-step theorem
docstring follows the node's entire proof: resolutions and exactness; products;
lower bounds; torsion etale bound; classical heart comparison; bounded devissage;
unbounded-below truncation; and the etale coproduct criterion. No proof dependency
is silently removed or replaced by a new assumption.

### Source and edge-case checks

Read the exact blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md`.
The source specifies the uniform bound `2d`, unbounded coproducts and transfer.
Also read Stacks' local statements for Tags 095U (torsion etale higher-image bound),
0D6J (module/abelian derived comparison), 0F0D (proper direct sums), and the
products/truncation passages referenced in the node. The node's explicit K-injective
product argument does not assume that products of arbitrary sheaves are exact.

Checked: the zero ring is allowed (no `Nontrivial A`); empty schemes and empty fibres
are allowed (`topologicalKrullDim = ⊥`); `e=0` gives exact amplitude zero rather than
an artificial positive bound; arbitrary signs of a and b are allowed; zero complexes
and vanishing intervals are allowed; `q=2e` is deliberately not covered by the strict
higher-image bound; the upper bound never requires L bounded below; countable product
indices may be finite or empty; arbitrary coproduct indices may be empty. Neither
coefficient characteristic nor invertibility on the schemes is assumed. The same e
is required on all base changes, including the identity.

### Searches for an existing declaration

All service searches used the prescribed `msearch.py` wrapper with group Q52 and item
`lem-sfb-finite-proper-classical-amplitude`:

- LeanFinder query: "Proper direct image for finite coefficients has amplitude zero
  to twice the fibre dimension on classical proetale complexes and preserves products".
  Eight hits, headed by `Condensed.profiniteSolid`, a properness instance for Proj,
  and affine-transition-limit declarations. None states the proper derived amplitude.
- Loogle query: `DerivedCategory, "IsLE"`. Twelve hits, including
  `DerivedCategory.IsLE`, `DerivedCategory.isLE_iff`, the single-functor bound and
  bounded-representative interfaces. These are useful vocabulary, not this theorem.
- Mathlib grep query:
  `proper.*amplitude|finiteProper.*amplitude|[Pp]roper.*[Cc]ohomological`.
  Zero hits.
- LeanSearch query: "A proper morphism with universally bounded fibre dimension has
  cohomological amplitude zero to twice the dimension on classical proetale complexes
  with finite constant coefficients". Eight hits, all properness/etale infrastructure,
  including `IsProper`, `isProper_eq` and stability under base change. No match.
- Project/upstream `rg` queries:
  `finite-proper-classical-amplitude|classical.*[Aa]mplitude|finiteProperClassical|ClassicalCohomology`
  and `finiteProper_classical_amplitude|finiteProper.*amplitude|proper.*classical.*amplitude`
  on `lean/Sheaf` and `lean/WeilConjectures`. No existing declaration for this node.
  The nearby `openDirectImage_classical_amplitude` concerns open immersions of
  finite-type schemes over a field, not proper arbitrary schemes; the generic
  `RightDerivedFunctorUpperBound` alone does not contain this assembled conclusion.
- The prescribed `grep -rn 'lem-sfb-finite-proper-classical-amplitude'
  lean/WeilConjectures` returned no hit.

Read the matching candidates and interfaces, especially
`FiniteProperClassicalTruncation`, `FiniteCohomologicalDimensionDirectImageCoproducts`,
`ProperTorsionDirectImageBound`, `ProEtaleConstantDerivedDirectImage`,
`ProEtaleDerivedCategory`, `ClassicalDefinition`, and the right-derived triangulated
module. These provide the ingredients, not a duplicate of the assembled statement.

### Validation

The prescribed `scompile.py Q52 lem-sfb-finite-proper-classical-amplitude …` checked
the sandbox and final module on the live server successfully (21.6 s and 18.7 s).
No errors or warnings were emitted. Every universe and variable is explicitly bound,
`autoImplicit` is false, and all Lean lines are at most 100 characters. The subsequently
added explicit separatedness proof import is included in delivery preflight's fresh
per-file compilation. No direct Git command, global build, live source edit or tool
modification was performed.

Initial delivery preflight found two formatting issues: the recorded signature included
the `:=` delimiter, and `by` was placed on its own line. The record now stops before
`:=`, and the theorem ends with the required `:= by` followed by `sorry`. Its Lean
type and mathematical content are unchanged.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
