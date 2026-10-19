## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.EllCohomologicalDimensionComparison`,
as `AlgebraicGeometry.ProEtale.ellCohomologicalDimension_etale_comparison`.
All theorem proofs are `sorry`; all definitions have real data. No item statement
correction, new node, or disputed statement is needed.

Hypotheses and clauses, in the order of the node:

- A fixed prime is `(ℓ : ℕ) (hℓ : ℓ.Prime)`. The qcqs scheme is
  `(S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]`.
  The qcqs morphism is `(g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]`.
  No compactness or quasi-separatedness is assumed of X or Y separately.
  A nonnegative integer c is `(c : ℕ)`, covering exactly the specified integers c ≥ 0.
- All sheaves have coefficients `AddCommGrpCat.{u + 1}` on the recorded small sites.
  This is the coefficient size of the recorded derived-section and direct-image APIs,
  with object universe u+1 and morphism universe u for the site; no site universe
  equality is imposed. Cohomology degrees are `q : ℕ`, cast to integer degrees.
- The local primary condition is `CategoryTheory.IsEllPowerTorsion F ℓ`.
  Its diagram is r ↦ `kernelSubobject ((ℓ ^ r) • 𝟙 F)` followed by
  `Subobject.underlying`, with actual subobject-inclusion arrows. Its cocone is the
  kernel inclusions into F. `Nonempty (IsColimit (ellPowerKernelCocone F ℓ))`
  says that this canonical cocone is colimiting. This is precisely the condition
  that the map from any chosen colimit to F is invertible, by the colimit universal
  property; it introduces neither another arbitrary object nor a stronger global
  sectionwise torsion condition. In sheaves the colimit sheafifies the sectionwise
  union, so exponents may vary on a cover.
- Clause 1 is the first conjunct: for every étale abelian F₀ and pro-étale abelian F,
  the recorded `ProEtale.IsClassical` on its underlying set sheaf, and
  `Nonempty (F ≅ (comparisonUpperStar AddCommGrpCat S).obj F₀)`, imply exactly
  `IsEllPowerTorsion F ℓ ↔ IsEllPowerTorsion F₀ ℓ`.
  `Nonempty` here packages the given isomorphism hypothesis, not a construction.
- Clause 2 is `ellCohomologicalDimension S ℓ = ellEtaleCohomologicalDimension S ℓ`.
  The right side is literally `sSup` of the natural degrees q in `ℕ∞` admitting
  a primary torsion F₀ with nontrivial
  `(Etale.cohomology AddCommGrpCat S q).obj ((DerivedCategory.singleFunctor _ 0).obj F₀)`.
  A group is nonzero precisely when its carrier is not `Subsingleton`.
- Clause 3 is `ellRelativeCohomologicalDimension g ℓ =
  ellEtaleRelativeCohomologicalDimension g ℓ`. Its right side is `sSup` of the
  same natural degrees admitting a primary torsion étale F₀ on X with
  nonzero q-th cohomology sheaf of
  `(Etale.lowerStar AddCommGrpCat g).rightDerivedFunctor.obj (single 0 F₀)`.
  This uses the recorded direct image, derived on the unbounded category then
  evaluated on a sheaf in degree zero; its bounded-below restriction is the
  recorded `Etale.rightDerivedLowerStarPlus`.
- Clause 4 is `S.HasTorsionEtaleCohomologicalDimensionLE c →
  ellCohomologicalDimension S ℓ ≤ c`, with the precise recorded ordinary
  derived-section, locally torsion predicate. It is not a bound on an unrelated
  cohomology theory or on uniformly annihilated sheaves.

Dependency declarations read and used:

- `def-sc-etale-torsion-cd`: `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`,
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `sk-def-pe-classical-definition`: `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`,
  `AlgebraicGeometry.ProEtale.IsClassical`; its complete continuity-map definition
  was read, including the affine-presentation index and section universes.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `AlgebraicGeometry.Scheme.proEtaleSiteComparison` and its coefficient interpretation.
  `ProEtale.comparisonUpperStar` is the same canonical Kan-extension/sheafification
  construction on abelian coefficients, from the imported upstream Comparison.Defs.
- `sk-def-cd`: supplied dependency module described below; its actual pro-étale
  definitions are used on the left sides, not replaced by the étale suprema.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`; its derived forms were read in
  `Derived.UpperLowerStarCoherence`.
- `def-weil-pbc-scheme-conventions` is a collector with no declaration of its own;
  the standard Mathlib Scheme, compactness, quasi-separatedness and morphism
  property declarations render its hypotheses.
- The additional dependency module imports the recorded
  `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage` and uses the
  canonical upstream `ProEtale.lowerStar`, together with its total derived functor.
  The annihilator construction uses Mathlib `kernelSubobject`,
  `le_kernelSubobject`, `Subobject.underlying` and `IsColimit`; no replacement
  kernel, colimit, classicality or comparison functor is introduced.

Edge cases checked mathematically before writing:

- r=0 gives the kernel of the identity, hence zero; including it does not change
  the filtered union. There is no fixed exponent on the entire sheaf.
- Zero coefficients, the empty scheme, and a morphism with empty source contribute
  no nonvanishing degrees. The supremum is zero in `ℕ∞`, including for c=0.
- Infinite disjoint unions allow a section with unbounded orders; the colimit
  predicate permits it when it is locally in the union. No global-section torsion
  or finite-cover condition was substituted.
- Identity morphisms and degree zero are included. Higher images are sheaves,
  so vanishing is `IsZero`; ordinary cohomology groups use `Subsingleton`.
- There is no invertibility assumption on ℓ in the base; the characteristic-ℓ case
  and all primes are retained. The relative comparison assumes only g qcqs.
- The suprema are in `ℕ∞`, so unbounded dimensions are permitted.

Searches, with results saved by the prescribed wrapper in searches.jsonl:

- LeanFinder: “comparison between etale and proetale ell power torsion
  cohomological dimensions”: eight unrelated ring-theoretic étale results, no match.
- Loogle: quoted `"cohomologicalDimension"`: zero hits.
- LeanSearch: “A sheaf of abelian groups is locally killed by powers of a prime
  and its cohomological dimension on the etale and proetale sites agrees”:
  Sheaf.H, Grothendieck abelian/sheaf category and sheafification results, no match.
- msearch grep `cohomologicalDimension|CohomologicalDimension` in
  `AlgebraicGeometry/Sites`: zero Mathlib hits.
- msearch grep `IsPrimaryTorsion|IsTorsion|torsionBy|torsion.*[Ss]heaf` in
  `CategoryTheory`: zero Mathlib hits.
- Direct rg in the upstream WeilConjectures and project Sheaf sources for primary
  torsion and cohomological dimension found the all-torsion étale invariant,
  classical uniform bounds, and full-cohomological-dimension bounds, which have
  different input sheaves. No existing primary classical supremum or four-clause
  comparison was found. The item id and proposed declaration names have no hits.
- Live source fallback confirmed
  `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension` is a
  Leray factorization/bound for all pro-étale coefficients, not this primary invariant.
  Its finite-coefficient derived global-section definition was read and reused.

Compilation: both delivered modules compiled individually and in dependency order
through scompile.py, without errors or warnings. The legacy pro-étale Derived.LowerShriek
import duplicated a declaration from the published FiniteCoefficient variant; the
latter is now imported. The proof-only recorded module
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` itself imports both variants
through its dependency closure and fails with duplicate
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`.
It is omitted from these imports; the exact comparison source and its proof use remain
in the theorem docstrings, and the usable smaller canonical coefficient interfaces
are imported. No shared or upstream file was edited. The absent Lean declaration for
`sk-thm-pe-direct-image-comparison` is not imported as a nonexistent module; its
mathematical use is recorded in the proof docstrings, as in the DAG.

## Dependency modules

`sk-def-cd` had neither a Lean record nor a Mathlib match, so the human's bottom-up
instruction requires supplying it here. Only its lean field is changed. The module
`Sheaf.AlgebraicGeometry.EllCohomologicalDimension` defines the genuine annihilator
kernel diagram, canonical cocone and primary condition, the two pro-étale suprema,
and the corresponding étale suprema. Its `lean.declarations` lists every helper.
It also states, with sorry proofs, the node's comparison and finite-type finiteness
clauses. Source: the current blueprint sk-def-cd unit and its complete six-step DAG
proof, read before writing. This adds no independent notion or duplicate DAG node.

The dependency's hypothesis/clause correspondence is as follows. ℓ is a natural prime
in each theorem. The annihilator convention is `IsEllPowerTorsion` as detailed above.
Its absolute formula is `ellCohomologicalDimension`; its relative formula is
`ellRelativeCohomologicalDimension`. Each quantifies q : ℕ and all classical primary
abelian sheaves on the recorded pro-étale site. All suprema use `sSup` in ℕ∞.
For a field the expression is the same definition applied to `Spec (.of K)`; no
second field invariant is introduced. The comparison clause is
`ellCohomologicalDimension_comparison`, assuming the stated qcqs S and g.
The final clause is `ellCohomologicalDimension_finite_of_finiteType`: K is an
arbitrary `Field` in universe u, its primary dimension is assumed `< ⊤`, S,X,Y
are schemes over `Spec K`, and their structure morphisms are locally of finite
type and quasi-compact. The morphism g is any K-morphism. The conclusion states
both absolute S dimension and relative g dimension are `< ⊤`. No stronger all-torsion
field bound, finite extension, separation, or source/target extra hypothesis is added.
The canonical formulas are defined for arbitrary schemes and morphisms; the comparison
and finite-type assertions impose exactly the hypotheses in the node.

## Second reading by Q121

I reread the source node `det-cd-etale-comparison` and the complete Stacks/blueprint
source place before checking the Lean signature. The objects and hypotheses render as
follows, and each verdict is pass:

- The prime is `(ℓ : ℕ)` with `hℓ : ℓ.Prime`; this is rendered by the first two
  binders of `ellCohomologicalDimension_etale_comparison` and is used by every
  `IsEllPowerTorsion ℓ hℓ` predicate. The qcqs scheme is
  `(S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]`; the qcqs morphism is
  `{X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]`. No separate
  compactness or separation assumptions on `X` or `Y` are introduced. The integer is
  `(c : ℕ)`, and the final implication has exactly `c` as its bound.
- Clause 1 quantifies the étale sheaf `F₀` and pro-étale sheaf `F` in
  `AddCommGrpCat.{u + 1}`, assumes `IsClassical` of the underlying sheaf and
  `Nonempty (F ≅ comparisonUpperStar ... S |>.obj F₀)`, and concludes the exact
  iff `IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ F₀`. The comparison functor is
  the recorded canonical one; no arbitrary map or chosen isomorphism is substituted.
- Clause 2 is rendered by
  `cohomologicalDimension ℓ hℓ S = etaleCohomologicalDimension ℓ hℓ S`. The
  canonical dependency defines both suprema over natural degrees (empty supremum
  zero) and exactly the local annihilator-colimit convention.
- Clause 3 is rendered by equality of `relativeCohomologicalDimension ℓ hℓ g` and
  the explicit canonical étale `sSup` over `q : WithTop ℕ`, `n : ℕ`, étale sheaves,
  `IsEllPowerTorsion ℓ hℓ`, and nonzero homology of the recorded étale derived
  lower-star. This is the relative étale supremum in the landed `sk-def-cd`
  declaration; the dependency has no separate named relative-etale definition.
- Clause 4 is exactly
  `S.HasTorsionEtaleCohomologicalDimensionLE c →
  cohomologicalDimension ℓ hℓ S ≤ c`, with no extra finiteness or characteristic
  hypothesis.

The canonical dependency declaration `AlgebraicGeometry.ProEtale.cohomologicalDimension`
(and its sibling declarations) was read in
`Sheaf.AlgebraicGeometry.CohomologicalDimension`. It is the landed `sk-def-cd`
interface and has the same kernel-colimit torsion notion, site universes, degree range,
and qcqs hypotheses. The worker sandbox also contained a private duplicate module
`EllCohomologicalDimension.lean` with a second `IsEllPowerTorsion` and alternate
cohomological-dimension names. That was a mismatch with H4 after `sk-def-cd` landed;
I removed the duplicate module and its copied dependency node, and changed the item
module imports and signature to use the canonical landed declarations. No definition
or theorem from that duplicate is delivered.

Edge cases were checked: `r = 0` gives the kernel of the identity; zero and empty
schemes give empty nonvanishing sets and supremum zero; `q = 0` is included; identity
and empty-source morphisms satisfy the same relative statement; no invertibility of
`ℓ` or restriction on characteristic is assumed; unbounded suprema remain `⊤`; and
there is no uniform exponent requirement. Universe parameters use one `u`, with
coefficient category `AddCommGrpCat.{u + 1}` and the recorded pro-étale site
universes.

The existing searches in `searches.jsonl` were independently checked (LeanFinder,
Loogle, LeanSearch, and Mathlib/project `rg` searches). They find no declaration of
this four-clause comparison. A direct search does find the landed
`CohomologicalDimension.lean`; that is the dependency `sk-def-cd`, not this comparison
node, so the item remains new. No item statement correction, new definition node, or
additional dependency repair is needed.

Compilation with `scompile.py Q121 det-cd-etale-comparison` succeeds for the item file
against the landed canonical dependency. The only change in this second reading is the
replacement of the stale private dependency copy by the landed `sk-def-cd` interface,
with the corresponding canonical names and explicit relative étale supremum.
