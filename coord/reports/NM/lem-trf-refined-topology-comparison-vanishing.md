## Worker report

Repaired immutable returned head `8062e98f86a4`, including the expressly requested
repair of proof prerequisite `lem-trf-comparison-induction-step` (H3/H6 and its
original H11 defect). The retained item statement and all its hypotheses are
unchanged. Both delivered node files are refreshed from the shared DAG and changed
only in `lean`; the delivery wrapper rebases these records on current main.

The item module is `Sheaf.TraceFormula.RefinedTopologyComparisonVanishing`.
The prerequisite module is `Sheaf.TraceFormula.ComparisonInductionStep`, whose main
declaration is `CategoryTheory.RefinedTopologyComparison.comparisonInductionStep`.
It states exactly `(V_r) → (V_{r+1})`, including all degrees up to `r + 1`.
Each theorem has `sorry` as its whole proof, as required for stage 2.

The canonical helpers `abelianSheafify`, `geometricDirectAdditive`, `relocalization`,
`comparisonDirect`, `comparison`, and `sliceComparison` retain their full names in
`CategoryTheory.RefinedTopologyComparison`. They now belong to the induction
prerequisite's module and `lean.declarations`. The item imports that module because
its statement uses these helpers. This gives one copy of each construction and
keeps imports acyclic. All helper data is constructed from existing APIs.

Source reopened: `literature/stacks-project/sites-cohomology.tex`,
`section-compare`, `section-compare-general`, `situation-compare` (Tag 0EZ3),
`lemma-induction-step-V-C-general` (Tag 0EZE), and `lemma-V-C-all-n-general`
(Tag 0EZF). The item's first assertion is `(V_n)` for every n. The induction
prerequisite has precisely the same slice sites, weak Serre conditions, and five
hypotheses. Its docstring contains all thirteen expanded DAG proof steps, including
the canonical augmentation compatibility and boundary-map argument.

The following table applies to the common hypotheses of BOTH declarations; its
last two rows describe the item. The additional induction binders are detailed below.

Every object, hypothesis, and conclusion is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Category small in the fixed universe | `{C : Type u} [SmallCategory C]`; coefficients are `AddCommGrpCat.{u}`. Sheaf objects consequently live in the next universe. |
| Two site structures | `(τ τ' : Precoverage C)` and the recorded site predicate in `hτsite : τ.IsSiteForCoverings` and `hτ'site : τ'.IsSiteForCoverings`. |
| Every τ′ covering is a τ covering | `hτ : τ' ≤ τ`, an inclusion of the actual covering presieves. |
| Slice objects and morphisms | Mathlib `Over X`, used by `τ.toGrothendieck.over X` and `τ'.toGrothendieck.over X`. |
| Underlying families determine slice coverings | Mathlib `GrothendieckTopology.over`; its `mem_over_iff` gives precisely the underlying covering-sieve condition. |
| Comparison geometric morphism ε_X | The constructed `sliceComparison τ τ' hτ X`, using the recorded `GeometricMorphism` structure on abelian sheaf categories. |
| Comparison direct image is identity on underlying presheaves | `comparisonDirect J K h := ObjectProperty.ιOfLE ...`; it changes only the sheaf-condition proof, retaining the underlying functor and natural transformation. |
| Comparison inverse image is τ sheafification | `comparison.inverse := sheafToPresheaf K AddCommGrpCat.{u} ⋙ presheafToSheaf J AddCommGrpCat.{u}`. The adjunction is the restriction of `sheafificationAdjunction J ...` along the fully faithful inclusion of coarser sheaves. |
| Relocalization inverse image | `relocalization J f` has inverse `J.overMapPullback AddCommGrpCat.{u} f`, i.e. precomposition with `Over.map f`. |
| Relocalization direct image | `sheafPushforwardCocontinuous` of `Over.map f`, the right Kan extension, with its existing `sheafAdjunctionCocontinuous`. No pullbacks outside those required in hypothesis (1) are assumed. |
| Ordinary higher direct images using injective resolutions | Mathlib `Functor.rightDerived` is used both in `hderivedImage` and the conclusion. Grothendieck abelian sheaf categories supply enough injectives and injective resolutions. |
| Morphism class P | `P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop`. |
| Full subcategories A′_X | The object-property family `A' : ∀ X, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop`; it imposes no restriction on morphisms between members. |
| Contains zero | `hzero : ∀ X, A' X 0`. |
| Closed under isomorphisms | `hiso`, transferring membership along `Nonempty (H ≅ K)`. |
| Kernels of maps between its objects | `hkernel` quantifies over all H, K and f, assumes membership of both objects, and concludes `A' X (kernel f)`. |
| Cokernels of maps between its objects | `hcokernel`, with the same membership hypotheses and `cokernel f`. |
| Extensions | `hextension` takes a `ShortComplex`, `S.ShortExact`, and membership of `S.X₁` and `S.X₃`, and concludes membership of `S.X₂`. |
| (1) Pullbacks exist for P arrows along arbitrary arrows | `hbaseChange` quantifies over f in P and every g, then asserts `∃ h : HasPullback f g, ...`. |
| (1) Base-change projection belongs to P | Under that `HasPullback` witness, `letI := h; P (pullback.snd f g)`. |
| (2) All relocalization inverse images preserve A′ | `hrelocalization`, for every f, H, and `A' Y H`, concludes membership of `(relocalization ... f).inverse.obj H`. |
| (3) Every A′ object is already a τ sheaf | `htauSheaf` concludes `Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj`. |
| (4) Higher P-direct images preserve A′, including degree zero | `hderivedImage` takes `P f`, `A' X H`, and every `i : ℕ`, and concludes membership of the canonical direct image's `rightDerived i`. |
| (5) Every actual τ covering | `hrefinement` quantifies over U, any `I : Type u`, U₀ and a, assuming `Presieve.ofArrows U₀ a ∈ τ U`. It does not replace actual coverings by arbitrary generated covering sieves. |
| (5a) First τ′ covering | Existential J, V and v, with `Presieve.ofArrows V v ∈ τ' U`. |
| (5b) Middle singleton τ coverings in P | W and w with `∀ j, Presieve.singleton (w j) ∈ τ (V j) ∧ P (w j)`. |
| (5c) Last τ′ coverings | Dependent K, Z and z with `∀ j, Presieve.ofArrows (Z j) (z j) ∈ τ' (W j)`. |
| (5d) Refinement through each original family member | For every j and k, `∃ i b, z j k ≫ w j ≫ v j = b ≫ a i`. |
| A_X is the essential image of A′_X | `hH` says `∃ H', A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')`. This is written inline, without a second definition of essential image. |
| Every integer n ≥ 0, object X and member H | `(n : ℕ) (X : C) (H : Sheaf ...)` and `hH`. Natural numbers exactly parametrize the nonnegative integers here. |
| R^i ε_{X,*} H = 0 for 1 ≤ i ≤ n | `∀ i : ℕ, 1 ≤ i → i ≤ n → IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H)`. |

Dependency records and source declarations were read:

- `def-weil-size-convention` has the existing metatheoretic convention record,
  with no Lean declaration; the explicit universes implement it.
- `def-weil-pbc-sites-and-cohomology`: module
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, declaration
  `CategoryTheory.Precoverage.IsSiteForCoverings`. Actual covering presieves use
  this predicate; sheaf categories use its prescribed `toGrothendieck` topology.
- `def-trf-geometric-morphism`: module
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`, declaration
  `CategoryTheory.GeometricMorphism`, with inverse, direct, adjunction, and
  left-exactness fields. The canonical comparison and relocalization fill all
  four fields with the existing functors and adjunctions.
- `def-weil-pbc-sheafification`: module
  `Mathlib.CategoryTheory.Sites.Sheafification`, recorded declarations
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction`; the construction uses the functor and adjunction.

Additional APIs read and used include Mathlib's `Sites.Over`, `CoverLifting`,
`Adjunction.Restrict`, `Abelian.RightDerived`, the Grothendieck-abelian sheaf
and enough-injectives instances, and upstream
`GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian` from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`.
The named `abelianSheafify` instance is a direct application of this existing
result in universe u, not a new sheafification construction. The additive
instance is the existing additivity result for right adjoints between abelian
categories, applied to the geometric-morphism adjunction.

Edge cases checked against the written type and source:

- n = 0 gives the empty interval; the conclusion makes no degree-zero claim.
  Conversely, hypothesis (4) does include degree zero.
- Empty C is allowed. Empty covering index types I, J and K j are allowed.
  For I empty, the final factorization clause forces the composite-index
  family to be empty, exactly as refinement of an empty family requires.
- Zero sheaves and arbitrary isomorphic representatives are included.
  Kernel/cokernel closure only concerns maps between two members; no stronger
  Serre condition on every subobject or quotient was imposed.
- Hypothesis (1) does not impose global pullbacks, and (2) has no P restriction.
- Singleton covers, repeated indices, identical τ and τ′, and n = 1 introduce
  no special restrictions. All families remain within the given small universe.

Searches for an existing statement and its constructions:

- `msearch.py ... leansearch "Higher right derived images of the comparison of
  a finer and coarser topology vanish under weak Serre and three-stage
  refinement hypotheses"`: 8 hits, including `Functor.rightDerived`,
  `Presieve.isSheaf_of_le`, and unrelated derived-functor comparisons; no theorem
  with these five hypotheses.
- `msearch.py ... leanfinder "Vanishing of higher direct images for comparison
  of two topologies under weak Serre and refinement hypotheses"`: generic site
  and sheafification APIs, not this vanishing assertion.
- `msearch.py ... loogle "CategoryTheory.GrothendieckTopology,
  CategoryTheory.Functor.rightDerived"`: zero hits.
- `msearch.py ... grep "comparison.*[Vv]anish|[Ww]eakSerre" CategoryTheory`:
  zero hits.
- `rg` for the item id, `weakSerre`, and `refinedTopologyComparison` in
  upstream `WeilConjectures` found no match; in `lean/Sheaf` the weak-Serre hit
  was a scheme-specific module, not this general comparison theorem.
- Reading declarations under upstream `CategoryTheory/Sites` and side-project
  `CategoryTheory/Sites`, together with Mathlib's sheafification, continuous,
  cover-lifting, and slice-site sources, identified the existing generic
  constructors used here. The landed `PhBigEtaleTorsionAcyclicity` module is a
  scheme-specific application, not a replacement for this general theorem.

No statement dispute or source mismatch remains. Both genuine proofs are intentionally
postponed in this stage; no hollow definitions are left.

## Dependency modules

`lem-trf-comparison-induction-step`: the returned interface allowed an arbitrary
family `rightDerived`, arbitrary `ε`, arbitrary pullback/direct-image operations,
and sheaves on the unsliced sites. The saved attempted repair still allowed
arbitrary geometric morphisms and arbitrary comparison isomorphisms and encoded
(3) merely as essential-image membership. These interfaces do not state the DAG
node. The replacement constructs every operation canonically and uses actual slice
categories. `htauSheaf` is the required sheaf condition on the underlying presheaf.
`hderivedImage` and all vanishing claims use `Functor.rightDerived` of those actual
direct-image functors. No new compatibility hypothesis is assumed: the specified
adjunctions fix the units and counits used by the source's canonical comparisons.

The common binders are exactly those in the clause table above. The remaining
induction clauses are:

| Dependency clause | Lean rendering |
| --- | --- |
| Every nonnegative r | `r : ℕ` |
| Every object X and finer sheaf H in A_X | Quantification over `X`, `H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}`, followed by an existential `H'`, membership `A' X H'`, and `Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')` |
| `(V_r)` | `hr` quantifies over every such X and H and every `i : ℕ`, and asserts `IsZero` for `1 ≤ i` and `i ≤ r` |
| `(V_{r+1})` | The conclusion repeats exactly the same X, H, essential-image condition and actual direct-image derived functor, replacing only `i ≤ r` by `i ≤ r + 1` |

For r = 0, `hr` has an empty positive interval while the conclusion really demands
degree-one vanishing of the canonical inclusion's derived functor. It cannot be
falsified by choosing an unrelated constant `rightDerived` family because that
binder no longer exists. For higher r the conclusion explicitly retains the old
degrees. Empty categories, empty covering families, the zero class, equal topologies,
and arbitrary isomorphic representatives remain allowed. Pullbacks are requested
only by (1), with no global pullback class added. The item can use the induction
statement with its hypotheses verbatim and the same helper definitions.

The prerequisite includes proof-only imports for the recorded modules of
`lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`,
`lem-weil-pbc-cohomology-over-object-localization`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-weil-pbc-complex-injective-resolution-mono`,
`lem-weil-pbc-derived-direct-image-triangulated`, and
`lem-sp-long-exact-of-triangle`. The existing sheafification, geometric-morphism,
and site-covering modules are already public imports needed by the signature.
The remaining proof nodes have no recorded Lean module in the current shared DAG.

There are no new independent definition nodes and no natural-language statement
corrections. No citer's DAG fields are changed. Searches for the induction statement
recorded in its node and the retained Q30 report returned only generic site,
local-injectivity and Dold–Kan results, with no exact theorem. Current `rg` of the
upstream library and project `lean/Sheaf` for `comparisonInductionStep` and
`CategoryTheory.RefinedTopologyComparison` found no usable published declaration
of the induction theorem. The failed arbitrary-interface attempt is superseded.

## Second reading by NM

This is a self-check by the same worker, not an independent-agent review; the
brief forbids subagents. I reopened both final files and both current DAG nodes,
and checked every common binder against the clause table above. The maintainer's
independent review follows delivery.

This reading identified the errors that the saved attempted dependency repair
had retained: ε acted on unsliced sheaf categories, the compatibility isomorphisms
were arbitrary, and `hsheaf` asserted essential-image membership rather than the
τ sheaf condition. I replaced that entire interface with the item's already
canonical constructions. I checked the τ′ ≤ τ direction, slice `Over X` types,
identity-on-presheaves inclusion, sheafification adjunction, relocalization
precomposition and right Kan extension, and ordinary right derived functors.

I checked zero and isomorphism closure separately, membership of both objects in
the kernel/cokernel assumptions, `ShortExact` for extensions, the direction of
`pullback.snd`, the unrestricted relocalization hypothesis, the all-degree
quantifier in (4), and all three covering clauses and the factorization equation
in (5). Both occurrences of A_X in the induction statement use the same
isomorphism-invariant essential-image condition as the item. `hr` is universal
over X and H; it is not merely a pointwise induction assumption. The conclusion
is the whole interval through r + 1. No epsilon, relocalization, comparison
isomorphism or right-derived family remains an unconstrained input.

I also checked ownership: the canonical helper definitions occur once, in the
prerequisite module, with source/blueprint docstrings; the parent's public import
is needed by its signature. The prerequisite does not import the parent. Each
node's `lean.statement` is copied verbatim from its final theorem signature.
Both theorem proofs remain `sorry`. Compilation and delivery validation use only
the authorized `scompile.py` and `deliver2.py` wrappers, per file, without a global
build or direct shared-repository changes.

Final `scompile.py` verification compiled both delivered files separately, in
prerequisite order, in their sandbox and library forms. Every invocation was below
the 60-second limit; the final library checks took 20.9 s and 19.0 s. There were no
errors or warnings. A local text/JSON check confirmed one whole-proof `sorry` per
file, no line over 100 characters, both `lean.statement` values verbatim, and no
DAG field changes outside `lean` relative to the refreshed shared nodes.
