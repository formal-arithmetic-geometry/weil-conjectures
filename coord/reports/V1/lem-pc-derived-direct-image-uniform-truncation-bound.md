## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound` states
`AlgebraicGeometry.exists_schemeDerivedDirectImage_uniform_truncation_bound` with
one `sorry`, and defines nothing. No statement correction or added node is needed.

Hypotheses and clauses:
- Schemes and their morphism: `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Quasi-compact and quasi-separated morphism: `[QuasiCompact f] [QuasiSeparated f]`.
- Quasi-compact target: `[CompactSpace S]`, compactness of the underlying scheme space;
  there is no separation assumption on S.
- The two `HasDerivedCategory` binders provide the recorded localizations of module
  sheaves, with independent morphism universes wX and wS. They impose no boundedness.
- Objects E of D_QCoh(O_X): `E : schemeDerivedQCohCategory X`; `E.obj` is the object
  of the ambient derived category. Quasi-coherence is its full-subcategory predicate.
- A single positive integer independent of E: `∃ N : ℤ, 0 < N ∧ ∀ E, ...`.
- No positive cohomology: `∀ m : ℤ, 0 < m → IsZero ((homologyFunctor ... m).obj E.obj)`.
- Vanishing of H^m(Rf_*E) for every m ≥ N:
  `∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj)`.
- The consequence is the second conjunct: `∀ (E : schemeDerivedQCohCategory X) (q : ℤ)`
  without the first clause's cohomological boundedness assumption.
- For all sufficiently large integers n: `∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ...`.
- The canonical E → τ_{≥ -n}E is `(DerivedCategory.TStructure.t.truncGEπ (-n)).app E.obj`.
  Mapping this through `schemeHigherDirectImage f q` applies first Rf_* and then H^q;
  `IsIso` is the asserted isomorphism of O_S-module sheaves, not an unspecified
  isomorphism between its endpoints.

Dependencies read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, and `schemeDerivedQCohCategory`, using the shared
  `SheafOfModules (moduleRings X.toRingedSpace)` carrier.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` and `schemeHigherDirectImage`.
  Read their complete module and the underlying ringed-space derived construction.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`
  and its cohomological interpretation `isLE_iff` / `isGE_iff`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`: the standard t-structure's
  `truncGE` and `truncGEπ` (read the definitions and docstrings).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: Mathlib's morphism properties;
  the quasi-compact property is imported by this module.

Source checked: [Stacks Tag 08D5](https://stacks.math.columbia.edu/tag/08D5), part (2)
and the final truncation paragraph. The local Stacks checkout is absent on this
machine, so the published page was opened. The source agrees with both clauses.
The docstring carries all four proof steps, their named DAG inputs, the affine-basis
argument, and the truncation triangle / integer bound argument. The conclusion
uses an eventual threshold rather than adding an explicit numerical bound that
the node's statement does not assert.

Edge cases checked: X or S empty, the zero derived object, affine identity morphism,
negative/zero/positive q, unbounded-below E, and negative n are all admitted. The
positive N permits N=1 for affine pushforward; the conclusion does not demand
vanishing at m=0. Neither separatedness nor quasi-separatedness of S is added.
Integer thresholds express “sufficiently large integers” directly. The morphism
conditions and target compactness are genuine hypotheses, not properties of an
identity map supplied as hollow substitutes.

Searches made:
- msearch.py leanfinder: "uniform cohomological bound for derived direct image of
  quasi coherent complexes on quasi compact quasi separated schemes": eight hits,
  generic derived cohomological support, qcqs section results and quasi-coherence
  data; none states this uniform bound or truncation-map consequence.
- msearch.py loogle: "DerivedCategory.TStructure.t, IsIso, homologyFunctor": zero
  hits, unknown identifier IsIso reported by the service.
- msearch.py grep: "uniform.*truncation|derived.*direct.*image" in AlgebraicGeometry:
  zero hits.
- msearch.py leansearch: "uniform cohomological bound derived pushforward quasi
  coherent complexes": service unavailable, Internal Server Error.
- rg on WeilConjectures and lean/Sheaf for the node id and uniform truncation:
  no exact declaration. Broader "uniform.*(cohomolog|trunc)|trunc.*bound" finds
  pro-etale exceptional-adjoint bounds and QCohTruncationDerivedLimit / PerfectHomGap
  commentary, none this scheme pushforward theorem.
- `tools/lean_names_upstream.py show` for the node: no attached declaration.
- rg on Mathlib's t-structure directory finds the existing `truncGEπ` map used here;
  its source was read instead of defining a new truncation notion.

Validation: `scompile.py` now compiles the module successfully against the published dependency (`Compiled in 12.4 s`). `deliver2.py V1 lem-pc-derived-direct-image-uniform-truncation-bound --no-push` completed with `OK (dry run)`: the commit passes preflight and server compilation.

## Second reading by V1

Independent reading of the sandbox node and theorem against Stacks `perfect.tex`,
`lemma-quasi-coherence-direct-image` (Tag 08D5), obtained from the upstream Stacks
TeX source, and the published [Tag 08D5](https://stacks.math.columbia.edu/tag/08D5).
The source assumes only a quasi-compact, quasi-separated scheme morphism; part (2)
adds quasi-compactness of the target. Enlarging its integer bound to a positive
integer preserves the assertion. The final triangle gives eventual isomorphism
of the canonical map, as the node states. No statement correction is needed.

Object, hypothesis and conclusion inventory, matched independently:

- X and S are arbitrary schemes: `{X S : Scheme.{u}}`. Pass. Read
  `def-pc-scheme` and Mathlib's scheme carrier; no base field, Noetherian condition,
  nonemptiness or separation condition is supplied.
- f is their scheme morphism: `(f : X ⟶ S)`. Pass; this is Scheme.Hom.
- f is quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
  Pass. Read Mathlib's morphism classes (compact preimages and quasi-compact
  diagonal), rather than substituting compactness or separation of X or S.
- S is quasi-compact: `[CompactSpace S]`. Pass. Mathlib compactness imposes no
  Hausdorffness; this is compactness of the whole underlying scheme space.
- D_QCoh(O_X) is the full subcategory with quasi-coherent cohomology:
  `E : schemeDerivedQCohCategory X`. Pass. Opened the dependency node and
  `DerivedCategory.lean`: `schemeDerivedCategory` uses the shared module-sheaf
  category, `schemeDerivedQCohProperty` tests every integer cohomology sheaf,
  and the category is its FullSubcategory. `E.obj` is its ambient derived object.
- Derived categories are presented by the two explicit `HasDerivedCategory`
  binders, with independent `wX` and `wS`. Pass: these are localization data for
  the shared abelian categories, not boundedness or geometric assumptions.
- A positive integer bound independent of E exists:
  `∃ N : ℤ, 0 < N ∧ ∀ E : schemeDerivedQCohCategory X, ...`. Pass; a positive
  integer represented in ℤ is equivalent to a positive natural-number bound.
- Only the first clause assumes H^m(E)=0 for m>0:
  `(∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor ... m).obj E.obj))`.
  Pass: no termwise vanishing or lower boundedness is added.
- H^m(Rf_*E)=0 for every m≥N:
  `∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj)`.
  Pass. Opened `def-pc-derived-direct-image`, `SchemeDerivedDirectImage.lean`
  and `RingedSpaceDerivedDirectImage.lean`: this functor is Rf_* followed by
  cohomology, and Rf_* is the shared unbounded right derived module direct image,
  computed with K-injective resolutions. It is not underived pushforward.
- The consequence applies to every E and every integer q, including E unbounded
  in both directions: the independent second conjunct is
  `∀ (E : schemeDerivedQCohCategory X) (q : ℤ), ...`. Pass.
- For all sufficiently large integers n:
  `∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ...`. Pass; threshold depends on E and q as allowed.
- The specific natural map induced by E→τ_{≥-n}E is an isomorphism:
  `IsIso ((schemeHigherDirectImage f q).map
    ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E.obj))`. Pass. Read the
  standard-t-structure dependency node, Mathlib's `isGE_iff` and `isLE_iff`, and
  the definitions of `truncGE` and `truncGEπ` in TruncLTGE. They give the standard
  cohomological truncation with the required direction. Functor.map applies
  Rf_* and then H^q to this map; an arbitrary endpoint isomorphism is not substituted.

Edge cases: empty schemes and the zero derived object are admitted; no nonempty
instance appears. An empty indexing family is not part of this statement, and no
hidden chosen cover is quantified over. N=0 is correctly excluded by positivity;
N=1 permits the affine identity case. n=0 and negative n are admitted whenever
above the eventual threshold, without asserting the map is an isomorphism for
all n. Every q in ℤ is admitted. No characteristic is selected. u is arbitrary;
X and S use the shared Scheme universe required by Scheme.Hom, and localization
morphism universes wX and wS are independent, with no fixed small universe.

Independent searches with different wording:

- `msearch.py ... leanfinder "cohomological dimension of pushforward on derived
  categories of module sheaves"`: eight hits, generic cohomological support and
  injective dimension; none states this scheme direct-image bound.
- `msearch.py ... loogle "CategoryTheory.Triangulated.TStructure.truncGEπ"`:
  twelve hits, the canonical truncation map and its generic t-structure identities.
  Read the map's actual definition and reused it; none is the claimed bound.
- `rg -n -i 'cohomological.*(dimension|bound)|pushforward.*trunc|directimage.*(bound|trunc)|direct.image.*(bound|trunc)'`
  on Mathlib AlgebraicGeometry and Algebra/Homology, the entire source
  WeilConjectures tree, and project lean/Sheaf: hits concern étale/pro-étale
  dimension, weights, generic support or separate QCoh truncation/limit arguments;
  no existing declaration states both clauses of this theorem.

No mathematical mismatch was found, so no Lean or node text was rewritten.
There are no new definition nodes or dependency modules in this delivery. All
notions used have the dependency meanings above. The one named theorem has the
only sorry; it defines no data and proves nothing at stage 2. Its source and
blueprint tags are present, and its docstring carries the node's four proof steps
with their inputs: uniform module bound, affine Leray, unbounded section bound
and affine-basis sheafification, then the truncation triangle. The shift signs
in step 4 agree with cohomological shifts: H^m(T[-n-1])=H^{m-n-1}(T).
All variables and universes are explicitly bound. The node's lean.statement
was checked verbatim against the theorem signature.
