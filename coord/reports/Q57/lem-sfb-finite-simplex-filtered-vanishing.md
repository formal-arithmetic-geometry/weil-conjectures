## Worker report

`Sheaf.CategoryTheory.FiniteSimplexFilteredVanishing` states
`DerivedCategory.finiteSimplex_filtered_vanishing`, with its proof postponed by `sorry`.
The natural-language statement is unchanged. No new definitions or dependency repairs
are needed: the row identification is stated directly by projection equations.

Hypothesis and clause correspondence:

- The category is `{A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{v} A]`. Its ordinary derived category is `DerivedCategory A`
  with `[HasDerivedCategory.{w} A]`, allowing the chosen morphism-size universe.
- `I : Type t` has `LinearOrder`, `Fintype`, and `Nonempty`; `m` is `Fintype.card I`.
  The independent index universe is unrestricted: only finite products are taken.
- `D : DerivedCategory A`. The finite decreasing tower is reindexed by `k = a+1`:
  `F k` is the node's `F^(k-1) D`, and `G k` its `G^(k-1)`.
  The maps are `i k : F (k+1) ⟶ F k`, `q k : F k ⟶ G k`, and
  `δ k : G k ⟶ (F (k+1))⟦1⟧`.
- `hT` asserts precisely that `Triangle.mk (i k) (q k) (δ k)` is distinguished
  for `k ≤ m`, i.e. `-1 ≤ a < m`. `eD : F 0 ≅ D` is the initial identification;
  `hF : IsZero (F (m+1))` is the terminal identification with zero.
  The function presentation allows irrelevant data above this finite range;
  neither the hypotheses nor the conclusion depend on those data. Every finite
  tower admits such an extension (zero objects and zero maps suffice).
- The first-page objects are written directly as
  `(homologyFunctor A ((k.val : ℤ) - 1 + b)).obj (G k.val)`.
  `M : ℤ → A` supplies one coefficient object for every integer row.
  `e b k` identifies each first-page object with the finite product indexed by
  increasing embeddings `Fin k.val ↪o I`, equivalently subsets of size `a+1`.
  Finite products in an abelian category are canonically finite biproducts;
  using them avoids an extra finite-biproduct structure hypothesis or local instance.
- `Fin 0 ↪o I` has exactly one member, so `e b 0` identifies the augmentation
  term with a singleton product of `M b`, canonically `M b` itself. For `k=0`,
  `he` says that every vertex projection of the augmentation is the unique
  empty-subset projection: exactly the diagonal map under that canonical identification.
- The first differential is the actual triangle connecting morphism
  `HomologySequence.δ` followed by the cohomology of `q (k+1)`.
  Its source degree is `a+b`, its target degree is `a+b+1`, and its horizontal
  target is `a+1`, so the row degree `b` is unchanged. The `eqToHom` merely
  normalizes `(k-1+b)+1 = ((k+1)-1)+b`.
  `he` conjugates this differential by `e` and specifies every target projection.
  The right side is the sum over `j : Fin (k+1)` with coefficient `(-1 : ℤ)^j.val`;
  `(Fin.succAboveOrderEmb j).trans s` deletes exactly the `j`-th vertex of `s`.
  These projection equations include all differentials within the finite row.
- Terms outside `-1 ≤ a < m` are the zero extension of this finite page.
  They introduce no further hypotheses or choices in the signature. The last
  specified row object has `k=m`, and there is no outgoing differential in the
  finite row. Extending the tower by zero makes that outgoing differential zero.
- The first conclusion is `IsZero D`. The next conjunct takes any distinguished
  triangle with third object isomorphic to `D` and asserts `IsIso T.mor₁`:
  this is precisely the cone consequence, allowing any cone representative.
- The final conjunct asserts invertibility of every map from `D` to any zero
  derived object `D'`. Applying the first conjunct to another supplied filtered
  datum gives this hypothesis, and hence invertibility of every map of such data.
  This uses only the underlying map, so includes all compatible filtered maps.
  Induced squares on zero cohomology commute by uniqueness; inversion preserves
  commuting squares. No choice of simplex contraction appears in these conclusions.
- `b : ℤ` is unrestricted; there is no cohomological boundedness assumption and
  no isomorphism of chain-level graded objects. The signature uses only finitely
  many filtration indices; no infinite-totalization convergence is asserted.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian` (the mathlib match of
  `def-sp-grothendieck-abelian`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory` (record of
  `def-weil-abstract-derived-category`); its `HomologySequence` module supplies
  `DerivedCategory.homologyFunctor` and `DerivedCategory.HomologySequence.δ`.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`:
  `CategoryTheory.SpectralSequence` and its page-homology interface (match of
  `def-sp-spectral-sequence`); here only the explicitly displayed initial-page
  objects and differential are needed as input, not a separately chosen spectral sequence.
- `WeilConjectures.CategoryTheory.ExactCouple`:
  `CategoryTheory.BigradedExactCouple`, its `derived`, `pageCouple`, `page`, and
  `pageDifferential` (record of `def-sp-exact-couple`). This convention and the
  reindexing are included in the proof docstring, rather than assuming an arbitrary
  unrelated exact couple as an extra hypothesis.
- Proof imports: `Sheaf.CategoryTheory.FiniteCoconeExactCouple`, theorem
  `CategoryTheory.BigradedExactCouple.finiteCocone_weakConvergence`, with its
  upstream `WeilConjectures.CategoryTheory.ExactCoupleConvergence` interfaces
  `AlphaColimit`, `LimitSubobjects`, and `WeaklyConvergesTo`; and
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, theorem
  `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁`.

Source read: `literature/stacks-project/homology.tex`,
`lemma-biregular-ss-converges` (Tag 012W), including its proof of finite-filtration
convergence; the item's five proof steps and their agent-written derived-tower
extension; the current blueprint unit `sk-thm-sf-ctf-stability` and paragraph (3)
of its direct-images proof. Tag 012W itself concerns filtered complexes; this
statement follows the node's explicit derived-tower extension and generic
exact-couple proof dependency, without adding strict representative hypotheses.

Edge cases checked before writing: `m=1` gives the augmentation-to-singleton
identity and forces zero; `m=2` has diagonal `(1,1)` followed by `(-1,1)`.
The unique empty subset is included, while the empty vertex set is deliberately
excluded by `Nonempty I` (its augmented complex need not be acyclic).
Top-degree subsets contain the least vertex, so the contraction identity includes
the top term. Zero coefficient objects, the zero category, zero derived objects,
all negative and positive cohomological degrees, and arbitrary index universes
are allowed. Naturality is the uniqueness of maps between zero objects and does
not require a functorial least-vertex choice.

Searches performed (no exact statement found):

- `msearch.py leanfinder`: "A finite filtered derived object vanishes when its first
  page rows are augmented alternating simplex complexes". Eight hits, including
  DoldKan `HigherFacesVanish` variants and alternating-face augmentation;
  none asserts this finite derived filtration criterion.
- `msearch.py loogle`: `SpectralSequence, Triangle, IsZero` returned zero hits,
  with unknown unqualified identifier `SpectralSequence`.
- `msearch.py grep`: `augmented.*simplex|simplex.*(filtered|vanish)|FiniteTriangleTower`
  returned fifteen simplicial/augmented-simplex infrastructure hits, no match.
- `msearch.py leansearch`: "Augmented alternating subset cochains of a finite ordered
  set with coefficients in an abelian category". Eight hits include
  `CochainComplex.augment`, `ChainComplex.alternatingConst`,
  `AlgebraicTopology.AlternatingCofaceMapComplex.obj`, and `CochainComplex.of`;
  none gives this row identification or vanishing statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for simplex, finite triangle
  towers, augmented subsets and alternating subset rows found
  `CategoryTheory.TriangleTower` in the upstream exact-couple triangulated module
  and specialized principal-open Cech rows. The former has infinite tower data
  and the latter module sections over affine schemes, rather than the general
  finite-row theorem. The supplied statement can use the individual distinguished
  triangles directly, with the row differential built from their actual boundaries.
  Searching the item id in `lean/WeilConjectures` found no declaration.
- `tools/blueprint_refs.py search 'augmented subset'` returned zero blueprint nodes;
  DAG grep found this item and specialized principal-open subset Cech material,
  with no separate general row definition needed by the explicit formula.

Validation: the delivered module compiled against the live published library using
`scompile.py`, both sandbox and library passes, within the default 60-second
per-file limit, with no errors or warnings. The initial index-normalization
elaboration was repaired using `Fin.val_succ` before integer arithmetic.
There are no known statement faults or disputed clauses.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
