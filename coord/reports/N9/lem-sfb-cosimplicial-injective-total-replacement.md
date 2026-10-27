## Worker report

The module `Sheaf.CategoryTheory.CosimplicialInjectiveTotalReplacement` states
`CategoryTheory.exists_cosimplicial_injective_total_replacement`, with a single
`sorry` proof. It introduces no definitions and changes only the item's `lean` field.
The statement and all original statement/proof dependencies remain unchanged.

The source places read were Stacks `derived.tex`, Tag 0141,
`lemma-functorial-injective-resolutions` and `remark-match` (the normalization
J(0)=0, the common lower bound, and strict naturality); `injectives.tex`, Tag 079H,
`theorem-injective-embedding-grothendieck`; and `homology.tex`, Tag 0133,
`lemma-double-complex-gives-resolution`, including its variant exchanging indices.
The node's five proof steps are reproduced in the theorem docstring, including
coface cancellation, both sign computations, and the transposed-column comparison.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A Grothendieck abelian category | `(A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]`; object and hom universes are independent. |
| Nonnegative cochain complexes, extended by zero in negative degrees | `CochainComplex A ℕ`; this is the natural-index encoding of the zero extension. No negative-degree data, extra vanishing assumption, or localization choice is introduced. |
| Strict diagram on the category of nonempty finite ordered sets and monotone maps | `CosimplicialObject (CochainComplex A ℕ)`, Mathlib's functor category on `SimplexCategory`. A diagram morphism is a natural transformation. |
| T(K)^r is the finite sum over n+q=r | `HomologicalComplex₂.total` of `(alternatingCofaceMapComplex (CochainComplex A ℕ)).obj K`, with total shape `ComplexShape.up ℕ`. Its `ιTotal` are precisely the coprojections of these summands. |
| δ is the alternating sum of cofaces | `AlgebraicTopology.AlternatingCofaceMapComplex.objD`: sum over `Fin (n+2)` with coefficient `(-1 : ℤ)^i`. The outer differential is this map in the category of complexes. |
| Total differential δ+(-1)^n d | Mathlib's `total`, with outer degree n and inner degree q, using the project's natural-index `TensorSigns` instance (`ε_up_ℕ`). |
| There exist one functor I and natural η:id→I | The first existential binds `I : CochainComplex A ℕ ⥤ CochainComplex A ℕ` and `η : 𝟭 (CochainComplex A ℕ) ⟶ I`. |
| Every η is a quasi-isomorphism | First inner conjunct, `∀ K, QuasiIso (η.app K)`. |
| Every term of I(K) is injective | Second inner conjunct, `∀ K q, Injective ((I.obj K).X q)`. |
| R(K)=I∘K, u_K=(η_Kn)_n, with strict simplex operators | Postcomposition is the existing functor `K ⋙ I`; its augmentation is `Functor.whiskerLeft K η`, whose components are `η.app (K.obj n)`. The functor and natural transformation types enforce identities, compositions, and every simplex-operator equation. |
| T(u_K) is a quasi-isomorphism | Third inner conjunct: `QuasiIso (total.map ((alternatingCofaceMapComplex _).map (Functor.whiskerLeft K η)) (ComplexShape.up ℕ))`. |
| Every strict f has strict lift R(f)_n=I(f_n) | `Functor.whiskerRight f I : K ⋙ I ⟶ L ⋙ I` is that lift by its actual definition; there is no arbitrary comparison morphism. |
| R(f)u_K=u_L f | Fourth inner conjunct: `whiskerLeft K η ≫ whiskerRight f I = f ≫ whiskerLeft L η`, using Lean's left-to-right composition convention. |
| The same I and η apply to whole augmented diagrams, including nonnegative augmentation objects | Fifth inner conjunct quantifies over every nonnegative B, diagram K and strict augmentation `b : const B ⟶ K`. Its square compares b followed by u_K with `const (η.app B)` followed by the canonical identification and `whiskerRight b I`. The latter is the actual lifted augmentation; B has the same quasi-isomorphism and injectivity guarantees as every other complex. |
| Strict maps of augmented diagrams | The globally bound I maps the augmentation-object map and every column map; η is natural for all these maps. The strict diagram-map square applies to the cosimplicial part. `Functor.constComp` identifies the lifted constant diagram with the constant diagram on I(B), with identity components. No separately chosen resolution of B is used. |
| Every componentwise quasi-isomorphism induces a quasi-isomorphism on totals | Second outer conjunct, for arbitrary K, L, f and `∀ n : SimplexCategory, QuasiIso (f.app n)`. Its conclusion is `QuasiIso (total.map ((alternatingCofaceMapComplex _).map f) (ComplexShape.up ℕ))`. |
| Transposed bicomplex (q,n), with differentials d,δ | `HomologicalComplex₂.flip` of the alternating-coface bicomplex. Its total has differential d+(-1)^q δ. |
| Summand signs (-1)^(nq) specify a chain isomorphism | Third outer conjunct fixes `HomologicalComplex₂.totalFlipIso` by the equation from the (q,n) coprojection into its source to `(-1 : ℤ)^(n*q)` times the (n,q) target coprojection. The object is an actual `Iso` of cochain complexes, with both chain maps and inverse identities supplied by the existing construction. |
| The sign isomorphisms are natural | Fourth outer conjunct states `Tot(flip(f)) ≫ S_L.hom = S_K.hom ≫ Tot(f)` for every strict f. |

Dependency declarations read and used:

- `def-sp-double-complex-total`: recorded module
  `WeilConjectures.CategoryTheory.DoubleComplexTotal`, imported publicly. The
  used declarations in its mixed record are Mathlib's `HomologicalComplex₂`,
  `total`, `ιTotal`, `flip` and `TotalComplexShape`. The full total and flip
  construction signatures were read in their Mathlib sources. The filtrations
  themselves do not occur in this node's statement.
- `def-sp-grothendieck-abelian`: its Mathlib match
  `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, read with its
  full class signature and docstring. The match uses Grothendieck size v.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `InjectiveResolution`
  in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`. Both definitions
  and docstrings were read; the latter module is imported publicly and the
  statement uses `Injective` on each term.
- `def-weil-abstract-derived-category`: recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, imported publicly. The
  definitions `DerivedCategory`, `HasDerivedCategory`, `Q`, and the underlying
  `HomologicalComplex.QuasiIso` were read. Only complexes and quasi-isomorphisms
  are needed, so the statement does not add a `HasDerivedCategory` assumption.
- The required natural-index total shape, finite-diagonal coproduct instance,
  and natural-index symmetry are the existing declarations in
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` and its public import
  `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`.
- `AlgebraicTopology.alternatingCofaceMapComplex` in
  `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`, and
  `HomologicalComplex₂.totalFlipIso` in
  `Mathlib.Algebra.Homology.TotalComplexSymmetry`, are existing constructions;
  their definitions and docstrings were read rather than duplicated.
- `Functor.constComp` in `Mathlib.CategoryTheory.Functor.Const` supplies the
  canonical constant-diagram identification; its definition was read. Its
  identity components make the augmentation square exactly the componentwise
  naturality square in the node.

Proof dependencies imported without `public`:

- `lem-weil-pbc-grothendieck-functorial-injective-embedding`: the recorded
  Mathlib match in `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `lem-weil-pbc-functorial-bounded-injective-resolution`:
  `CochainComplex.exists_functorial_bounded_injective_resolution`, in
  `Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution`. Its signature
  preserves every lower bound, including zero, with one functor.
- `lem-sc-first-quadrant-total-column-comparison`:
  `HomologicalComplex₂.quasiIso_totalMap_of_columns`, in
  `WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison`. Its full
  signature uses the columns after flip, which explains the transposition in
  this node's proof. `def-sp-double-complex-total` is already a public import.

Edge cases checked before writing and again on the final statement:

- In total degree zero the only summand is (0,0), and its sign is 1. There is
  no incoming nonnegative differential; the natural-index encoding retains
  exactly the cohomology of extension by zero at degree zero.
- For n=0 or q=0 the transposition sign is 1. For n=q=1 it is -1;
  the internal differential sign on the (n,q) summand remains (-1)^n.
- Every diagonal n+q=r is finite. In negative integer degrees the extension
  has the empty sum, hence zero. No infinite coproduct or convergence
  hypothesis has been substituted for this finite-diagonal construction.
- The zero complex and zero augmentation object are allowed. No nonzero,
  nonempty, bounded-above, additivity-of-I, or degreewise monomorphism
  hypothesis was introduced. A functor I need not be additive here because
  it acts on already formed complexes and strict diagram maps.
- Identity maps, arbitrary codegeneracies, and all augmentation maps remain
  in the actual functor category; no passage to homotopy or derived diagrams
  occurs. Nonnegative complexes with unbounded positive support are included.
- The category may be trivial, and u and v are independent. No category of
  derived objects or chosen localization universe occurs in the conclusion.

Searches actually run:

- `msearch.py ... leanfinder` with query “A strict cosimplicial diagram of
  nonnegative cochain complexes admits functorial injective replacement with
  total quasi-isomorphism and signed transposition”: eight hits, including
  `CochainComplex.cm5b`, `cm5b.I`, `isKInjective_of_injective`, and
  `alternatingCofaceMapComplex`. None states the complete node; the alternating
  coface construction is reused.
- `msearch.py ... loogle '"alternatingCofaceMapComplex", "QuasiIso"'`: zero hits.
- `msearch.py ... grep 'cosimplicial.*injective|injective.*cosimplicial|flip.*[Tt]otal|[Tt]otal.*[Ff]lip'`:
  ten hits, finding `Mathlib/Algebra/Homology/TotalComplexSymmetry.lean` and
  `BifunctorFlip.lean`; reused `totalFlipIso` instead of constructing it.
- `msearch.py ... leansearch` with query “Functorial injective replacement of
  nonnegative cosimplicial cochain complexes and quasi-isomorphism of alternating
  total complexes”: eight hits, including object injective resolutions,
  homotopy-category right derivation, CM5b, and alternating cofaces. No complete
  strict nonnegative resolution plus total-comparison statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for cosimplicial/injective
  combinations, `alternatingCofaceMapComplex`, `flipTotal`, `totalFlip`, and
  `totalFlipIso`: found the parent `NonnegativeDerivedTotalization`, the Cech
  totalization consumer, and many uses of the existing alternating and signed
  total constructions. The parent's `nonnegativeCosimplicialTotal` definition
  is exactly the composite used inline here. It is not duplicated, and its
  downstream theorem is not imported as a prerequisite of its own proof lemma.
- Searched the source tree for the item id and searched the Mathlib, project,
  and upstream-name index for `cosimplicial_injective_total_replacement`:
  no pre-existing statement of this node was found.

Validation: `scompile.py N9 lem-sfb-cosimplicial-injective-total-replacement`
compiled both the sandbox probe and final module cleanly (8.6 s and 1.9 s).
The first compile diagnosed missing publicly visible natural-index total-shape
instances, ambiguous field projection from the complex-of-complexes encoding,
and the necessary `constComp` identification. The final module imports the
existing natural-total API, qualifies bicomplex operations, and uses that
canonical identification; it adds no definitions or hypotheses to resolve them.
There are no statement disputes, source corrections, dependency repairs, or new nodes.

## Second reading by N9

I reread the final node and Lean signature together after successful compilation.
This is a second pass by the assigned worker, not a claim of an independent
second agent's review; the dispatch brief forbids starting other agents, and
the maintainer performs the independent delivery review.

I checked that the first outer conjunction chooses I and η once, before any
cosimplicial or augmentation object is quantified. All components of η are
quasi-isomorphisms and all I(K)^q are injective, including the augmentation
complex B. The third inner conjunction uses the actual whiskered unit, the
fourth uses the actual postcomposition lift, and the fifth uses the actual
postcomposition of b, with `constComp.inv` in the correct direction. Since
this is a natural isomorphism with identity components, the extra term
records an existing canonical identification and imposes no new mathematical
condition.

I checked the second outer conjunction applies to every componentwise
quasi-isomorphism, rather than just the chosen η. I then checked the last two
conjunctions: the source inclusion has indices (q,n), the target inclusion
has (n,q), their common degree is n+q, the coefficient is precisely
`(-1 : ℤ)^(n*q)`, and the naturality equation is from the flipped source total
to the unflipped target total. The actual `totalFlipIso` type supplies a
chain isomorphism rather than a collection of cohomology isomorphisms.

No clause was dropped or replaced by an arbitrary map. No statement change
was necessary. The only changes after the first compile were the API repairs
listed in the validation paragraph above. The module uses all four recorded
statement dependencies and imports all stated proof dependencies.
