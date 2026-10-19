## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialModuleModel` states
`AlgebraicTopology.simplicialModuleModel`, with one postponed theorem proof. Its three
helper definitions construct the actual degreewise forgetful functor, free-module functor,
and their adjunction from Mathlib's existing constructions. No data are chosen from a
postponed existence theorem. No statement, dependency list, or proof plan was changed.

Hypothesis and clause correspondence:

- An arbitrary commutative ring is `(Λ : Type u) [CommRing Λ]`; there is no nonzero,
  field, characteristic, finiteness, or Noetherian hypothesis.
- The category of simplicial modules is exactly `SimplicialObject (ModuleCat.{u} Λ)`.
  Mathlib defines this as `SimplexCategoryᵒᵖ ⥤ ModuleCat Λ`, with natural transformations
  as morphisms. The universe `u` is arbitrary; rings, simplicial sets, and module carriers
  are in the same ambient universe, as in the free-module API and the horn dependency.
- The forgetful functor `U` is `simplicialModuleForget Λ`, explicitly the right-whiskering
  of `forget (ModuleCat Λ)`. On an object this is the same composition used by the
  published `AlgebraicTopology.simplicialModuleUnderlying` helper; it is not another
  definition of a simplicial object or of an underlying module.
- The degreewise free-module functor is `simplicialModuleFree Λ`, explicitly the
  right-whiskering of `ModuleCat.free Λ`. Its data in degree n are finitely supported
  Λ-linear combinations of n-simplices. `simplicialModuleAdjunction` is the actual
  Mathlib adjunction `ModuleCat.adj Λ` whiskered over `SimplexCategoryᵒᵖ`.
- The normalization used in every criterion and in the final conclusion is
  `(Abelian.DoldKan.doldKanNormalizationEquivalence (ModuleCat Λ)).functor`.
  Reading that dependency and Mathlib's `DoldKan.Equivalence` shows its functor is
  definitionally `AlgebraicTopology.normalizedMooreComplex`. In `MooreComplex.lean`,
  `NormalizedMooreComplex.objX` is top in degree zero and the intersection of the
  kernels of `X.δ k.succ` in degree n+1. Its differential `objD` is the restriction of
  the zeroth face. Thus this is exactly the node's positive-face convention.
- The model-category witness is `m : ModelCategory (SimplicialObject (ModuleCat Λ))`.
  `HasLimits` and `HasColimits` supply completeness and cocompleteness, beyond Mathlib's
  finite-limit/finite-colimit model axioms. The two `HasFunctorialFactorization`
  conjuncts concern precisely `(Cof ∩ W, Fib)` and `(Cof, Fib ∩ W)`. Mathlib's model
  axioms include retract stability, two-out-of-three and the two lifting/factorization
  systems; there are no extra generating-map or properness claims.
- The witness `s : ModelCategory SSet` has its fibration and cofibration structures
  equal to the scoped Mathlib Kan structures and its weak equivalences equal to
  `SSet.KanQuillen.weakEquivalenceStructure`. The latter is exactly the dependency's
  realization-based `SSet.Enhanced.IsWeakHomotopyEquivalence`, not an unspecified
  simplicial-set model. All three structures are fixed, so `s` cannot be an unrelated
  model when used in the Quillen clause.
- For EVERY simplicial module map `f`, the first equivalence identifies m-weak
  equivalences with `Enhanced.IsWeakHomotopyEquivalence (U.map f)`. The second identifies
  m-fibrations with `SSet.modelCategoryQuillen.J.rlp (U.map f)`, i.e. all horns including
  outer horns in every positive dimension. These are the two classes created by U.
- The third equivalence is `m.W f ↔ QuasiIso (N.map f)`. Mathlib's quasi-isomorphism
  condition covers all nonnegative homology degrees, including degree zero.
- The fourth equivalence is `m.Fib f ↔ ∀ n : ℕ, 0 < n → Function.Surjective ((N.map f).f n)`.
  It imposes precisely positive-degree surjectivity and no surjectivity in degree zero.
- `DgLeftQuillen s m (simplicialModuleFree Λ)` is exactly the recorded model dependency's
  preservation of cofibrations and trivial cofibrations. Together with the explicitly
  constructed free--forgetful adjunction this says the free-module functor is left Quillen.
- The final universally quantified implication has arbitrary `X Y : SSet` and `f : X ⟶ Y`.
  Its sole premise is `Enhanced.IsWeakHomotopyEquivalence f`; its conclusion is
  `QuasiIso (N.map ((simplicialModuleFree Λ).map f))`. No fibrancy or extra cofibrancy
  premise is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject`, `.δ`, `.σ` (definition and operator signatures read).
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure` and `right_proper_kan_quillen`;
  the scoped Mathlib horn-fibration and mono-cofibration structures are those it uses.
- `Sheaf.CategoryTheory.DgPresheafModelLocalizations`:
  `HomotopicalAlgebra.DgLeftQuillen`; its definition was read in full. The general model
  axioms are Mathlib's `HomotopicalAlgebra.ModelCategory`, whose full fields were read.
- `Sheaf.AlgebraicTopology.DoldKanNormalizationEquivalence`:
  `CategoryTheory.Abelian.DoldKan.doldKanNormalizationEquivalence`; its full definition
  and docstring, and Mathlib's resulting equivalence and normalized Moore construction,
  were read. No private normalization or alternate chain category is introduced.

All four statement-dependency modules are public imports. All currently stated proof-only
modules are ordinary imports: `DiskLiftingSurjective`, `NormalizedHornDisk`,
`SimplicialModuleMooreHomotopy`, `ModelInfinityDerivedAdjunction`, and
`SortedSimplicialAlgebraModel` in their recorded topic directories. The theorem docstring
carries each of the DAG's seven proof steps and the dependencies used there. There is no
additional postponed helper theorem.

Source check: opened [Choudhury--Gallauer, §3.3](https://arxiv.org/pdf/1511.02828),
printed pp. 11–12, sequence (1), Fact 3.14, and the paragraph preceding Proposition 3.15.
It transfers along the forgetful functor and specifies quasi-isomorphisms and
positive-degree surjections on connective chains. The paper displays the other standard
normalization (kernels of faces 0 through n−1, differential (−1)^n d_n). The DAG explicitly
uses the equivalent positive-face convention; the recorded Dold--Kan dependency and this
module consistently use that convention. Neither a source-based correction nor an
unrecorded change of the DAG statement is needed.

Edge cases checked mathematically before writing:

- For constant simplicial modules all positive normalized terms vanish. Every linear map
  between them is a fibration, including `0 → M` for nonzero M; this verifies that adding
  degree-zero surjectivity would be wrong. Weak equivalence still requires the map on
  degree-zero homology to be an isomorphism.
- A horn has dimension at least one, including the two one-dimensional horns. The
  `0 < n` condition includes normalized degree one and neither drops outer horns nor
  adds a fictitious zero-dimensional horn.
- The zero ring is permitted: its modules and free module objects are zero. Characteristic
  two is permitted; no sign or unit-inversion hypothesis was added.
- The empty simplicial set is permitted, and its degreewise free module is zero. The final
  clause quantifies over empty sources and targets as well as nonempty simplicial sets.
- The final clause applies to non-Kan simplicial sets. This is justified by every simplicial
  set being cofibrant, not by a fibrancy restriction.

Searches performed through `msearch.py NB lem-cbc-simplicial-module-model`:

- `leanfinder`: "simplicial modules model category fibrations surjective positive normalized
  degrees free module functor left Quillen". Eight hits, on Dold--Kan normalization,
  homological resolutions and the inverse functor; none states the model structure or
  free-module Quillen result.
- `loogle`: "ModuleCat.free, HomotopicalAlgebra.QuillenAdjunction". Zero hits; the latter
  identifier is unknown. The actual free-module declaration was then read directly.
- `grep`: "simplicial.*[Mm]odel|[Mm]odel.*simplicial|[Ss]implicial[Mm]odule" in
  `AlgebraicTopology`. Zero hits.
- `leansearch`: "model structure on simplicial modules weak equivalences fibrations
  forgetful functor". Eight hits, including `SSet.modelCategoryQuillen.fibrations_eq`,
  its fibration structure, and its cofibration equality. No simplicial-module model match.
- Direct `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf` for simplicial module/model
  spellings found the published Moore-homotopy and normalized-horn helpers, plus unrelated
  cosimplicial and enriched-module material. The normalized-horn helper already defines
  normalized free chains; this module does not redefine that composite.
- Direct `rg` for right-whiskering `ModuleCat.free`, free simplicial module and simplicial
  forgetful names found raw composites and the object-level underlying helper, but no
  existing free/forgetful functor or adjunction declaration for this notion. The helpers
  here merely expose the canonical functor-level constructions required by this item.
- Direct `rg` for the four proposed full declaration names in Mathlib, the source,
  `lean/Sheaf` and `dag/lean_names_upstream.json` found no collision. `grep -rn` for
  `lem-cbc-simplicial-module-model` in `WeilConjectures` returned no match.

No missing independent notion or unusable dependency record was found. No new node or
 dependency module is needed. No STATEMENT-DISPUTED issue remains. Compilation and delivery
checks are recorded below after running the prescribed wrappers.

Validation: `scompile.py NB lem-cbc-simplicial-module-model` compiled the delivered module
both as the sandbox statement and under its library module name, with no errors or
warnings. The wrapper also compiled its required dependency overlay. All Lean lines
are at most 100 characters. The only `sorry` is the named main theorem, and the node's
`lean.statement` is copied verbatim from its signature. Only the item's `lean` record
is changed in the node copy.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
