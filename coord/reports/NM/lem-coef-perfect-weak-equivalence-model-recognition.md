## Worker report

The module `Sheaf.CategoryTheory.PerfectWeakEquivalenceModelRecognition` states
`HomotopicalAlgebra.perfectWeakEquivalenceModelRecognition`, with its sole proof `sorry`.
It introduces no definition and changes no natural-language statement or dependency list.
The declaration docstring reproduces all nine proof steps of the node, including the
small-object, small-generator, pushout, transfinite, lifting and retract arguments.

Source read: Lurie, Higher Topos Theory, Definition A.2.6.12, Proposition A.2.6.15,
Definition A.2.6.1 and the surrounding accessibility discussion, online at
https://www.math.ias.edu/~lurie/papers/HTT.pdf (PDF pages 835–844, printed 818–827).
The node deliberately assumes the stronger pushout stability along all cofibrations;
its proof explains how this supplies the hypothesis and closure step of recognition.
Proposition A.1.2.5 is the node's cited source for functorial small-object factorizations.

Every hypothesis is rendered as follows:

- Fixed universe: explicit `universe v u`, `C : Type u`, `Category.{v} C`.
  All sets and indexing categories below are small in the fixed universe `v`.
  The object universe `u` remains unrestricted. This implements the recorded
  metatheoretic convention `def-weil-size-convention`; its lean record explicitly has
  `convention: true`, no declaration and no importable module.
- Complete and cocomplete: `HasLimitsOfSize.{v, v} C` and
  `HasColimitsOfSize.{v, v} C`.
- Locally presentable: `IsLocallyPresentable.{v} C`. Its source signature and docstring
  were read: existence of a regular cardinal and a small family of presentable objects
  with filtered colimit presentations, together with small colimits. This is exactly
  the node's stated meaning, rather than an additional small-object assumption.
- Small set `I`: `I : MorphismProperty C` and `MorphismProperty.IsSmall.{v} I`.
  Mathlib defines this as smallness of the corresponding subset of `Arrow C`.
- `Cof` is the weakly saturated closure of `I`: `hCof` includes `I ≤ Cof`,
  `isomorphisms C ≤ Cof`, `IsStableUnderCobaseChange`,
  `IsStableUnderTransfiniteComposition.{v}`, and `IsStableUnderRetracts`, followed by
  minimality among all classes with those properties. This is the exact universal
  characterization of closure, not an assumption of the factorization theorem.
  Mathlib's transfinite composition API uses well-ordered continuous diagrams, with
  a chosen initial-object isomorphism and a colimit cocone. It includes identities
  (shape `Fin 1`) and all small ordinal compositions. Its equivalent ability to use
  any small well-order makes no mathematical restriction or enlargement.
- `W` contains isomorphisms: `hWiso : isomorphisms C ≤ W`.
- Two-out-of-three: `W.HasTwoOutOfThreeProperty`.
- Filtered-colimit stability: `IsStableUnderFilteredColimits.{v, v} W`.
- A fixed small subset generating `W` by filtered colimits: `hWgen` supplies one
  `W₀`, `IsSmall.{v} W₀`, `W₀ ≤ W`, and for every `f` in `W` an indexing
  `K : Type v`, `SmallCategory K`, `IsFiltered K`, and `W₀.colimitsOfShape K f`.
  The source of `colimitsOfShape` was read: it consists of a natural transformation
  whose components belong to `W₀` and colimit cocones on its source and target, with
  the induced map equal to `f`. Since arrow colimits are computed on source and
  target, this is precisely the arrow-category colimit assertion. No closure of
  `W₀` under isomorphisms or presentability of its elements is assumed.
- Pushouts of weak equivalences along cofibrations: `W.IsStableUnderCobaseChangeAgainst Cof`.
  The API definition was checked for orientation: its first property is the map
  being pushed out and its second is the map along which it is pushed out.
- Right lifting against `I` implies weak equivalence: `hI : I.rlp ≤ W`.
  Mathlib's `rlp` uses `HasLiftingProperty` and diagonal fillers in all commuting squares.

Every conclusion clause is rendered as follows:

- Retract closure of `W`: the first conjunct `W.IsStableUnderRetracts`.
- Existence of a model structure: `∃ m : ModelCategory C`.
  Three field equalities prescribe its cofibrations to be `Cof`, its weak equivalences
  to be `W`, and its fibrations to be `(Cof ⊓ W).rlp`. No unrelated model structure or
  arbitrary fibrations are substituted.
- Left properness: `m.categoryWithWeakEquivalences.weakEquivalences` is
  `IsStableUnderCobaseChangeAgainst m.categoryWithCofibrations.cofibrations`.
- The first weak factorization system: `IsWeakFactorizationSystem Cof
  ((Cof ⊓ W).rlp ⊓ W)`, exactly `(Cof, Fib ∩ W)`.
- The second: `IsWeakFactorizationSystem (Cof ⊓ W) (Cof ⊓ W).rlp`, exactly
  `(Cof ∩ W, Fib)`. Mathlib's class explicitly asserts both mutual lifting
  characterizations and factorization of every arrow; its full source was read.
- Functorial factorizations: the two corresponding `HasFunctorialFactorization`
  conjuncts. This class asserts existence of `FunctorialFactorizationData`, with a
  middle-object functor `Arrow C ⥤ C`, natural transformations `i` and `p`, their
  composition equal to the original arrow, and membership in the two classes.
- Small generation of the first system: the given small `I` and the equality
  `I.rlp = (Cof ⊓ W).rlp ⊓ W`.
- Small generation of the second: the final existential supplies `J`,
  `IsSmall.{v} J`, `J ≤ Cof ⊓ W` and `J.rlp = (Cof ⊓ W).rlp`.
  A generating set of a weak factorization system means precisely that its right
  class is its right lifting class; its left class is then the mutual left lifting
  class asserted above. In this locally presentable setting it is equivalently
  the weakly saturated closure of that generating set, by the small-object argument.
- Combinatorial: the assumed local presentability and these two small generating
  sets express the definition in HTT A.2.6.1, with no additional predicate needed.
- The universe assertion is preserved by `v` on all small generating sets, filtered
  diagrams, ordinal closures and available colimits. The proof plan uses only those
  colimits and small sets. Functorial factorization data is on the original category
  with its original Hom and object universes; no enlarged category is substituted.

Dependency declarations used:

- `def-weil-size-convention`: convention only, no declaration to import. The entire
  node and its `lean.note` were read and its prescribed explicit universe hypotheses used.
- `Mathlib.AlgebraicTopology.ModelCategory.Basic`:
  `HomotopicalAlgebra.ModelCategory` and its three class projections; the constructor
  `ModelCategory.mk'` was examined and is not a recognition theorem.
- `Mathlib.CategoryTheory.Presentable.LocallyPresentable`:
  `CategoryTheory.IsLocallyPresentable`, `IsCardinalLocallyPresentable`, and
  `HasCardinalFilteredGenerator` (through their source definitions).
- `Mathlib.CategoryTheory.MorphismProperty.IsSmall`: `MorphismProperty.IsSmall`.
- `Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition`:
  `IsStableUnderTransfiniteComposition`; its imports give `IsStableUnderCobaseChange`,
  `IsStableUnderFilteredColimits`, `colimitsOfShape`, `IsStableUnderCobaseChangeAgainst`.
- The model-category import gives `MorphismProperty.IsWeakFactorizationSystem`,
  `HasFunctorialFactorization`, `rlp`, `HasTwoOutOfThreeProperty`, `IsStableUnderRetracts`.
  These are Mathlib's existing notions, not private copies.
- Proof dependency `lem-coef-lifting-class-closure` is a Mathlib leaf with the recorded
  lifting/retract declarations in `MorphismProperty.LiftingProperty`, already publicly
  imported through `ModelCategory.Basic`. Its declaration signatures and docstrings
  were read. The two other proof dependencies
  `lem-coef-accessible-intersection-generators` and
  `lem-coef-accessible-small-object-factorization` currently have neither a `lean` record
  nor a Mathlib match; they are not statement prerequisites and no import can yet be
  added. No other DAG node was stated here.

Edge cases checked before writing:

- Empty `I` is permitted: `IsSmall` requires no nonemptiness. Its weak saturation is
  the isomorphisms; `I.rlp` is every map, so `hI` then forces `W` to contain every map,
  which is consistent with the resulting discrete/extreme model structure.
- Empty small generating subsets and empty attaching families are not excluded.
  Filtered indexing categories must be nonempty by the mathematical definition, so
  `IsFiltered K` has exactly the required restriction and no added nonemptiness binder.
- Zero-length transfinite compositions are identities and are included. Successor
  and nonzero limit chains are both represented by the existing Mathlib API.
- No pointedness, zero object, simplicial structure, chosen presentability rank,
  finite-generation bound, or cardinal small-object hypothesis is added.
- `C` need not be small in `v`. The two independent universe levels allow the usual
  large locally presentable examples with small Hom sets and small colimits.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`: “A perfect class of weak equivalences with small
  generating cofibrations recognizes a left proper combinatorial model category”.
  Eight hits, led by `ModelCategory`, `ModelCategory.mk'`, and model-category axioms.
  Their signatures require the factorization systems and do not derive them from
  perfectness; no exact match.
- `msearch.py ... loogle`: `"ModelCategory", "IsPresentable"`: zero hits.
- `msearch.py ... leansearch`: “Smith recognition theorem for a perfect class of weak
  equivalences and a small set of generating cofibrations”. Eight hits, including
  `ModelCategory.mk'`, WFS consequences and simplicial-set specializations; no match.
- `msearch.py ... grep`: `PerfectClass|perfect.*morphism|recognition|weaklySaturated`
  restricted to `CategoryTheory`: two unrelated ind-object recognition hits.
- `rg` in `WeilConjectures` for `weaklySaturated|perfect class|model.*recognition|
  recognition.*model|IsLocallyPresentable`: only Gabriel–Popescu local presentability,
  not a model recognition theorem. Searching the item ID there returned no match.
- `rg` in `lean/Sheaf/CategoryTheory` and the Mathlib morphism-property directories
  checked saturation, perfect-class, accessibility and filtered-colimit terminology.
  The presentable small-object and cotorsion recognition modules give other statements;
  none states this theorem. The exact new declaration name is absent from Mathlib,
  upstream source, the side library and `dag/lean_names_upstream.json`.
- The wrapper's four raw search result records are in `searches.jsonl` in this sandbox.

No statement correction, new node, dependency module, or disputed statement is needed.

Validation: the prescribed `scompile.py NM lem-coef-perfect-weak-equivalence-model-recognition`
compiled both the sandbox and library forms cleanly (1.1 s and 1.2 s respectively).
The one named theorem has `sorry` as its whole proof, as required for stage 2.

## Second reading by NM

I read the node statement and its source place (HTT Definition A.2.6.12 and
Proposition A.2.6.15, with Proposition A.1.2.5 for functorial factorizations) before
checking the Lean declaration. The item-by-item correspondence is:

- The fixed universe and category are `universe v u`, `C : Type u` and
  `[Category.{v} C]`; the size convention is reflected by the explicit `v` parameters.
- Completeness and cocompleteness are `[HasLimitsOfSize.{v, v} C]` and
  `[HasColimitsOfSize.{v, v} C]`, and local presentability is
  `[IsLocallyPresentable.{v} C]`, matching the source's regular-cardinal filtered-colimit
  generation and the node's complete/cocomplete hypothesis.
- The small arrow class is `I : MorphismProperty C` with
  `[MorphismProperty.IsSmall.{v} I]`; `Cof` and `W` are the two other arrow classes.
- The complete weak-saturation characterization of `Cof` is the conjunction `hCof`:
  inclusion of `I`, inclusion of isomorphisms, pushout stability, small transfinite
  composition stability, retract stability, and minimality among classes with these
  properties. This renders the node's pushout/transfinite/retract closure clause.
- `hWiso` gives isomorphisms in `W`; `[W.HasTwoOutOfThreeProperty]` gives two-out-of-three;
  `[MorphismProperty.IsStableUnderFilteredColimits.{v, v} W]` gives filtered-colimit
  stability.
- `hWgen` introduces a small `W₀`, includes `W₀ ≤ W`, and for every `f` in `W` supplies
  a `v`-small filtered category and `W₀.colimitsOfShape K f`; this is exactly the fixed
  small filtered-colimit generation in the arrow category.
- `[W.IsStableUnderCobaseChangeAgainst Cof]` is the source's pushout of a weak
  equivalence along a cofibration, with the API orientation checked in its definition.
- `hI : I.rlp ≤ W` is the stated right-lifting implication; `rlp` quantifies over all
  commutative squares and diagonal fillers.
- The conclusion begins with `W.IsStableUnderRetracts`, then introduces
  `∃ m : ModelCategory C` and identifies its cofibrations, weak equivalences, and
  fibrations as `Cof`, `W`, and `(Cof ⊓ W).rlp` respectively.
- The remaining conjuncts state left properness, the two weak factorization systems
  `Cof`/`((Cof ⊓ W).rlp ⊓ W)` and `(Cof ⊓ W)`/`(Cof ⊓ W).rlp`, functorial factorizations
  for both, the first generating equality `I.rlp = (Cof ⊓ W).rlp ⊓ W`, and a small
  `J ≤ Cof ⊓ W` with `J.rlp = (Cof ⊓ W).rlp`. These are the node's two small
  generation clauses and its explicit meaning of weak factorization system.

Edge cases were checked: `I`, `W₀`, and `J` may be empty; no nonemptiness is added.
`IsFiltered K` supplies the required filtered-index condition. Identity and zero-length
transfinite composites are included by the Mathlib transfinite-composition notion. The
independent object and morphism universes permit large locally presentable categories, and
no pointedness, zero object, finite-generation, characteristic, or extra scheme hypothesis
is introduced. The statement therefore covers the empty-index and identity cases in the
node.

I searched Mathlib and the source tree with the recorded `leansearch`, `leanfinder`,
`loogle`, and targeted `grep` queries in `searches.jsonl`, and searched project `lean/Sheaf`
and DAG names for the declaration. The hits are model-category constructors and unrelated
perfect/Smith terminology; no exact recognition theorem exists. The declaration name is
also absent from the upstream source and Mathlib. No definition or dependency module was
needed, and no statement correction or citer audit was triggered.

My fresh searches used different wording from the worker: LeanFinder, "Construct a model
category from filtered-colimit generated weak equivalences and a small generating set of
cofibrations" (eight hits, including `ModelCategory.mk'`, which assumes both WFS);
Loogle, `"HasFunctorialFactorization", "IsLocallyPresentable"` (zero hits); and grep,
`recognition|perfect|Smith` in `AlgebraicTopology/ModelCategory` (zero hits). Direct `rg`
for `weaklySaturated|weakSaturat|perfect.*equivalence|recognition.*[Mm]odel|[Mm]odel.*recognition`
in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` found the specialized
cotorsion recognition statement and marked-simplicial consumers, not this statement.
I opened Mathlib's definitions of local presentability, small arrow classes,
`colimitsOfShape`, filtered-colimit stability, cobase change against a class,
transfinite-composition stability, lifting properties, WFS and functorial factorization,
and the `ModelCategory` fields. Each verdict in the list above is a match.

There are no new nodes or dependency modules in this delivery. The sole statement
dependency `def-weil-size-convention` is explicitly a convention without an importable
declaration. I opened its full record and checked that explicit universe binders implement
its instruction. The lifting-closure proof dependency is the recorded Mathlib leaf and is
already imported through `ModelCategory.Basic`; the other two proof dependencies still
have no recorded Lean declarations. HTT, rather than a Stacks tag, is the node's actual
source. Its A.2.6.15 has weaker pushout hypotheses than this node, as the node explicitly
records; the Lean follows the node's stated stronger hypothesis without adding one.

I found no mismatch between the node and the Lean signature, so no source or module change
was required. I reran `scompile.py` on the module; both sandbox and library compilations
completed cleanly, with only the intentional theorem `sorry`.
