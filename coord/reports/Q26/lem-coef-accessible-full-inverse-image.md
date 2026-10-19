## Worker report

The module `lean/Sheaf/CategoryTheory/AccessibleFullInverseImage.lean` states
`CategoryTheory.accessible_full_inverse_image` and leaves its proof as `sorry`.
It formalizes the arbitrary-functor version of Lurie, HTT Corollary A.2.6.7.
There are no new definition nodes and no dependency modules: the only statement
dependency is the Mathlib realization of `def-weil-pbc-category-colimit`.

The Lean correspondence is as follows.

- The fixed universe and small Hom sets are represented by universes `v u₁ u₂`,
  `Category.{v} C`, and `Category.{v} D`.  Small diagrams use `Type v` and
  `SmallCategory`; filteredness is Mathlib's `IsCardinalFiltered`.
- `IsLocallyPresentable.{v} C` and `IsLocallyPresentable.{v} D` express that the
  two ambient categories are locally presentable.  The category and colimit
  notions are Mathlib's ordinary category, `Cocone`, and `IsColimit` notions;
  the chosen colimit is `c.pt`, as in `CategoryTheory.Limits.colimit` and its
  universal property.
- The functor `H : C ⥤ D` and instance `[H.IsCardinalAccessible κ]` express
  preservation of small `κ`-filtered colimits.  The explicit binders
  `(κ : Cardinal.{v}) [Fact κ.IsRegular]` preserve the node's infinite regular
  cardinal hypothesis through Mathlib's `Fact κ.IsRegular` interface.
- `V : ObjectProperty D` is the full subcategory on the selected objects and
  `[V.IsClosedUnderIsomorphisms]` is exactly repleteness.  The hypothesis
  `hVacc` first gives a regular `lam` and its closure clause: every diagram
  `X : J ⥤ D` of `V`-objects, with `J` `lam`-filtered, has every colimit cocone
  in `V`.  Its second clause gives a small family `P : I → D` of `V`-objects
  and, for each `V X`, a `lam`-filtered colimit presentation whose terms are
  isomorphic to members of `P`.
- The conclusion chooses a possibly different regular `μ`.  Its first clause
  records repleteness of the inverse image as
  `(V.inverseImage H).IsClosedUnderIsomorphisms`.  Its second clause states
  closure under all `μ`-filtered colimits in `C`, transported through `H` by
  the displayed `V (H.obj c.pt)` conclusion.  Its third clause supplies a
  small generating family `P : I → C` and presentations of every `X` with
  `V (H.obj X)`, with all index, filteredness, isomorphism, and colimit clauses
  written explicitly.  Thus the conclusion is the replete accessible full
  inverse-image subcategory, and it permits `μ` to differ from `κ` and `lam`.

The declaration uses these dependency interfaces:

- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, and the
  chosen-colimit convention recorded by `CategoryTheory.Limits.colimit` for
  `def-weil-pbc-category-colimit`.
- `Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms`:
  `ObjectProperty`, `ObjectProperty.inverseImage`, and
  `ObjectProperty.IsClosedUnderIsomorphisms`.
- `Mathlib.CategoryTheory.Presentable.LocallyPresentable`:
  `IsLocallyPresentable`, `Functor.IsCardinalAccessible`,
  `IsCardinalFiltered`, and `Cardinal.IsRegular` through `Fact`.

The proof docstring records all five proof clauses from the DAG.  It names
`lem-coef-accessible-functor-presentability-ranks` for the common rank and
`lem-coef-accessible-subdiagram-criterion` for the transferred approximation
and generation arguments.  Those are proof dependencies with no Lean records
yet, so they are intentionally not imported by this statement module; the
statement itself only needs the Mathlib interfaces above.

Before writing the statement I checked the edge cases.  `V = ⊥` (the empty
subcategory) and `V = ⊤` (all of `D`) satisfy the interface, as do the identity
functor and a constant functor whose value is in `V`.  The index type is allowed
to be any small type covered by `Type v`, and `IsCardinalFiltered` retains its
nonemptiness requirement.  Zero objects and empty object properties introduce
no extra hypotheses.  A constant functor whose value is outside `V` gives an
empty inverse image, confirming that no hidden nonemptiness conclusion is
being asserted.  The theorem allows the witnessing rank `μ` to be different
from the input ranks, as required by the source.

Searches made on 2026-10-17:

- `msearch.py Q26 lem-coef-accessible-full-inverse-image leanfinder
  "inverse image of an accessible replete full subcategory along an accessible
  functor"`: only general accessibility predicates (`Functor.IsAccessible`,
  `IsLocallyPresentable`, and cardinal-accessibility rank lemmas) were found;
  no inverse-image theorem with the required closure and generation clauses.
- `msearch.py ... loogle "IsCardinalAccessible, IsClosedUnderIsomorphisms,
  ObjectProperty.inverseImage"`: no hit (the search service reported the
  identifier pattern as unknown).
- `msearch.py ... grep
  "accessible_full_inverse_image|inverseImage.*IsCardinal" CategoryTheory/`:
  no exact declaration was found.  Direct `rg` searches of
  `WeilConjectures/` and the project's `lean/Sheaf/` found no declaration with
  this general statement.  The project's `AccessibleArrowInverseImage` is the
  distinct arrow-category specialization and was read to confirm that its
  explicit filtered-colimit interface is analogous, not identical.
- I read Mathlib's `Presentable/Basic`, `Presentable/LocallyPresentable`,
  `Presentable/CardinalFilteredPresentation`, and
  `ObjectProperty/ClosedUnderIsomorphisms`.  They provide the individual
  predicates and inverse-image repleteness, but no theorem asserting the
  arbitrary-functor accessibility result from HTT A.2.6.7.

No statement correction or `STATEMENT-DISPUTED` flag is needed.  The module
compiled cleanly with `scompile.py`; the expected warning for the theorem's
`sorry` was the only permitted warning.

## Second reading by Q26

I reread the node in `dag/nodes/sec-six-functors/lem-coef-accessible-full-inverse-image.json`,
its source place (HTT Corollary A.2.6.7, with the common-rank preparation from Proposition
A.2.6.5), and `AccessibleFullInverseImage.lean` line by line.

The node's objects, hypotheses, and conclusion match as follows.

1. The fixed universe is rendered by `universe v u₁ u₂`, with
   `C : Type u₁`, `D : Type u₂`, `[Category.{v} C]`, and `[Category.{v} D]`.
   The two locally presentable categories are exactly
   `[IsLocallyPresentable.{v} C]` and `[IsLocallyPresentable.{v} D]`.
2. The input accessibility rank and its regularity are `(κ : Cardinal.{v})`
   and `[Fact κ.IsRegular]`; the arbitrary functor is `H : C ⥤ D`, with precisely
   `[H.IsCardinalAccessible κ]`. No endpoint-induced or full/faithful hypothesis is added.
3. The target full subcategory is the object property `V : ObjectProperty D`, with
   `[V.IsClosedUnderIsomorphisms]`, rendering repleteness. Its accessibility hypothesis
   is `hVacc`: a regular `lam`, closure under every `lam`-filtered small diagram's
   colimit (for every cocone carrying `Nonempty (IsColimit c)`), and a small family
   `P : I → D` whose `V`-objects present every `V X` by a `lam`-filtered colimit,
   objectwise up to isomorphism.
4. The conclusion introduces a possibly different regular rank
   `∃ (μ : Cardinal.{v}) (_ : Fact μ.IsRegular)`. Its three clauses are exactly:
   `(V.inverseImage H).IsClosedUnderIsomorphisms`; closure of the inverse image under
   `μ`-filtered colimits in `C`, expressed as `V (H.obj c.pt)` for every colimit cocone;
   and a small family `P : I → C` of inverse-image objects presenting every inverse-image
   `X` by a `μ`-filtered colimit, objectwise up to isomorphism. Quantifier order and
   all `SmallCategory`, `IsCardinalFiltered`, cocone, colimit, and isomorphism clauses
   agree with the node.

No mismatch was found, so no Lean or node repair was needed. The source's ordinary
statement uses a common accessibility rank; the node deliberately states the equivalent
weaker existence of some witnessing `μ` after the common-rank enlargement, and the Lean
uses that exact corrected node statement. The recorded dependency is used through
Mathlib's `CategoryTheory.Limits.Cocone`, `IsColimit`, and chosen `colimit` interfaces;
`ObjectProperty.inverseImage` and `IsClosedUnderIsomorphisms` are also the recorded
Mathlib notions, with no private duplicate.

Edge cases checked: `V = ⊥` and `V = ⊤`, identity and constant functors (including a
constant outside `V`), empty/small index types subject to `IsCardinalFiltered`'s
nonemptiness, zero objects, and distinct object universes `u₁` and `u₂`. The statement
has no characteristic, finite-type, or nonemptiness assumption beyond the filteredness
class and therefore covers the node's empty and zero cases. The arbitrary functor case
is retained, including functors between arrow categories not induced endpointwise.

I repeated the existing-definition searches with LeanSearch/LeanFinder, Loogle, and
`rg` over pinned Mathlib, `WeilConjectures/`, and project `lean/Sheaf/`. They found only
general accessibility predicates and the distinct arrow-category specialization
`accessible_arrow_inverse_image`; no declaration states this arbitrary-functor theorem.
The source PDF was checked at the displayed Corollary A.2.6.7 and Proposition A.2.6.5
passages. The module compiles with `scompile.py`; the only expected diagnostic is the
statement theorem's `sorry`.
