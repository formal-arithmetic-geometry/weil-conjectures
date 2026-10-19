## Worker report

The module `Sheaf.CategoryTheory.OperadicWeakApproximationAlgebras` states the
Gepner--Haugseng Theorem A.6.5 consequence.  It defines the canonical map on the
unary (`[1]`) fibres induced by the lax monoidal map `f`, and states that, when
`IsWeakApproximation q p f` holds and this colour-fibre map is an equivalence,
restriction along `f` is an equivalence on the full coherent algebra infinity
categories for every ordinary small nonsymmetric infinity operad `P`.

The Lean rendering of each hypothesis and clause is as follows.

* `M` and `O` are simplicial sets in `SSet.{max u v}`; `q` and `p` are their
  maps to `monoidalSimplexBase.{max u v}`.  This is rendered by the binders
  `{M O : SSet.{max u v}}`, `(q : M ⟶ monoidalSimplexBase.{max u v})`, and
  `(p : O ⟶ monoidalSimplexBase.{max u v})`.
* `f : M ⟶ O` is rendered by `(f : M ⟶ O)`.
* The full small/generalized/ordinary/lax weak-approximation package is rendered
  by `(hf : IsWeakApproximation.{u, v} q p f)`, using the recorded dependency
  `SSet.Enhanced.Nonsymmetric.IsWeakApproximation`.
* The equivalence on colours is rendered by `hcolour` applied to
  `operadicColourMap q p f hf.2.2.2.2.1`, where the helper definition is the
  pullback lift from `fiber q (monoidalBaseVertex 1)` to
  `fiber p (monoidalBaseVertex 1)` induced by `f`.  The proof component
  `hf.2.2.2.2.1` is exactly the lax-monoidal part of the conjunction defining
  `IsWeakApproximation`.
* The universal ordinary target is rendered by
  `(P : Operad.{u, max u v})`; `Operad` supplies its smallness, ordinary
  operad axioms, and projection.
* The conclusion that restriction is an equivalence is rendered by
  `IsFunctorEquivalence (restriction P.projection f hf.2.2.2.2.1)`.  The
  restriction declaration is the recorded `restriction` from
  `Sheaf.CategoryTheory.OperadicAlgebraPresentability`, so it is literal
  precomposition on the full marked functor subcomplex and retains coherent
  noninvertible transformations.

The recorded dependency declarations used are:

* `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory` for the universe and coherent
  infinity-category conventions (through the two direct dependency modules).
* `Sheaf.CategoryTheory.OperadicAlgebraPresentability`,
  `SSet.Enhanced.Nonsymmetric.Operad` and
  `SSet.Enhanced.Nonsymmetric.restriction` for ordinary operads, algebras, and
  restriction.
* `Sheaf.CategoryTheory.OperadicWeakApproximation`,
  `SSet.Enhanced.Nonsymmetric.IsWeakApproximation` for the weak-approximation
  predicate.

The helper `operadicColourMap` is a canonical pullback construction, not a
replacement notion: it is the same construction as the symmetric
`operadicColourMap`, with `fiber` over `monoidalBaseVertex 1` and the equality
provided by the lax-monoidal map.  It is declared in the owning module and
listed in the node's `lean.declarations`.

Edge cases checked against the source conventions: the `[0]` fibre is not
assumed nonempty or groupoidal; empty colour fibres are allowed; arity zero is
included through the ordinary operad's empty-product axiom; no space hypothesis
on the ordinary colour category is added; and all coherent transformations,
including noninvertible ones, remain in the full algebra subcategories.

Searches made:

* `msearch.py ... leanfinder "restriction along a weak approximation of nonsymmetric infinity operads equivalence on algebras when colors are equivalent"`: eight unrelated Mathlib hits, no operadic theorem.
* `msearch.py ... loogle "CategoryTheory.Functor.IsEquivalence, SSet.Enhanced.Nonsymmetric.IsWeakApproximation"`:
  zero hits; Loogle reported the project identifier as unknown.
* `msearch.py ... grep "operadicWeakApproximation|operadic_weak_approximation_algebras|operadicColourMap" CategoryTheory`:
  zero hits in the searched Mathlib subdirectory.
* `rg` over `WeilConjectures/` and the existing `lean/Sheaf/` found no declaration
  of this theorem; the only existing `operadicColourMap` is the symmetric one in
  `SymmetricOperadicApproximation.lean`, which has a different base and domain.

A first `scompile.py` run compiled the target module successfully (with only a
long-docstring warning, subsequently shortened).  Later required runs expose an
unrelated existing side-overlay failure while compiling the imported module
`Sheaf.CategoryTheory.SpaceValuedStraightening`: its `Diagrams` abbreviation
uses the noncomputable constant `smallSpaces` without a `noncomputable` section,
causing `error(lean.dependsOnNoncomputable)`.  A diagnostic private-overlay
compile with a temporary copy adding `noncomputable section` compiled all
transitive modules and this target cleanly, confirming the statement itself is
well typed; the temporary repair is outside this delivery and was not copied
into the project.

## Second reading by Q46

I reread the node and module side by side.  The binders for `M`, `O`, `q`, `p`,
`f`, the weak-approximation hypothesis, the unary colour equivalence, and the
universal ordinary operad `P` occur in the same order and with no extra
hypotheses.  The conclusion uses the recorded `restriction` map and states
`IsFunctorEquivalence`, exactly the node's equivalence clause.  The helper's
pullback map has source and target the `[1]` fibres specified by the node.  No
statement correction, dependency-module repair, or new DAG node was needed.

## Dependency modules

* `lem-coef-space-valued-straightening` is a transitive dependency of the
  recorded complete-algebroid interface.  Its published `Diagrams` abbreviation
  used the noncomputable `smallSpaces` construction without a noncomputable
  declaration, so the recorded module was unusable in the required file-only
  compile.  The delivered dependency module adds only `noncomputable section`
  and retains its full definitions, theorem statement, and interfaces.  The
  item now cites this landed dependency node in `stmt_deps` so the repair is
  explicit and reviewable.

## Maintainer review correction (NT-stage2-cc-ef36b7d0a)

* H3: the delivered statement took the target as `(P : Operad.{u, max u v})`, whose
  `small` field makes the target operad u-small. The node, Gepner--Haugseng A.6.5 and
  HA 2.3.3.23 quantify over every ordinary nonsymmetric infinity operad `P`, and the
  citer lem-coef-operadic-localization-operation-criterion (and the enrichment
  ancestry, whose targets are large presentably monoidal `V`) needs that. The target
  is now `{P : SSet.{max u v}} (r : P ⟶ monoidalSimplexBase.{max u v}) (hr : IsOperad r)`
  and the conclusion is `IsFunctorEquivalence (restriction r f hf.2.2.2.2.1)`. Only
  `M` and `O` stay u-small (inside `IsWeakApproximation`). A large
  `V : SSet.{max (u+1) w}` is reached with `v := max (u+1) w`; this instantiation was
  compile-checked.
* H8: the theorem docstring now gives the node's 14 proof steps.
* Dependency module: Q19 has since landed the same `Diagrams` compile repair on
  newtargets-dag (`noncomputable abbrev Diagrams`). So the delivered copy of
  `SpaceValuedStraightening.lean` is superseded. The landing keeps the landed record
  (`--revert-nodes lem-coef-space-valued-straightening`), and the stmt_deps entry
  stays as a landed node.
