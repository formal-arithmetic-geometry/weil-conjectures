## Worker report

The module `Sheaf.CategoryTheory.DiagonalCoherentNerveComparison` states precisely
`lem-coef-diagonal-coherent-nerve-comparison`. Its sole postponed theorem is
`CategoryTheory.CoherentNerve.diagonal_coherent_nerve_comparison`; its proof is `sorry`.
All helper definitions contain real data, with structural laws proved from the existing
category/enrichment laws. No mathematical assertion is separately postponed.

Clause-by-clause reading:

- A small simplicial category is `A : CategoryTheory.CoherentNerve.SCat.{u}`. This is the
  recorded bundled `EnrichedCat` interface, using the fixed sufficiently large universe
  of the dependency. No local fibrancy or cofibrancy is assumed globally.
- The specified object-preserving locally Kan replacement is the explicit parameter
  `R : CoherentNerve.LocallyKanReplacement.{u}`. This is exactly the type of the
  `replacement` field of the recorded `CoherentNerveComparisonStatement`. It supplies
  `R.R`, `R.unit`, equality of object types, the identity object function, local weak
  equivalences, local Kan fibrancy, and functoriality. The theorem works with this supplied
  replacement; it makes no new choice of replacement or of an inverse.
- The ordinary category `A_n` is the existing
  `CofibrantSimplicialInversion.Degree A n`, with its existing `degreeCategory` instance.
  Its objects are those of `A`, its hom set is `(CoherentNerve.hom A x y).obj n`, and
  identities/composition are degreewise enriched identities/composition. The existing
  `degreeFunctor F n` evaluates an enriched functor on these labels.
- `D(A)` is `CoherentNerve.diagonalNerve A`. In degree `n` its definition is
  `(CategoryTheory.nerve (Degree A n)).obj n`: a functor from the finite ordinal to
  `A_n`, equivalently the stated string of composable arrows. Its operator first
  precomposes the ordinal string and then applies `degreeRestriction A a` to every
  arrow label. Thus both nerve and mapping-set indices vary by the same operator.
  `diagonalNerveMap` and `diagonalNerveFunctor` apply the actual enriched functor to all
  labels, giving exactly `D(f)`.
- The comparison's existence and naturality for **all** simplicial functors are
  `∃ η : diagonalNerveFunctor ⟶ CoherentNerve.nerveFunctor`. A natural transformation
  includes the actual simplicial maps `η.app A` and the strict naturality equation
  `D(F) ≫ η.app B = η.app A ≫ N_hc(F)`. The coherent nerve is the dependency's existing
  functor using Mathlib's subset-poset thickening, with no substitute nerve.
  The node asserts a natural map, not a separate chosen definition or a uniqueness
  clause; the existential transformation states exactly this existence.
- The locally Kan condition is exactly `IsLocallyKan A`, and the first conjunct says
  `IsWeakHomotopyEquivalence (η.app A)` under that condition. It introduces no condition
  on the homotopy category or object set.
- Object preservation in the second conjunct is the existing `FixesObjects F`:
  equality of the two object types **and** the identity object function expressed by
  `HEq`. This is the identity-on-the-common-object-set convention in the node's proof.
  The other hypothesis is exactly
  `∀ x y : A, IsWeakHomotopyEquivalence (F.map x y)`; the conclusion is the same
  predicate on `diagonalNerveFunctor.map F`. There is no Kan hypothesis in this clause.
- `replacedDiagonalComparison R η` is the natural transformation
  `Functor.whiskerRight R.unit diagonalNerveFunctor ≫ Functor.whiskerLeft R.R η`.
  Its component is literally `D(R.unit.app A) ≫ η.app (R.R.obj A)`, the stated
  `D(A) → D(RA) → N_hc(RA)`. The third conjunct asserts it is a weak equivalence for
  every `A`. Its natural-transformation type retains the precise square
  `D(F) ≫ γ.app B = γ.app A ≫ N_hc(R.R.map F)` for every `F`, including functors
  changing object sets. No arbitrary comparison or inverse is passed as a hypothesis.
- Every weak homotopy equivalence is
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, already used by
  `KanQuillen.right_proper_kan_quillen`: bijectivity on realization's path components
  and on positive based homotopy groups at every basepoint. No Joyal equivalence or
  unqualified model-structure weak equivalence is substituted.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement.replacement` and the underlying
  `CoherentNerve.SCat`, `hom`, `IsLocallyKan`, `LocallyKanReplacement`, `nerveFunctor`
  from its public import `Sheaf.CategoryTheory.CoherentNerveInfrastructure`.
  I read the full signatures/docstrings, including replacement's object-type equality,
  unit object identities, local weak equivalences and discrete normalization.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, with its explicitly fixed realization-based
  weak-equivalence structure. Its public dependency
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies the actual weak-equivalence
  predicate, whose component and homotopy-group definitions were also read.
- Reused supporting constructions from the published
  `Sheaf.CategoryTheory.CofibrantSimplicialInversion`:
  `CategoryTheory.CofibrantSimplicialInversion.Degree`, `degreeCategory`, `degreeFunctor`,
  `FixesObjects`. The full source was read locally and confirmed with
  `scompile.py --source Sheaf.CategoryTheory.CofibrantSimplicialInversion`.
  Only these definitions are used, not its postponed inversion theorem.

All already stated proof dependencies have their prescribed imports:
`BisimplicialDiagonalEquivalence`, `RightPinchComparison`, `RealizationFiniteLimits`,
plus `EnhancedDiagramsCones` through the public dependencies. The Mathlib leaves are
imported from `ModelCategory.BrownLemma` and `AnodyneExtensions.PushoutProduct`.
The other proof nodes have no current Lean record, so no speculative import is added.
The theorem's docstring preserves the full six-step proof plan, including the actual
mapping-fiber comparison, two coend identities, and strict replacement naturality.

Edge cases checked before finalizing:

- Empty object type: every ordinal has at least one vertex, so the diagonal has no
  simplices, just as the coherent nerve. All naturality equations remain meaningful.
  `FixesObjects` includes object-type equality, so its condition cannot hold for an
  empty-to-nonempty inclusion by vacuity of the pointwise clause.
- Degree zero: `nerve (Degree A n)` has the usual zero-simplex objects; no arrows or
  nonempty arrow products are added. Finite products in the proof include the empty
  product, namely a point.
- Identities, constant operators and collapsed intervals: the diagonal restricts an
  actual ordinal functor, so degeneracies insert identities and faces compose arrows.
  Its functor laws compile from the mapping-set simplicial identities.
- A discrete category, a point and the empty category are admitted with no hypotheses
  excluding them. A discrete groupoid's nerve and a noninvertible-arrow category's
  nerve are not conflated: the conclusion is a realization weak equivalence, not Kan
  fibrancy of the coherent nerve.
- Non-Kan mapping sets are allowed in the invariance assertion and in the final
  replacement assertion. Only the first assertion about `η.app A` needs local Kan.
- Universes and all variables are explicitly bound; `set_option autoImplicit false`
  is active. No extra equality between independently specified universes is imposed.

Searches for an existing statement/construction:

- `msearch.py ... leanfinder`: “The diagonal of the levelwise nerve of a simplicial
  category has a natural weak homotopy equivalence to its coherent nerve when mapping
  spaces are Kan”. Eight hits concerned ordinary nerves, coskeletal nerves and
  2-truncations; none states this comparison.
- `msearch.py ... loogle '"SimplicialNerve"'`: one hit,
  `CategoryTheory.SimplicialNerve`; its full source defines the coherent nerve but
  contains no diagonal comparison theorem.
- `msearch.py ... grep 'diagonalNerve|levelwiseNerve|SimplicialNerve' AlgebraicTopology`:
  five hits in `SimplicialNerve.lean`, all definition/documentation references.
- `msearch.py ... leansearch`: “Diagonal nerve comparison with the homotopy coherent
  nerve of a simplicial category”. Eight hits included `SimplicialNerve`, ordinary
  `nerve`, and the ordinary/truncated nerve adjunction; no diagonal comparison.
- `rg` over upstream `WeilConjectures`, Mathlib, the side library, and
  `dag/lean_names_upstream.json` for the item id, `diagonalNerve`, `levelwiseNerve`,
  `DegreeCategory`, `degreeCategory`, `degreeRestriction`, `degreeFunctor`,
  `diagonal_coherent_nerve_comparison`, `replacedDiagonalComparison`: no comparison
  exists. The supporting degree category and degree functor were found in
  `CofibrantSimplicialInversion`; those are reused, and the initially drafted copies
  were removed before the final compile.

Source verification: opened the cited Arakawa journal PDF. Definitions 1.2 and 1.7
identify the levelwise nerve and its diagonal; Proposition 2.1 constructs the natural
transformation in the same direction using the predecessor formula; Corollary 4.3
asserts the locally Kan comparison is a weak homotopy equivalence. The inclusion-poset
convention agrees with Mathlib. No source correction or statement dispute was found.

Process note for the maintainer: `CofibrantSimplicialInversion` already owns the degree
category definitions but its theorem cites this item in its proof plan. This delivery
imports that module solely to obey the one-definition-per-notion rule. Adding the
reverse proof-only import of `DiagonalCoherentNerveComparison` to
`CofibrantSimplicialInversion` would close a source import cycle and must be omitted
under stages/2-statements §3.7. No DAG dependency on the downstream theorem is added,
and that theorem is not used. A later neutral-module extraction of the shared
supporting definitions would remove this source-layout limitation; no live module or
other DAG node was edited in this delivery.

Validation: the prescribed `scompile.py Q77 lem-coef-diagonal-coherent-nerve-comparison`
compiled the published supporting overlay, the sandbox module and the module at its
intended library path cleanly (no errors or warnings). Only the permitted theorem
`sorry` remains. The node copy differs only in `lean`.

## Second reading by Q77

I independently opened the node, its source place, the dependency records, and
`Sheaf/CategoryTheory/DiagonalCoherentNerveComparison.lean`. The node's objects,
hypotheses, and conclusion render as follows, with the indicated verdicts.

- The small simplicial category (A) is Lean `A : SCat.{u}`, namely the recorded
  `CategoryTheory.EnrichedCat` over simplicial sets. Its object type and every
  mapping simplicial set are in the single fixed universe (u); no fibrancy or
  cofibrancy is added.
- The specified object-preserving locally Kan replacement is the explicit Lean
  parameter `R : LocallyKanReplacement.{u}`. This is exactly the `replacement` field
  of `CoherentNerveComparisonStatement`: `R.R`, `R.unit`, same object type and
  identity-on-objects unit, local weak equivalences, local Kan values, and strict
  functoriality. Its discrete normalization fields are part of that recorded
  replacement datum, not a new hypothesis on (A).
- For each degree (n), the ordinary category (A_n) is
  `CofibrantSimplicialInversion.Degree A n` with the existing `degreeCategory`:
  objects are those of (A), homs are `(hom A x y).obj n`, and identities and
  composition are the enriched ones evaluated in degree (n). The existing
  `degreeFunctor` is used for enriched functors. Verdict: exact object and arrow
  data from the node.
- The diagonal (D(A)) is Lean `diagonalNerve A`; its degree-(n) simplices are
  `(nerve (Degree A n)).obj n`, and `degreeRestriction` applies the same simplicial
  operator to every mapping label. `diagonalNerveMap` and
  `diagonalNerveFunctor` give precisely (D(f)) and its functoriality. Verdict:
  the two bisimplicial indices and their simultaneous operators are retained.
- Existence and naturality of the comparison are exactly
  `∃ η : diagonalNerveFunctor ⟶ nerveFunctor`. The natural-transformation type
  contains all components and the strict naturality square for every simplicial
  functor. `nerveFunctor` is the dependency's subset-poset coherent nerve, not an
  ordinary nerve substitute. Verdict: exact natural map clause.
- The locally Kan hypothesis is exactly `IsLocallyKan A`, and the conclusion is
  `SSet.Enhanced.IsWeakHomotopyEquivalence (η.app A)`. No condition on the
  homotopy category or object set is present. Verdict: exact first conclusion.
- The invariance hypothesis is `∀ x y : A,
  SSet.Enhanced.IsWeakHomotopyEquivalence (F.map x y)` together with the existing
  `FixesObjects F`. `FixesObjects` says equality of object types and `HEq` identity
  on that common type, matching “object-preserving”; the conclusion is exactly
  weak equivalence of `diagonalNerveFunctor.map F`. Verdict: no hypothesis added
  and no conclusion weakened.
- The replacement composite is
  `replacedDiagonalComparison R η`, whose component is definitionally
  `D(R.unit.app A) ≫ η.app (R.R.obj A)`, with target
  `nerveFunctor (R.R.obj A)`. Its natural-transformation type records the required
  naturality square, and the final conjunct asserts its component is a weak
  homotopy equivalence for every (A). Verdict: exact specified composite and
  naturality clause.
- `SSet.Enhanced.IsWeakHomotopyEquivalence` is the dependency's realization-based
  predicate, so the node's weak-equivalence convention is preserved verbatim.

Edge cases were checked against these definitions: empty object types and empty
mapping sets are admitted; an empty category remains covered by every quantified
clause; (n=0) gives the ordinary zero-simplex nerve with no arrow-product
requirement; empty finite products are the point; identities, degeneracies, face
maps, and collapsed ordinal intervals use the existing simplicial/category laws;
discrete categories and non-Kan mapping sets are allowed in the invariance clause;
the locally Kan assumption occurs only where the node puts it; and no universe
equality beyond the common (u) supplied by the small simplicial-category notion
is imposed.

For the existing-notion check I reran semantic LeanSearch, Loogle/LeanFinder, and
`rg` searches over Mathlib, `WeilConjectures`, the side `lean/Sheaf`, and
`dag/lean_names_upstream.json` for `diagonalNerve`, `levelwiseNerve`,
`degreeRestriction`, `degreeFunctor`, `replacedDiagonalComparison`, and
`diagonal_coherent_nerve_comparison`. They found only the ordinary/coherent nerve
definitions and the already recorded degree-category declarations; no comparison
statement or duplicate diagonal construction exists. I also opened the source PDF:
Definition 1.7 identifies (B(C)) as the diagonal of the levelwise nerve,
Proposition 2.1 constructs the natural (B\to N_{hc}) map, and Corollary 4.3
asserts its weak homotopy equivalence for fibrant (locally Kan) simplicial
categories. These agree with the node and Lean.

No mismatch was found, so no Lean or node repair was needed. The only postponed
declaration remains `diagonal_coherent_nerve_comparison` with `sorry`; all helper
definitions carry real data, source/blueprint docstrings, and compile cleanly.
