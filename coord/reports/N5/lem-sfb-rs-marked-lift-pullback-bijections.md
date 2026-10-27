## Worker report

The module `Sheaf.AlgebraicGeometry.RSMarkedLiftPullbackBijections` states the
marked lift bijections of Stacks, formal-defos.tex, Tag 06JH
(`remark-lift-bijections`), using the marked lifts of Tag 06JE
(`definition-lifts`). I read both source passages and all seven proof steps of
the DAG node. The node statement is unchanged. All theorem proofs are `sorry`;
all definitions have explicit data, and each postponed theorem has the source,
blueprint id, and its natural-language argument in its docstring.

The node's hypotheses and clauses correspond as follows.

- The field is `{k : Type u} [Field k]`; the test category is the recorded
  `TestCategory k k`, with its canonical self-algebra structure. There is no
  additional predeformation or terminal-fibre assumption.
- The groupoid-valued covariant pseudofunctor is
  `F : CofibredGroupoids.{u,v,w} k k`; `(hRS : IsRimSchlessinger F)` is exactly
  the recorded (RS) condition. The object and morphism fibre universes remain
  independent (`w` and `v`) and independent of the ring universe `u`.
- For `f : B ⟶ A` and `x : fibre F A`, the statement directly uses
  Mathlib's `CostructuredArrow (push F f) x`. Its object is exactly a pair of `y` and
  `hom : (push F f).obj y ⟶ x`. The target fibre is a groupoid, so this arrow is
  automatically invertible. An isomorphism of costructured arrows has underlying
  isomorphism `u` and the equation `(push F f).map u.hom ≫ α' = α`, exactly the
  node's marked compatibility, in Lean's left-to-right composition convention.
- The class set is written directly as `Quotient (isIsomorphicSetoid ...)`, exactly
  the set of those marked isomorphism classes. No marking is forgotten and no
  representative is chosen. No project-specific lift or quotient alias is declared.
- `MarkedLiftSquare` names `A`, `A₁`, `A₂`, `P`, `p`, `q`, and the two projections
  as `base`, `first`, `second`, `product`, `p`, `q`, `a₁`, `a₂`. `comm` is the
  square equation. `isPullback` is the pullback condition on the underlying
  `CommAlgCat k` arrows, and `surjective` is literally the disjunction that
  `map p` or `map q` is surjective. This allows precisely the actual ring fibre
  product and all its uniquely isomorphic projection-preserving presentations;
  it does not require a second surjectivity hypothesis or restrict to one leg.
- The composite arrow from P to A is `S.a₁ ≫ S.p`. The helper
  `markedLiftRestriction` uses `compIso` and the supplied equality of composite
  arrows to send the marking α to `c_i ≫ α`. `markedLiftPairRestriction` pairs
  its two components. The first conjunct of
  `rs_marked_lift_pullback_bijections` states this canonical function is bijective.
- A specified marked first lift is `x₁ : CostructuredArrow (push F S.p) x`, not merely an
  unmarked object or an isomorphism class. `markedLiftSecondRestriction` uses
  `markedLiftFixedRestriction`, whose explicit marking is
  `δ⁻¹ ≫ p_*η ≫ α₁`. The second conjunct quantifies over every such `x₁` and
  states the resulting map from lifts along `a₁` to lifts along `q` is bijective.
- `rs_marked_lift_pair_iso` gives naturality in every specified base isomorphism.
  `rs_marked_lift_second_iso` additionally quantifies over the specified first
  object isomorphism `j` and the required marking compatibility `hj`. Their
  equalities use the actual change-of-marking maps `markedLiftChange`.
- `MarkedLiftSquareMap S S'` gives all four diagram arrows and all four
  commuting squares. It imposes no surjectivity on those four arrows.
  `rs_marked_lift_pair_diagram` and `rs_marked_lift_second_diagram` state the two
  naturality equalities using `markedLiftSquareMap`, whose marking is the
  canonical compositor comparison followed by transported α and the specified
  base isomorphism β. The fixed target lift is the actual
  `markedLiftSquareObject`, so its marking is retained. A further isomorphism
  to any other specified target fixed lift is covered by `second_iso`.
- Coherent pseudofunctor morphisms are Mathlib's
  `Pseudofunctor.StrongTrans F.transport G.transport`, in the common ambient
  bicategory `Cat.{v,w}`. Its invertible naturality constraints and unit and
  composition coherence are precisely what the node requires. Both `hF` and
  `hG` assume (RS). `rs_marked_lift_pair_morphism` and
  `rs_marked_lift_second_morphism` state the two equalities. The explicit map
  `markedLiftMorphismMap` uses the inverse of `T.naturality`, in the direction
  `T_B ⋙ push G f` to `push F f ⋙ T_A` as appropriate for the costructured-arrow
  comparison (on objects: `t_f ≫ T_A α`). The fixed lift is transported by
  `markedLiftMorphismObject` with exactly that marking.

`Function.Bijective` on the specified canonical forward functions is the
bijection assertion without making arbitrary choices of inverse data. Every
naturality square for the inverse follows from its forward square and the
bijectivity theorem, as the node's proof explains. `markedLiftSquareMap_base`
is the elementary reassociation consequence of the four diagram equations used
to type the canonical composite-base transport; it is stated with `sorry`, too.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (the `def-weil-field` Mathlib match).
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`,
  `AlgebraicGeometry.ArtinDeformation.TestCategory`, `ring`, `map`,
  `CofibredGroupoids`, `fibre`, `push`, `compIso`, `IsRimSchlessinger`.
  I read the full test-category construction, transport definitions, comparison
  functor, literal pullback construction, and (RS) signature and docstrings.
- Proof-only import `Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra`,
  `AlgebraicGeometry.ArtinDeformation.artin_local_test_algebra`, the node's
  recorded algebraic pullback/nilpotence input. The definition dependency
  already supplies the literal pullback's validity, projections and condition.
- Mathlib `CostructuredArrow`, `CostructuredArrow.map₂`, `isIsomorphicSetoid`,
  `Quotient.map`, `IsPullback`, `Pseudofunctor.StrongTrans`, `Cat.Hom.toNatIso`.
  `map₂` and its full signature and implementation were read before use.

Edge cases checked: empty fibres (the quotient may be empty); a fixed first
lift need not exist (the second clause then has no instance); nontrivial
stabilizers (the comma isomorphism compatibility keeps them, rather than
quotienting unmarked objects); identity test maps and nonidentity marked-object
automorphisms; either only p or only q surjective; both legs surjective;
arbitrary nonsurjective arrows between the squares; arbitrary characteristic;
no predeformation assumption; identity and nonidentity coherent transformations.
Pullback uniqueness and equivalence of transport handle a different choice of
pullback presentation without a new assumption. No false or disputed clause was
found, and no dependency interface needed replacement.

Actual searches made for an existing statement or missing notion:

- `msearch.py`, LeanFinder, query "An equivalence with a pullback of groupoids
  gives bijections on isomorphism classes of marked lifts": eight hits, including
  `PreGaloisCategory.fiberPullbackEquiv`, descent-data equivalences,
  `HasFibers.Fib.isoMk`, and free groupoid constructions. None states the marked
  deformation lift assertions or all their naturalities.
- `msearch.py`, Loogle, `CategoryTheory.Equivalence, CategoryTheory.Groupoid`:
  two hits (`Groupoid.invEquivalence` and the fundamental-groupoid equivalence
  from a homotopy equivalence), neither applicable as the item statement.
- `msearch.py`, Mathlib grep,
  `markedLift|MarkedLift|marked_lift|Schlessinger`: no hits.
- `msearch.py`, LeanSearch, "Isomorphism classes of costructured arrows marked
  lifts of a groupoid pseudofunctor": eight hits, notably
  `CostructuredArrow.isoMk`; this confirmed the exact existing primitive for
  marked arrows. Other hits concern subobjects, free groupoids and lift properties.
- `rg` on `lean/WeilConjectures` for the item id and marked-lift spellings: no
  declaration of this statement. `rg` on `lean/Sheaf` found the existing test
  category, tangent tensor theorem, minimal descent theorem, and scheme-based
  marked stack deformations. The last uses a different scheme/stack framework;
  none is this pseudofunctor marked lift quotient or these bijections.
- The original `rg` across Mathlib, upstream and `lean/Sheaf` found no
  pre-existing declarations for the proposed helper names. The return identified
  a concurrent unlanded delivery that also declared `MarkedLift` and
  `markedLiftClass`; the repair below removes these aliases entirely.

Validation: compiled every declaration in module mode through the prescribed
`scompile.py`, against the published server build. The final dry run and delivery
results are recorded by the launcher wrappers.

## Repair of immutable head ab9a02c66217

The return identified two declaration collisions with the concurrent module
`Sheaf.AlgebraicGeometry.DeformationMarkedLiftTorsor`: `MarkedLift` and
`markedLiftClass`. I read the entire torsor delivery from its server branch
`deliver/NL/lem-sfb-deformation-marked-lift-torsor`, because neither the read
clone nor `scompile.py --source` had that unlanded module. Its `MarkedLift` is
exactly the same abbreviation for Mathlib `CostructuredArrow`, and its
`markedLiftClass` is exactly `Quotient.mk`. Its lowercase `markedLiftClasses`
also denotes the same quotient as the uppercase alias in the returned delivery.

Repair: removed all three aliases (`MarkedLift`, `markedLiftClass`, and
`MarkedLiftClasses`) and removed their entries from `lean.declarations`.
Every use now refers directly to the existing Mathlib `CostructuredArrow` and
`Quotient (isIsomorphicSetoid ...)`, through the already-public Mathlib imports.
There is no renamed replacement definition and no second copy of the notion.
The unused quotient-constructor alias was deleted outright. The seven substantive
theorems and all canonical map data have the same types after unfolding the old
aliases; only those aliases' syntax has been expanded in the signatures.

Importing the torsor module would be the wrong dependency direction: its DAG node
already depends on this node, it has no recorded landed Lean declaration, and
its source is not on current main (`scompile.py --source` reports unavailable).
Using the common existing Mathlib declarations directly resolves the collision
without adding a dependency on that downstream theorem or duplicating its
aliases. I also read the current main torsor node on the server and confirmed
that it remains a statement without a Lean record. The normal delivery wrapper
rebuilds this repaired packet on current main, rather than re-pushing the old head.

The repaired module compiles cleanly in both sandbox and library module modes
through `scompile.py`. All hypotheses, both bijections, and all six naturality
clauses remain present. The node's natural-language statement and dependencies
are unchanged; its Lean record now lists only the 21 declarations actually
owned by this module.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
