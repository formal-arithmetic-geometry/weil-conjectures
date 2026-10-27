## Worker report

The module `Sheaf.CategoryTheory.ChosenObjectQuasiInverse` states
`CategoryTheory.Functor.exists_quasiInverse_with_objIso`, with its one proof left
`sorry`. It states the whole node, including the prescribed objects, the specified
comparison components, uniqueness of the functor, the arrow formula, and the
comparison on the source category. There are no new definitions, new nodes,
dependency repairs, or statement corrections.

Source read: `literature/stacks-project/categories.tex`, Tag 05SG,
`lemma-construct-quasi-inverse`, its full statement and proof. The final comparison
in the node is the fully faithful cancellation described at the end of that proof.
The docstring gives all four DAG proof steps, including the identity/composition
checks, naturality, uniqueness, and the cancellation lemma.

Hypotheses and clauses, in order:

- The size convention is rendered by explicit levels `u₁ u₂ v₁ v₂`, the object
  binders `{A : Type u₁}` and `{B : Type u₂}`, and their explicit Hom levels.
  These categories both lie in a common larger universe (the maximum of these
  four levels, enlarged as necessary). No equality of universe levels is imposed.
- The two categories are `[Category.{v₁} A]` and `[Category.{v₂} B]`, using exactly
  Mathlib's `CategoryTheory.Category` recorded by `def-nagata-category`.
- The functor is `(F : A ⥤ B)`. Bijectivity of all Hom maps is precisely
  `[F.Full] [F.Faithful]`: surjectivity and injectivity respectively.
- The specified objects are `(j : B → A)`; the specified isomorphisms in the
  required direction are `(iX : ∀ X : B, X ≅ F.obj (j X))`.
- Existence of the required functor and equality with its specified object map
  are `∃ (J : B ⥤ A) (h : ∀ X : B, J.obj X = j X)`.
- The natural isomorphism is `(i : 𝟭 B ≅ J ⋙ F)`. The first conjunct states
  `i.hom.app X ≫ eqToHom (congrArg F.obj (h X)) = (iX X).hom` for every `X`.
  The transport identifies `F.obj (J.obj X)` with `F.obj (j X)`; it is equality
  transport, not an arbitrary comparison isomorphism. Equality of forward maps
  of isomorphisms also determines their inverses.
- The second conjunct is the formula for every `f : X ⟶ Y`:
  `F.map (J.map f)` equals `(iX X).inv ≫ f ≫ (iX Y).hom`, with only the
  equality transports at its endpoints inserted. Mathlib writes composition in
  diagrammatic order, reversing the displayed node's functional-composition order.
- The third conjunct supplies `e : F ⋙ J ≅ 𝟭 A`. Its equation is
  `F.map (e.hom.app a) = eqToHom (congrArg F.obj (h (F.obj a))) ≫
  (iX (F.obj a)).inv`. Thus it is precisely the prescribed inverse comparison,
  after the same necessary object equality transport. Faithfulness determines
  every component uniquely from this equation; a natural transformation is
  determined by its components, so it characterizes `e`.
- The fourth conjunct quantifies over every other `J'`, its object equalities
  `h'`, and its natural isomorphism `i'` with the same specified components,
  and concludes `J' = J`. This expresses uniqueness of the functor under exactly
  the requirements in the node, without requiring the competitor to satisfy the
  additional arrow formula or the final equivalence conclusions.
- `F.IsEquivalence ∧ J.IsEquivalence` states that both functors are equivalences.
  The actual mutual inverse data are the same `i` and `e` supplied above, rather
  than unrelated choices of inverse functors.

Dependency declarations read and used:

- `def-weil-size-convention`: its Lean record is a convention with no declaration
  or module; the explicit universe binders implement that record's instruction.
- `def-nagata-category`: `CategoryTheory.Category` and `CategoryStruct` in
  `Mathlib.CategoryTheory.Category.Basic`, publicly available through
  `Mathlib.CategoryTheory.Equivalence`. Their identity and composition laws are
  the exact category laws of the dependency node.
- Proof dependency `lem-sfb-fully-faithful-cancel-iso-components`:
  `CategoryTheory.Functor.fullyFaithfulCancelRight`, its two component formulas,
  and `Functor.map_preimage` in `Mathlib.CategoryTheory.Functor.FullyFaithful`.
  This is explicitly imported as a proof dependency. The full signature and
  component definitions were read, not inferred from the declaration name.
- `Mathlib.CategoryTheory.Equivalence` supplies `Functor.IsEquivalence`; its
  `Functor.inv` and `asEquivalence` were checked for possible reuse.
- `Mathlib.CategoryTheory.EqToHom` supplies the actual equality transports; its
  definition, source/target, and identity behavior were checked.

Edge cases checked before writing: both categories may be empty; then the object
and comparison data are vacuous and the empty functor is unique. If the target
category is nonempty and the source empty, the required object function cannot
be supplied, exactly as in the node. No `Nonempty` binder has been introduced.
For the identity functor and identity comparisons, the arrow formula gives the
identity functor. In a one-object category with nontrivial automorphisms, changing
the specified comparison conjugates the arrow formula; the theorem retains the
specified comparison, so it does not incorrectly assert independence of that
choice. With reflexive object equalities the transports reduce to identities.
Independent object and Hom universes remain allowed and fit a common larger
universe. No statement fault or disputed clause was found.

Searches, using `msearch.py N6 lem-sfb-chosen-object-quasi-inverse`:

- LeanFinder: “A fully faithful functor extends prescribed preimage objects and
  comparison isomorphisms to a unique quasi inverse functor”: 8 results,
  including `FullyFaithful.preimageIso`, `essImage.liftFunctor`, and both
  `fullyFaithfulCancelRight` component formulas; no exact full statement.
- Loogle: `CategoryTheory.Functor.FullyFaithful, "preimage"`: 12 results,
  including the preimage construction and its identity/composition properties;
  these give building blocks but do not state the node.
- LeanSearch: “A fully faithful functor has a unique quasi inverse with prescribed
  object representatives and comparison isomorphisms”: 8 results, including
  `Functor.IsEquivalence.mk'`, `Functor.inv`, and `FullyFaithful.preimageIso`;
  none retains the specified objects and comparisons with the uniqueness clause.
- Mathlib grep: `ofObjIso|copyObj|liftFunctor|fullyFaithfulCancelRight` in
  `CategoryTheory`: 25 results. Read `Functor.copyObj` and `isoCopyObj`,
  `Functor.essImage.liftFunctor`, `Functor.inv`, and `Functor.asEquivalence`.
  `copyObj` transports an already supplied functor; the other constructions
  choose their own representatives. None is the node's theorem.
- Ripgrep of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `chosenObject`, `chosen_object`, prescribed
  inverse/object phrases and the node id found no declaration of this statement.
  The chosen theorem name was also searched in Mathlib and both project roots
  without a collision.

Validation: the module compiled in module mode both as the isolated sandbox module
and under its actual library module name through `scompile.py`. The initial probe
showed that `Equivalence` did not publicly expose `eqToHom`; explicitly importing
its owning module fixed that visibility issue. No diagnostic commands remain.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
