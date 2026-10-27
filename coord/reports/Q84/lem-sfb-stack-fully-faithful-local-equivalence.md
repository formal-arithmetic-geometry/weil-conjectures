## Worker report

The module `Sheaf.CategoryTheory.StackFullyFaithfulLocalEquivalence` states
`CategoryTheory.Pseudofunctor.stack_equivalence_iff_locally_essentiallySurjective_of_fullyFaithful`.
It has one theorem, with proof `sorry`, and no new definitions. The natural-language
statement, statement dependencies, proof and proof dependencies are unchanged.

The source is Stacks Project, `stacks.tex`, Tag 046N,
`lemma-characterize-essentially-surjective-when-ff`, read with its proof. The preceding
fully-faithfulness argument also explains why the total-category and fibrewise
formulations agree: arrows over a fixed base map are identified with arrows into a
cartesian pullback, and a cartesian functor preserves these identifications.

### Objects and presentation

The statement uses the same Mathlib presentation as the already landed
`Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`: a category fibred in
groupoids with coherent choices of pullback is a contravariant pseudofunctor to `Cat`
with groupoid fibres. These choices are a presentation of the given fibred category,
not a split-fibration assumption: identity and composition comparisons are invertible
and need not be identities. Any fibration admits such choices of cartesian lifts;
their universal property gives the coherent comparisons. Conversely, its
CoGrothendieck construction recovers the total fibred category. Mathlib's
`CategoryTheory.Pseudofunctor.CoGrothendieck` has the canonical cartesian lifts and
fibre equivalences in `Mathlib.CategoryTheory.FiberedCategory.Grothendieck`.
We retain objects and all isomorphisms, rather than taking isomorphism classes.

A `StrongTrans` is a functor between these presentations with invertible pullback
comparisons and their coherence equations. An isomorphism in the category
`StrongTrans.homCategory` is an invertible modification, hence a natural isomorphism
of the total functors over identity base arrows. The two explicit modification
isomorphisms in the conclusion therefore assert precisely the specified inverse
over the base. No triangle identity or strict inverse is added.

### Each hypothesis and clause

| Node text | Lean rendering |
| --- | --- |
| Size convention and a site small in the larger universe | Explicit `universe w`, `{C : Type w}`, `[SmallCategory C]`, and `J : GrothendieckTopology C`. Both objects and hom sets of the site belong to `w`. |
| Two categories fibred in groupoids on this site, with small fibres in that universe | `A B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w,w}` and `hA`, `hB`, each asserting `∀ T : C, IsGroupoid (...obj (.mk (op T)))`. Fibre objects and arrows belong to `w`. |
| Both are stacks: slice isomorphism presheaves are sheaves | `[A.IsStack J]`, `[B.IsStack J]` extend `IsPrestack`, whose `isSheaf` field is `Presheaf.IsSheaf (J.over T) (A.presheafHom x y)`, respectively for `B`. In groupoids these morphism presheaves are canonically the isomorphism presheaves. |
| Every covering object descent datum is effective | The same `IsStack` classes have `essSurj_of_sieve` for every covering sieve. Together with the prestack axiom this also gives effective descent on every covering family. |
| Functor over the base compatible with pullback | `F : StrongTrans A B`, including its invertible `naturality` comparisons and identity/composition coherences. |
| Every fibre functor induces bijections on isomorphisms | `hF : ∀ T, Nonempty (F.app (.mk (op T))).toFunctor.FullyFaithful`. Mathlib's `FullyFaithful` structure consists of an inverse to the map on hom sets with both inverse equations. Its mere existence is exactly bijectivity, and in groupoids equivalent to bijectivity on isomorphism sets. |
| Equivalence over the base with a pullback-compatible inverse | `∃ G : StrongTrans B A`, with `Nonempty` isomorphisms from `StrongTrans.vcomp F G` to `StrongTrans.id A` and from `StrongTrans.vcomp G F` to `StrongTrans.id B`. The category instances for these isomorphisms are supplied explicitly, so the exported signature does not depend on opening a scope. |
| If and only if | The main connective is `↔`, with the specified equivalence on the left and local essential surjectivity on the right. |
| For every base object and target-fibre object | `∀ (T : C) (b : B.obj (.mk (op T)))`. |
| There is a covering on which the restrictions are images up to isomorphism | `∃ R : Sieve T, R ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), R f → ∃ a : A.obj (.mk (op V)), Nonempty ((F.app (.mk (op V))).toFunctor.obj a ≅ (B.map f.op.toLoc).toFunctor.obj b)`. |

The sieve formulation is equivalent to the covering-family formulation in the node.
All arrows of a covering sieve are a small covering family, since the site is small.
Conversely, if lifts exist on a covering family, then a factorization through any
member supplies a lift on an arrow of its generated sieve, by pullback and the
strong transformation's comparison. No compatible choices of these local lifts
are demanded by the right side.

### Dependencies and edge cases

`def-weil-size-convention` has a convention-only record, with no declaration to
import. It is implemented by the explicit universe above. The recorded module for
`def-weil-pbc-topos`, `Sheaf.CategoryTheory.Sites.GrothendieckTopos`, is publicly
imported. Its `CategoryTheory.IsGrothendieckTopos` docstring explicitly delegates
sieves, topology and sheaves to Mathlib's `Sieve`, `GrothendieckTopology`,
`Presheaf.IsSheaf`, and `Sheaf`. Those are exactly the portions of this dependency
used here; no new topos predicate or replacement site definition is needed.

Other directly imported interfaces are `Pseudofunctor.IsStack` and its
`IsPrestack` parent (`Mathlib.CategoryTheory.Sites.Descent.IsStack`),
`Pseudofunctor.StrongTrans`, `StrongTrans.vcomp`, `StrongTrans.id`,
`StrongTrans.homCategory` (`Mathlib.CategoryTheory.Bicategory.Modification.Pseudo`),
and `CategoryTheory.IsGroupoid` (`Mathlib.CategoryTheory.Groupoid`). Their full
signatures and docstrings were read. The proof dependency
`lem-sfb-fibred-groupoid-equivalence-criterion` has no recorded Lean declaration
in the supplied repository, so there is no module to import for it. Its use is
retained in the proof docstring and DAG; it is not needed to state this theorem.

Edge cases checked before writing: an empty base imposes no fibre obligations;
empty fibre groupoids remain allowed; a target object with no source objects can
satisfy local surjectivity on an empty covering, but source stack effectivity on
that covering then supplies a source object and target morphism descent gives the
unique needed isomorphism. No nonempty-cover hypothesis is introduced. No products
or fibre products of base objects are assumed: common test objects and covering
sieves suffice. Identity functors satisfy both sides using identity modifications
and the maximal sieve. The universal quantifiers range over all objects of the
chosen larger universe, with no independent smaller test-object universe.

### Searches and validation

- `msearch.py` LeanFinder: “A fully faithful functor of stacks in groupoids is an
  equivalence if and only if objects locally lie in its essential image”. Eight
  hits, including `Equivalence.fullyFaithfulToEssImage`,
  `Pseudofunctor.IsStackFor.isEquivalence`, and
  `Pseudofunctor.IsStack.essSurj_of_sieve`. These concern ordinary essential images
  or the stack descent functor, not this local criterion for a morphism of stacks.
- `msearch.py` Loogle: `"IsStack", "IsEquivalence"`. One hit,
  `Pseudofunctor.IsStackFor.isEquivalence`; again a different statement.
- `msearch.py` grep under Mathlib `CategoryTheory`: regex
  `locallyEssentiallySurjective|[Ss]tack.*[Ee]quivalence|[Ee]quivalence.*[Ss]tack`.
  Two hits, both in `Sites/Descent/IsStack.lean`, for the equivalence with descent data.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, using the item id and the above concept/name
  patterns. No existing statement found. Project hits for this item are proof
  docstrings invoking it, not declarations stating it. The groupoid stackification
  module supplies the established presentation but not this theorem.

Server compilation through `scompile.py` succeeded cleanly. Only the required
`sorry` proof is postponed; all variables and universe levels are explicitly bound.
There is no disputed statement, statement correction, new node or dependency repair.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
