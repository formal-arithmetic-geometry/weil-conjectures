## Worker report

Existing declaration:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.tensorPullComparison_existsUnique`
in `Sheaf.Paper.SectionDerivedRealization`, lines 233–237. No module is added.
The node copy changes only `lean`, with `existing: true` and no `file` field.
The existing theorem's proof remains `sorry`.

The source was read locally and confirmed from the live server with
`scompile.py --source Sheaf.Paper.SectionDerivedRealization`.
Its signature, recorded verbatim before `:=`, is:

```lean
theorem tensorPullComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : tensor Λ Y ⋙ derivedPullback Λ f ≅
        ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X,
      TensorPullRepresentativeCondition Λ f d
```

Hypothesis and clause correspondence:

1. The commutative condensed ring is the section variable
   `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})` with `[MonObj Λ]`
   and `[IsCommMonObj Λ]`. This is the unbundled presentation of the recorded
   `Profinite.CondensedRing`, a `Mon` of that abelian-sheaf category. It is not
   restricted to condensed rings arising from topological rings.
2. The arbitrary scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   No geometric property is required of `f`.
3. The small sites are the actual `Scheme.ProEt` with `Scheme.ProEt.topology`.
   The section categories are the existing `modules Λ X` and `modules Λ Y`.
   Their construction retains site object universe `u + 1`, site Hom universe `u`,
   and module coefficient universe `u + 1`; it does not identify site objects with
   site morphisms. This is the fixed size convention of the dependency data and
   the exact source declaration explicitly named in the node, rather than a new
   generic-site interface or an added universe equality assumption.
4. Chosen derived categories are the existing section variable
   `[∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]` of the data.
   `DerivedCategory.Q` is cochain localization, `tensor Λ T` is the conjugate
   derived tensor, and `totalTensor Λ T` is the signed direct-sum cochain total.
5. `qTensor Λ T` is chosen from the unique transformation asserted by the recorded
   dependency `tensor_representatives Λ T`. No arbitrary comparison is substituted.
6. `pullback Λ f` is the fixed ordinary section-module inverse image; its
   `pullOplax` instance is `(adjunction Λ f).leftAdjointOplaxMonoidal`.
   The strong instance retains these oplax maps. Exactness is furnished by
   `pullback_preservesFiniteLimits` and `pullback_preservesFiniteColimits`.
7. Termwise pullback is `(pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)`.
   `derivedPullback Λ f` is its exact localization, defined as
   `(pullback Λ f).mapDerivedCategory`. The prescribed epsilon is precisely
   `(pullback Λ f).mapDerivedCategoryFactors`.
8. The node's `b` is `totalPullComparison Λ f P Q`. Its definition uses the two
   `totalTensor_obj` identifications and `HomologicalComplex.mapBifunctorComparison`
   applied to `Functor.OplaxMonoidal.δNatTrans (pullback Λ f)`. This is the
   preserved-coproduct comparison whose degree-pair summands are the specified delta
   followed by the total inclusion. Both totals use Mathlib's up-integer signed total:
   `d_P ⊗ 1 + (-1)^p 1 ⊗ d_Q`.
9. `∃! d : tensor Λ Y ⋙ derivedPullback Λ f ≅ ...` is existence and uniqueness
   of exactly the required natural isomorphism of bifunctors. Lean's `⋙` reads
   left to right; the node's composition reads right to left.
10. Unfolding `TensorPullRepresentativeCondition` gives exactly
    `LF(q_Y) ≫ epsilon_Tot ≫ Q_X(b) =
    d.hom.app (...) ≫ tensor.map (epsilon_P, epsilon_Q) ≫ q_X`.
    This is the node's displayed equation in Lean composition order, with the
    same source and target. In particular epsilon occurs in the forward direction
    on both sides, not as its inverse.
11. That predicate starts `∀ P Q : CochainComplex (modules Λ Y) ℤ,` and has no
    further hypothesis. Thus all pairs of unbounded complexes are covered, including
    non-K-flat complexes and complexes with non-flat terms. The existence statement
    does not assert invertibility of `qTensor` or of ordinary totals on such pairs.

Dependency declarations read and reused (namespace below is
`AlgebraicGeometry.ProEtale.ModuleRingedComparison` unless stated otherwise):

* `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing`, the `Mon` abbreviation. Commutativity
  is `IsCommMonObj` on its underlying abelian sheaf.
* `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, weakly-etale objects over the scheme.
* `def-pd-section-derived-tensor-data`: `derivedEquivalence`, `derivedPullback`,
  `tensor`, `totalTensor`, `totalTensor_obj`, `sectionLocalizationComparison`,
  and `localizedTotalComparison` in `Sheaf.Paper.SectionDerivedTensorData`.
* `lem-pd-section-tensor-representatives-exists-unique`: `tensor_representatives`
  in `Sheaf.Paper.SectionDerivedRealization`; its `TensorRepresentativeCondition`
  and `qTensor` retain all three clauses of that dependency.
* `def-pd-proetale-section-module-functors`: `pullOplax`, `pullMonoidal`,
  `ordinaryTensorComparison`, `totalComparison` and exactness instances in
  `Sheaf.Paper.ProEtaleSectionModuleFunctors`, using the actual `pullback`,
  `modules`, `equivalence`, and `adjunction` from its public import
  `Sheaf.Paper.SectionModuleOperationsData`.

The existing theorem docstring gives the source and proof: the ordinary pure-tensor
mate, signed totalization, computation on flat-term K-flat replacements, two-variable
localization and uniqueness, then naturality to every complex pair. The node expands
the last step explicitly: cancel only the invertible source map induced by resolving
quasi-isomorphisms, without inverting the ordinary total comparison at arbitrary inputs.
I read Stacks Tag 07A4, `lemma-pullback-tensor-product`, in
`literature/stacks-project/sites-cohomology.tex`, lines 3683 onward. It constructs
the canonical bifunctorial isomorphism by exactly these resolving representatives;
the additional all-complex normalization is the exact source theorem named by the node.

Edge cases checked mathematically before attachment: identity and arbitrary scheme
morphisms; zero complexes and zero coefficient rings; empty schemes; degree-zero inputs;
and complexes unbounded in both directions. None is excluded. For non-flat inputs
such as degree-zero torsion modules, `qTensor` need not be invertible: the statement
requires the square, not invertibility of its factors. This agrees with the proof's
source-side cancellation argument and avoids a false ordinary-tensor assertion.

Searches made through `msearch.py` (full outputs logged in sandbox `searches.jsonl`):

* LeanFinder: `Unique derived pullback tensor isomorphism characterized by the
  localization tensor square on every unbounded complex pair`. Eight hits, including
  generic localization, Tor, fractions and good-tensor results; no exact Mathlib match.
* Loogle: `CategoryTheory.Functor.mapDerivedCategoryFactors`. Twelve hits on the
  generic exact-functor localization factor and its equations; no pinned tensor square.
* Mathlib grep: `TensorPullRepresentative|tensorPullComparison|mapDerivedCategoryFactors`.
  Ten hits, all generic factor occurrences in `ExactFunctor` and `Ext.Map`.
* LeanSearch: `Derived tensor pullback comparison unique natural isomorphism with
  localization square on all complexes`. Eight hits including `leftDerivedUnique`,
  `rightDerivedUnique` and localization comparisons; none is this section theorem.
* Local project grep (`rg --no-ignore -n`):
  `TensorPullRepresentative|tensorPullComparison_existsUnique` in both
  `lean/WeilConjectures` and `lean/Sheaf`. The exact theorem and predicate occur in
  `SectionDerivedRealization`; `ModuleRingedToposDerivedComparison` only mentions
  the theorem in a proof docstring. No upstream duplicate was found.
* Item-id search in `lean/WeilConjectures`: no hits.

No statement correction, new definition, or dependency repair is needed. No discrepancy
or `STATEMENT-DISPUTED` flag is raised. This attaches a statement, not a proof completion.

## Second reading by NI

This is a second self-check; the dispatcher prohibits starting another agent and the
maintainer performs the independent review. I reopened the node, its dependency records,
the live theorem and `TensorPullRepresentativeCondition`. The twelve mathematical
objects in the hypothesis list are the recorded existing constructions, rather than
copies. The natural-isomorphism type has the correct direction. The square has the
exact three factors on each side; the left starts with `LF(q_Y)`, while the right
starts with `d`, and both end in the localization of the pulled-back total.

I also reopened `totalPullComparison`, `pullOplax`, `derivedPullback`, and `totalTensor`
to check the canonical map, signs, and epsilon orientation rather than relying on names.
The fixed section/site size convention is retained, in particular site Hom universe `u`
is distinct from the coefficient universe `u + 1`. The universal quantifier on complex
pairs has no resolving, boundedness or flat-term premise. Uniqueness is `∃!` for the
whole natural isomorphism. No mismatch was found; only the item's `lean` record changes.
