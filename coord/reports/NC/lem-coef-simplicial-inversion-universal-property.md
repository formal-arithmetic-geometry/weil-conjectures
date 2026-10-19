## Worker report

Item: lem-coef-simplicial-inversion-universal-property. Module:
`Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`; main declaration:
`CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`.
Every theorem proof is `sorry` (one theorem); all six auxiliary predicates have real,
explicit propositional definitions. There are no chosen localization data, axioms,
instances, or hidden proof obligations in these definitions.

Source read: HTT Appendix A.3.5, especially Notation A.3.5.1, Remark A.3.5.2 and
Proposition A.3.5.5, printed pp. 891–893:
https://people.math.harvard.edu/~lurie/papers/HTT.pdf.
The proposition states injectivity and exactly the component-functor image test.
The node's seven-step proof is included in the theorem docstring, including the
framed-function-complex argument that repairs the elementary-fiber shortcut.

Clause-by-clause correspondence:

- Small simplicial categories: `SCat.{u}` is the recorded
  `CoherentNerve.SCat`, with arbitrary-object enriched functors as morphisms.
  Universes are explicitly bound by `universe u`; enlarge `u` to contain every
  displayed small category, marking and diagram. There is no restriction to locally
  Kan, cofibrant or fibrant input categories.
- Dwyer–Kan equivalences: the first equality fixes the model weak equivalences to
  `SSet.Bergner.dwyerKanEquivalences`, which uses the existing
  `DwyerKanEquivalence`: mapping weak equivalences and equivalence on components.
- The model structure and generators: `∃ B : BergnerModelData.{u}` supplies actual
  Mathlib model axioms and completeness/cocompleteness. Cofibrations are
  `I.rlp.llp`, and fibrations are `(J R).rlp` for every allowed interval representative
  family `R`. These two equalities together with the weak-equivalence equality fix
  both weak factorization systems; no recognition theorem is a hypothesis.
- Model homotopy category: `BergnerHomotopyCategory` and
  `bergnerHomotopyFunctor` are the existing ordinary localization at these same
  Dwyer–Kan equivalences. The model structure makes this the model homotopy category;
  its cofibrant/fibrant replacement description is the standard model-category
  computation, not an alternative weak equivalence relation.
- `C` and the set of vertex arrows `W`: the existing `Pair` has `category` and
  `marked : MorphismProperty (underlying category)`. The underlying category's
  arrows are the vertices of the simplicial mapping sets. No closure property is
  imposed on the marking; `Marks` indexes exactly its endpoint-labelled elements.
- The derived pushout and structure map: for each `P`, the theorem asserts existence
  of `L`, `q` and `LocalizationPresentation B P q`, and quantifies over every such
  presentation for the mapping assertion. The existing presentation fixes the
  marked-arrow evaluations by their source, target and forward vertex. Its walking
  arrow is `bundle (U (𝟙_ SSet))`, and its walking groupoid has tensor-unit mapping
  sets at all four ordered pairs, hence exactly one arrow per pair. It factors the
  arrow-to-groupoid inclusion through a cofibration and weak-equivalent resolved
  groupoid, takes the two marked coproducts, and requires the existing model
  homotopy-pushout predicate. Resolving this right leg gives the same derived span
  as the original discrete groupoid span; this is not an ordinary strict-inversion
  pushout or an arbitrary map with a universal-property hypothesis.
- Restriction for every `T`: `MappingProperty P (bergnerHomotopyFunctor.map q)`
  quantifies over all `T : SCat.{u}`. Its restriction is literally `fun b ↦ q ≫ b`
  in the homotopy category. `Function.Injective` renders injectivity.
- Exact image: the second part of `MappingProperty` says
  `(∃ b, q ≫ b = a) ↔ InvertsMarked P T a`. `InvertsMarked` uses an actual
  three-arrow presentation `C ← A → B ← T` of `a`, with source map `w` in `I.rlp`,
  target map `v` a Dwyer–Kan equivalence, and the equality
  `Q(w) ≫ a ≫ Q(v) = Q(b)`. `RepresentativeInverts` tests that every vertex `f`
  of `A` whose image under `w` is marked has `IsPiZeroIso (b(f))`.
  An `I`-injective map is surjective on objects and a trivial Kan fibration on each
  mapping set, including surjectivity on vertices. Thus every original marked
  arrow has such a lift, and any two lifts have the same component after the
  component-category equivalence. The predicate therefore tests exactly every
  original marked arrow under the induced functor on components. Conversely
  cofibrant replacement of `C` gives such a `w` and fibrant replacement of `T`
  gives such a `v`; all homotopy classes are represented. Both outside arrows
  induce equivalences on component categories. `IsPiZeroIso` means having a
  two-sided inverse in components, not a strict inverse. Existential presentation
  is a predicate of `a` itself and does not choose a representative; the induced
  component functor is well defined up to natural isomorphism. No saturation or
  strict-inverse hypothesis is introduced.
- Characterization under `C`: `Uniqueness` quantifies over every other apex `L'`
  and unit `q'` in the homotopy category satisfying `MappingProperty`, and gives
  `∃! e : L ≅ L', q ≫ e.hom = q'`. This is exactly isomorphism under the source,
  including uniqueness. Every object of the ordinary localization is represented
  by a simplicial category, so testing targets `T : SCat` loses no target.
- Induced maps: `InducedMaps` uses the existing `PairHom`, whose `preserves` field
  says the given enriched functor carries marked arrows to marked arrows. For any
  localized pairs it asserts a unique `h` with the required triangle
  `q ≫ h = Q(f.functor) ≫ q'`, in the homotopy category.
- Composition: `CompositionCompatibility` asserts the identity equation and that
  any induced maps for `f`, `g`, and `f ≫ g` satisfy `h₁₂ ≫ h₂₃ = h₁₃`.
  There is no globally chosen inverse, localization object or induced map.

Dependency declarations and reuse (full signatures and docstrings read):

- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, `I`, `J`,
  `IntervalRepresentatives`, `U`, `bundle`, and `IsEquivalenceVertex`.
- `Sheaf.AlgebraicTopology.SimplicialIntervalCellStability`:
  `SSet.Bergner.dwyerKanEquivalences`, `simplicial_interval_cell_stability`.
- `Sheaf.CategoryTheory.CoherentNerveInfrastructure`: `SCat`, `sCatCategory`,
  `underlying`, `hom`; reexported by the dependency modules.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: `BergnerModelData`,
  `DwyerKanEquivalence`, `IsPiZeroIso`; already reexported by cell stability.
- Existing helper definitions in `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `Pair`, `PairHom`, `pairCategory`, `Marks`, `walkingArrow`, `walkingGroupoid`,
  `adjoinInverse`, and `LocalizationPresentation`. Only these definitions are used;
  its theorem `simplicial_localization_comparison_calculus` is not a proof input.
  This avoids second definitions of these notions. The reverse proof import into
  that downstream module must be omitted because it would close an import cycle,
  as allowed by stages/2-statements.md §3(7). No theorem-dependency edge from this
  item to the downstream comparison theorem is added.
- `Sheaf.CategoryTheory.CofibrantSimplicialInversion`:
  `IsBergnerCofibrant`, `IsBergnerHomotopyPushout`, used by the existing presentation.
- `Sheaf.CategoryTheory.SimplicialFullyFaithfulHomotopyImage`:
  `BergnerHomotopyCategory`, `bergnerHomotopyFunctor`, reusing the same localization
  category and functor rather than introducing a second one.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper` (proof dependency) is publicly
  imported by interval lifting; its `right_proper_kan_quillen` is available.
- The proof nodes `lem-coef-simplicial-derived-pushout-mapping` and
  `lem-coef-simplicial-walking-groupoid-components` have no Lean records yet.
  No definitions from them are needed to type the item; their future proof imports
  are deferred. This delivery does not state their independent framed theorems.

Edge cases checked before writing: empty marking makes the representative test
vacuous and the property bijectivity of restriction; the derived empty-span
pushout is equivalent to `C`. Empty `C` and empty `T` are included, with the usual
empty or singleton Hom sets. Marked identities and already component-invertible
arrows are allowed. There is no local Kan assumption on `C` or `T`, no injective
object-map assumption on marking-preserving functors, and no saturation assumption.
The `n=0` boundary generator in `I` is essential for lifting the actual marked
vertices; using only a component equivalence in the representative test would
have missed vertices and was rejected during design. All universes and variables
are explicitly bound and compilation uses `set_option autoImplicit false`.

Searches:

1. `msearch.py ... leanfinder` query "Simplicial category localization as a derived
   pushout inverting arrows universal homotopy mapping property": eight hits,
   including `CofibrantObject.HoCat.toLocalization`, ordinary localization and
   homotopy-relation facts. None states this enriched arrow-inversion theorem.
2. `msearch.py ... loogle` query
   `CategoryTheory.Localization, HomotopicalAlgebra.ModelCategory`: no hits;
   reports unknown identifier `CategoryTheory.Localization` (a namespace).
3. `msearch.py ... grep` query `simplicial.*localization|Bergner|DwyerKan`,
   Mathlib `CategoryTheory`: zero hits. Mathlib's localization construction was
   read directly; it supplies ordinary category localization, not this theorem.
4. `rg` for the node id and simplicial inversion/localization terms in
   `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no statement matching this
   node. Unrelated derived-category and ring-localization hits only.
5. `rg` for the node id, `Bergner`, derived/homotopy pushouts and inversion terms
   in `lean/Sheaf`: found the helper declarations reused above and citations of
   this still-unstated theorem in the comparison-calculus proof; no existing
   declaration states its universal mapping property. Read the complete relevant
   signatures and docstrings. The full-name prefix `CategoryTheory.SimplicialInversion`
   is new and the file compiled with no duplicate declaration errors.

6. `msearch.py ... leansearch` query "A localization of a simplicial category at
   chosen morphisms is universal for homotopy classes of functors that invert
   these morphisms": eight ordinary-localization hits, including
   `MorphismProperty.Localization`, `Functor.q_isLocalization`, and
   `Localization.strictUniversalPropertyFixedTargetQ`. None is a simplicial
   category inversion theorem or the required derived-pushout mapping assertion.

Validation: the prescribed `scompile.py NC
lem-coef-simplicial-inversion-universal-property <module>` compiled both sandbox
and library-form module cleanly, with no warnings. The first `deliver2.py --no-push`
dry run also passed server preflight and compilation (commit `17708af30c`); this
report was then supplemented with the additional LeanSearch result above. No statement correction, new
DAG node or dependency-record repair was needed. No STATEMENT-DISPUTED issue found.

## Second reading by NC

The dispatcher expressly forbids spawning another agent and assigns the independent
reading to the maintainer. This section records my own final clause audit, not an
independent worker verdict. I reopened the original node and the delivered module.
The audit checked the exact model generators, all categories and markings, the
resolved derived-pushout structure map, restriction direction, injectivity and
both directions of the image condition, uniqueness under `C`, and identities and
composition for marking-preserving functors. In particular the final definition
uses an `I`-injective source replacement, so every original marked vertex is
actually tested, and the conclusion concerns component inverses, never strict
inverse data. All three extra reused interfaces are definitions already in the
published modules; their downstream theorems are not hypotheses. There are no
node changes outside `lean`, no new definition copies and no missing conclusion
clauses. The maintainer's independent review remains the actual second reading.
