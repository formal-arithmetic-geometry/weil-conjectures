## Worker report

The module `Sheaf.CategoryTheory.CompactPushoutRetractDescent` states
`CategoryTheory.exists_presentable_pushout_of_retract`, with its sole proof `sorry`.
The node is unchanged except for `lean`. No definitions, new nodes, dependency repairs,
or statement corrections are required.

Source read: Lurie, *Higher Topos Theory*, Lemma A.1.5.10, printed pp. 805–806,
https://people.math.harvard.edu/~lurie/papers/HTT.pdf (PDF pages 822–823, one-based).
The lemma's three conclusions are presentable endpoints, the pushout presentation of the
specified retract, and membership of the new arrow in the weak saturation of the original.
The node additionally fixes the uncountable case, which is retained exactly. Its seven
proof steps are included in the declaration docstring, including the common-source
reduction, the two eventual-equality arguments, the coequalizer splitting, and the final
pushout universal property.

Hypotheses and clauses, matched individually:

- Small universe: `universe v u`, `τ : Cardinal.{v}`, and `[Category.{v} A]` give small
  Hom sets and a small cardinal. `A : Type u` leaves the object universe unrestricted.
- Regularity: `[Fact τ.IsRegular]`. Uncountability: `hτ : Cardinal.aleph0 < τ`.
- Small colimits and a small generating family of presentable objects with small
  τ-filtered presentations: `[IsCardinalLocallyPresentable A τ]`. Its Mathlib definition
  extends `HasCardinalFilteredGenerator A τ` and `HasColimitsOfSize.{v,v} A`.
  The former supplies an essentially small family, presentable endpoints, and a
  small τ-filtered colimit presentation of every object. Choosing representatives
  gives precisely the node's small family, without adding a finiteness condition.
- τ-filtered means every diagram with fewer than τ arrows has a cocone:
  `IsCardinalFiltered.nonempty_cocone` tests `HasCardinalLT (Arrow K) τ`.
- τ-presentability means preservation of small τ-filtered colimits of Hom:
  `IsCardinalPresentable X τ` is `(coyoneda.obj (op X)).IsCardinalAccessible τ`;
  `Functor.IsCardinalAccessible` quantifies over `J : Type v`, `[SmallCategory J]`
  and `[IsCardinalFiltered J τ]`.
- Original morphism `u : P → Q`: `f : P ⟶ Q`, with separate
  `[IsCardinalPresentable P τ]` and `[IsCardinalPresentable Q τ]`.
- Pushout along some `P → V`: bind `a : P ⟶ V`, `b : Q ⟶ W`, `g : V ⟶ W`,
  and `hg : IsPushout f a b g`. The explicit legs specify the square witnessing
  the given pushout; `IsPushout.isColimit'` is precisely the span-colimit property.
- Given retract `g' : V' → W'`: bind `g' : V' ⟶ W'` and
  `hret : RetractArrow g' g`. This abbreviates `Retract (Arrow.mk g') (Arrow.mk g)`;
  its fields are the two commuting squares and `i ≫ r = 𝟙 _`.
- New objects and map: `∃ (P' Q' : A) (f' : P' ⟶ Q')`, followed by
  `IsCardinalPresentable P' τ ∧ IsCardinalPresentable Q' τ`.
- Attaching map: `a' : P' ⟶ V'`; the other pushout leg is `b' : Q' ⟶ W'`.
- Specified retract is the pushout: `IsPushout f' a' b' g'`, retaining exactly `g'`
  and its original source and target.
- Weak-saturation membership: the final `∀ S : MorphismProperty A` says every class
  containing `f` and all isomorphisms, and closed under pushouts, small continuous
  transfinite compositions, and arrow retracts, contains `f'`. These are respectively
  `S f`, `MorphismProperty.isomorphisms A ≤ S`, `S.IsStableUnderCobaseChange`,
  `S.IsStableUnderTransfiniteComposition.{v}`, and `S.IsStableUnderRetracts`.
  This is membership in their intersection, hence exactly the smallest such class.
  Mathlib's transfinite-composition structure requires well-order continuity and a
  colimit cocone for the entire chain. The universe `v` is the specified small one.
- There are no presentability instances or assumptions for `V`, `W`, `V'`, `W'`.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: module `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, with `Cocone`, `IsColimit`, `colimit.desc` and
  `CategoryTheory.IsFiltered` as recorded. The theorem expresses the specialized
  span universal property through Mathlib's `CategoryTheory.IsPushout`; no colimit
  definition is copied. Read `HasLimits.lean:174–221`, `Cones.lean:126–138`,
  `IsLimit.lean:58–71`, and `IsPullback/Defs.lean:65–81`.
- Supporting Mathlib vocabulary read: `IsCardinalLocallyPresentable`
  (`Presentable/LocallyPresentable.lean:35–42`), its generator interface
  (`Presentable/CardinalFilteredPresentation.lean`), `IsCardinalPresentable`
  and `Functor.IsCardinalAccessible` (`Presentable/Basic.lean`),
  `IsCardinalFiltered` (`Presentable/IsCardinalFiltered.lean:39–48`),
  `RetractArrow` (`CategoryTheory/Retract.lean:95–111`), and the three closure
  classes (`MorphismProperty/Limits.lean:117–123`, `Retract.lean:28–34`,
  `TransfiniteComposition.lean:210–220,296–304`).
- Proof-dependency Mathlib matches read and imported non-publicly:
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`
  (`Mathlib.CategoryTheory.Presentable.Directed`, lines 528–539), and
  `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`
  (`Mathlib.CategoryTheory.Limits.Final`, lines 290–295);
  `CategoryTheory.Limits.Types.jointly_surjective`,
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff` and
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`
  (`Mathlib.CategoryTheory.Limits.Types.Filtered`, and its imported `Types.Colimits`);
  `CategoryTheory.isCardinalPresentable_of_isColimit`
  (`Mathlib.CategoryTheory.Presentable.Limits`, lines 185–195).

Edge cases checked before writing: the category need not have a small object type;
its Hom universe and the small-cardinal/index universe agree. The large categories
of small sets are included (`u = v+1`). Empty filtered indexing categories are
correctly excluded by Mathlib's cocone condition on the empty diagram; finite
spans and parallel-pair coequalizers are smaller than τ. Identity generators and
identity retractions are allowed. Initial/zero objects and maps out of an initial
object are allowed, with no nonzero, monomorphism or epimorphism assumption on
`f`, `g`, `g'`, or their legs. The conclusion asks for no compactness of any of the
four original pushout/retract endpoints. No characteristic or additive structure
is imposed. No disputed statement or node fault was found.

Searches actually run through `msearch.py Q40 lem-coef-compact-pushout-retract-descent`:

- LeanFinder: “A retract of a pushout of a morphism between presentable objects is a
  pushout of a presentable morphism in its weakly saturated closure”. Eight hits,
  including `Retract.isCardinalPresentable` and `MorphismProperty.PreIndSpreads.exists_isPushout`.
  The former only preserves object presentability under retracts; the latter
  assumes a spreading property for a given arrow class and filtered presentation.
  Neither is this descent theorem.
- Loogle: `CategoryTheory.RetractArrow, CategoryTheory.IsCardinalPresentable`.
  Zero hits.
- LeanSearch: “Retract of pushout of presentable morphism descends to presentable
  pushout”. Eight hits, including `MorphismProperty.pushouts`, `IsPushout.desc`,
  `IsPushout.of_hasPushout`, and `Retract.isCardinalPresentable`; none has the
  requested existential presentation of an arrow retract.
- Mathlib grep: `weaklySaturated|WeaklySaturated|RetractArrow`, subdirectory
  `CategoryTheory`. Sixteen hits, exposing `RetractArrow` and retract closure,
  with no exact theorem.
- `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, weak saturation names, and
  `compact.*pushout|pushout.*retract`: no upstream exact theorem. The existing
  `WeakSaturationTreePresentation.lean` cites this item in its proof plan and uses
  precisely the same universal-class formulation of weak-saturation membership.
  Presheaf and marked-simplicial-set saturation definitions are specialized to
  those categories and cannot state this theorem for an arbitrary `A`.
- `rg` across Mathlib, upstream and `lean/Sheaf` for
  `exists_presentable_pushout_of_retract`: no pre-existing declaration.

Validation: prescribed `scompile.py` compiled the sandbox and final library module
successfully, with no errors or warnings. The prescribed delivery dry run is
`deliver2.py Q40 lem-coef-compact-pushout-retract-descent --no-push`; it recompiles
the module and runs server preflight. The independent second reading is reserved
for the next worker.

## Second reading by Q40

I independently read the corrected node statement in `dag/nodes/sec-six-functors/lem-coef-compact-pushout-retract-descent.json`, the source at HTT Lemma A.1.5.10 (printed pp. 805--806), the dependency record for `def-weil-pbc-category-colimit`, and the complete Lean declaration. The item-by-item rendering is:

- **Universe and cardinal.** The node fixes a universe of small sets, an uncountable regular `τ`, and small Hom sets. Lean uses `universe v u`, `{A : Type u} [Category.{v} A]`, `(τ : Cardinal.{v})`, `[Fact τ.IsRegular]`, and `hτ : Cardinal.aleph0 < τ`; thus the Hom/cardinal universe is the specified small universe and the object universe is unrestricted. Verdict: exact.
- **Locally presentable category.** The node requires all small colimits and a small family of `τ`-presentable objects presenting every object by a small `τ`-filtered colimit. Lean's `[IsCardinalLocallyPresentable A τ]` is the Mathlib class whose fields are precisely a `HasCardinalFilteredGenerator` and `HasColimitsOfSize.{v,v}`. Verdict: exact, with no extra finiteness or presentability hypothesis.
- **Original arrow.** The node's map between `τ`-presentable objects is rendered by `{P Q : A} (f : P ⟶ Q)` and `[IsCardinalPresentable P τ] [IsCardinalPresentable Q τ]`. Verdict: exact.
- **Original pushout.** The node's pushout of `f` along a map from `P` is rendered by `{V W : A}`, `(a : P ⟶ V)`, `(b : Q ⟶ W)`, `(g : V ⟶ W)`, and `hg : IsPushout f a b g`. The explicit four maps retain the specified square. Verdict: exact.
- **Arrow retract.** The node's specified retract in the arrow category is rendered by `{V' W' : A}`, `(g' : V' ⟶ W')`, and `hret : RetractArrow g' g`. Mathlib defines this as a retract of `Arrow.mk g'` from `Arrow.mk g`, with the commuting squares and split identity in the required orientation. Verdict: exact.
- **New compact presentation.** The existential binders `(P' Q' : A) (f' : P' ⟶ Q') (a' : P' ⟶ V') (b' : Q' ⟶ W')` and the first two conjuncts `IsCardinalPresentable P' τ ∧ IsCardinalPresentable Q' τ` render the two compact objects, their arrow, and the attaching map. Verdict: exact.
- **Pushout conclusion.** `IsPushout f' a' b' g'` says that the given retract arrow `g'` itself is the pushout, retaining its source and target and all four legs. Verdict: exact.
- **Weak saturation conclusion.** The final quantifier renders “the smallest class containing `f` and all isomorphisms and closed under pushouts, small continuous transfinite compositions, and arrow retracts”: for every `S : MorphismProperty A`, it assumes `S f`, `MorphismProperty.isomorphisms A ≤ S`, `S.IsStableUnderCobaseChange`, `S.IsStableUnderTransfiniteComposition.{v}`, and `S.IsStableUnderRetracts`, then concludes `S f'`. The `. {v}` parameter is the node's small universe. Verdict: exact.
- **Absent assumptions.** No presentability is assumed for `V`, `W`, `V'`, or `W'`, and no monomorphism, epimorphism, additive, characteristic, or nonzero assumption occurs. Verdict: exact.

The source's construction (common-source reduction, filtered compact-stage presentation, factorization and eventual equality, descended idempotent, coequalizer image, and final pushout universal property) is the seven-step proof plan in the declaration docstring; each step cites the recorded colimit dependency where needed. The prior statement wording now says “every object is the colimit of a small `τ`-filtered diagram of objects of this family,” matching the source's single filtered presentation requirement; the Lean class above has that meaning.

Edge cases checked: identity and zero arrows; initial/zero objects; empty or singleton indexing diagrams (the Mathlib cardinal-filtered condition supplies the required nonempty cocone condition); `u = 0` or an isomorphism; identity retracts; `τ = aleph_1`; and large object universes with small Hom sets. None is excluded by the binders or conclusion. The source imposes no characteristic or additive structure, and the Lean statement does not either.

I repeated the independent searches with `msearch.py` (LeanFinder semantic searches for compact pushout retract descent, Loogle searches for `RetractArrow` with `IsCardinalPresentable` and with pushouts, LeanSearch for retracts of presentable pushouts, and `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the theorem and its alternate phrasings). They found only general retract/presentability or closure lemmas, never this existential theorem. The exact declaration `CategoryTheory.exists_presentable_pushout_of_retract` is absent elsewhere.

No mismatch was found, so no source, node, dependency, or Lean text was changed in this second reading. `scompile.py Q40 lem-coef-compact-pushout-retract-descent lean/Sheaf/CategoryTheory/CompactPushoutRetractDescent.lean` completed for both sandbox and library copies with no errors.
