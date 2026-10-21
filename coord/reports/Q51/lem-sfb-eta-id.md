## Worker report

Recorded the existing theorem
`AlgebraicGeometry.ProEtale.condensedPushforwardHom_id` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (local source lines 640–648,
also read from the current server with `scompile.py --source`). No Lean module is
added: brief-stage2 §1 requires reusing this exact upstream statement. Only the
item's `lean` field changes. Its `statement` is copied verbatim from the source
signature, before `:=`.

Hypothesis and clause comparison:

- A condensed ring Λ: the dependency `sk-def-sfb-condensed-ring` records
  `Profinite.CondensedRing` in `Sheaf.Topology.ProfiniteCondensedRing`. Its body is
  `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`. The upstream theorem's
  section parameter is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`;
  apply it to the underlying object `Λ.X` of any such bundled condensed ring.
  Its `omit [MonObj Λ] in` removes a structure unused in the underlying-sheaf
  equality. This is the same required equality for every condensed ring, with
  no need to change the node or add a specialized duplicate. No commutativity,
  admissibility, or topological presentation is required.
- An arbitrary scheme X is exactly `(X : Scheme.{u})`; `u` is the declared
  universe of the upstream file, and no scheme property is assumed.
- The object Λ_X is `condensedRingObj Λ X`, transparently
  `(upperStarFromPoint X).obj Λ`. Here `upperStarFromPoint X` is
  `pointUpperStar ⋙ (toSpecZ X)^*[Ab.{u + 1}]`, exactly pullback from the point.
- The left side η_id is `condensedPushforwardHom Λ (𝟙 X)`, the exact declaration
  recorded by `def-sfb-eta`. Its definition is the unit of
  `upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)` followed by pushforward of
  `condensedPullbackHom Λ (𝟙 X)`. This is the prescribed mate, not an arbitrary map.
- The conclusion “inverse of i_X at Λ_X” is the theorem's right side
  `(ProEtale.lowerStarId Ab.{u + 1} X).inv.app (condensedRingObj Λ X)`.
- The specified pushforward is `ProEtale.lowerStar`, recorded by
  `def-sfb-finite-lower-star`. Its body is restriction along
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ g`, with sections over V equal
  to the original sheaf's sections over `V ×_Y Z`.
- The canonical projection normalization is part of that same identity
  isomorphism, not an extra assumption. `ProEtale.lowerStarId` is
  `Functor.sheafPushforwardContinuousId'`
  applied to `MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X`. The latter's
  component has `hom := pullback.fst A.hom (𝟙 X)` and inverse the diagonal lift
  `pullback.lift (𝟙 A.left) A.hom ...`. Consequently the inverse sheaf comparison
  is restriction along the first projection `V ×_X X → V`, as required.

Dependency declarations inspected, including their signatures and docstrings:

- `def-sfb-eta`: `AlgebraicGeometry.ProEtale.condensedPushforwardHom`, in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `def-sfb-finite-lower-star`: `AlgebraicGeometry.ProEtale.lowerStar` and
  `lowerStar_obj_val_obj`, in the recorded compatibility module
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`, which publicly
  reexports their canonical owner
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing`, in
  `Sheaf.Topology.ProfiniteCondensedRing`, the transparent abbreviation above.
- The identity comparison is `AlgebraicGeometry.ProEtale.lowerStarId`, in the
  canonical finite-coefficient `UpperLowerStar.Defs` module. Its projection is
  explicitly constructed by `CategoryTheory.MorphismProperty.Over.pullbackId`
  in `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`.
  `Mathlib.CategoryTheory.Sites.Continuous` defines the induced identity
  isomorphism of sheaf pushforwards.

The existing proof agrees with the DAG route: unfold η and the inverse
pullback compositor, then apply `ProEtale.unitCompUpperStarComp_id` at
`pointUpperStar.obj Λ` and `toSpecZ X`. That coherence lemma compares adjoints
under the structure morphism and uses the left identity law for the
pushforward compositor. This is precisely the four-step blueprint argument.
The blueprint statement and proof were read in the main-20261015 snapshot,
`sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-id`.

Edge cases checked: X may be empty; no nonemptiness, finiteness, separation, or
characteristic hypothesis occurs. Λ may be the zero ring and may be
noncommutative; the equality uses only its underlying abelian sheaf. It is
universe-polymorphic in u, using schemes in u and abelian groups in u+1, exactly
as the dependency declarations do. The right side has direction
`Λ_X → (𝟙 X)_* Λ_X`, not the opposite direction. There are no node faults,
new definitions, dependency repairs, or statement disputes.

Searches made with `msearch.py Q51 lem-sfb-eta-id`:

- `leanfinder`: “The coefficient morphism of a condensed ring along the identity
  scheme morphism is the inverse of the canonical identity pushforward
  isomorphism”. Eight hits, including `Scheme.Modules.conjugateEquiv_pullbackId_hom`
  and Spec/global-sections identities; no exact Mathlib coefficient theorem.
- `loogle`: `AlgebraicGeometry.ProEtale.condensedPushforwardHom_id`.
  Zero hits, unknown identifier in Mathlib's index; this is an upstream name.
- `loogle`: `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction`.
  Twelve generic mate/adjunction hits; these do not replace the coefficient theorem.
- `grep`: `condensedPushforwardHom_id|unitCompUpperStarComp_id|lowerStarId`
  in Mathlib CategoryTheory. Zero hits.
- `leansearch`: “The identity coefficient morphism of a condensed ring on the
  pro-etale site is the inverse of the identity pushforward isomorphism”.
  Eight hits, including `Functor.sheafPushforwardContinuousId'_inv_app_val_app`
  and `Scheme.Modules.conjugateEquiv_pullbackId_hom`; none is the coefficient
  theorem on small pro-etale sites.
- Direct `rg` of Mathlib for `condensedPushforwardHom_id|unitCompUpperStarComp_id`
  found no exact theorem. Searches of `lean/WeilConjectures` found the exact
  declaration at `SixFunctors/ProEtale/ModuleObject/Basic.lean:643` and its
  coefficient-unit consumers. Searching for the blueprint id itself found no
  upstream textual tag; the exact named theorem is nevertheless present.
- `rg` of `lean/Sheaf` for `condensedPushforwardHom_id` found only uses in
  `Paper/ProfinitePointPullback.lean`, not a competing declaration. The upstream
  names index had no additional hit for that name.

Validation: the delivery wrapper checks the existing declaration on the live
compile server through its generated `#check @...` probe using scompile.py,
then runs the maintainer's server preflight. No source module is delivered.

## Second reading by Q51

No second reading by a worker: the dispatch brief requires direct delivery and
prohibits starting other agents. The maintainer's independent review is the
review of this existing-declaration binding.
