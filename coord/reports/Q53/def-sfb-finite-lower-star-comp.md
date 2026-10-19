## Worker report

This delivery records the existing definition
`AlgebraicGeometry.ProEtale.lowerStarComp` in
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`, lines 330–337.
No new module or declaration is written. Only the item's `lean` field changes;
its natural statement, dependencies, proof, audit and status are preserved.
The inherited attachment named the same candidate but omitted the required
module, primary declaration, signature, existing flag, author and date fields.
There is no maintenance repair note for this item.

The source is the current blueprint `main-20261015`,
`sec-proetale-coefficients/sk-def-sfb-finite-pushforward-pullback/def-sfb-finite-lower-star-comp.md`.
I read that text, the dependency node and its full declarations/docstrings,
and the defining source and component lemma. The recorded signature is verbatim
from the definition, omitting only `:=` and its body, as required:

```lean
noncomputable def ProEtale.lowerStarComp : (h₁)_*[A] ⋙ (h₂)_*[A] ≅ (h₁ ≫ h₂)_*[A]
```

Clause-by-clause match:

- The morphisms `h₁ : T ⟶ S` and `h₂ : S ⟶ R` are precisely the enclosing
  explicitly declared variables `{R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)`.
  They have no finiteness, weak-etaleness, properness or other restrictions.
- The coefficient category is the same `A` as in `def-sfb-finite-lower-star`.
  The source declares `A : Type u'` with `Category.{u + 1} A`, `Abelian A` and
  `IsGrothendieckAbelian.{u + 1} A`. The latter two unused instances are omitted
  from the elaborated type: the formula works for any such category and thus
  specializes directly to every Grothendieck abelian coefficient category in
  the dependency. No additional coefficient datum is chosen.
- `(h₁)_*[A] ⋙ (h₂)_*[A]` means first push forward from `T` to `S`, then from
  `S` to `R`. It is the node's `(h₂)_* ∘ (h₁)_*`, using Lean's forward order.
  The notation expands to the dependency's own `ProEtale.lowerStar A h₁` and
  `ProEtale.lowerStar A h₂`, with no private copies.
- `(h₁ ≫ h₂)_*[A]` is pushforward along the composite `h₂ ∘ h₁`.
- `≅` between these functors is a natural isomorphism, so its components are
  sheaf isomorphisms natural in the sheaf `G` on `T`.
- The actual definition applies `Functor.sheafPushforwardContinuousComp'` with
  `eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
  (Q := ⊤) h₁ h₂).symm` and the three small pro-etale topologies. Thus it uses
  exactly the canonical base-change pasting comparison, not an unspecified
  isomorphism.
- The sections clause is verified by the existing
  `AlgebraicGeometry.ProEtale.lowerStarComp_hom_app_hom_app` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso`, lines 81–88:
  for every `G : Sheaf (ProEt.topology T) A` and `V : R.ProEtᵒᵖ`,
  `((lowerStarComp A h₁ h₂).hom.app G).hom.app V` equals
  `G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op`.
  `Over.pullbackComp` goes from the single pullback to the iterated pullback;
  its inverse is the displayed iterated-to-single isomorphism in the node.
  Contravariance of `G` gives the required direction from sections on the
  iterated pullback to sections on the single pullback.
  Reading Mathlib's definition confirms that this is constructed from
  `pullbackLeftPullbackSndIso`, not from an arbitrary choice of isomorphism.
  This component lemma is supporting verification evidence in a separate
  existing module; the primary record points to the module defining the notion.

Dependency declarations used:

- `def-sfb-finite-lower-star` records
  `AlgebraicGeometry.ProEtale.lowerStar` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
  Its full definition is restriction of sheaves along
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ g`.
- The same dependency records
  `AlgebraicGeometry.ProEtale.lowerStar_obj_val_obj` in that module: evaluation
  at `V` is exactly evaluation of `G` at the base change of `V`.
- Its continuity declaration
  `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback` is in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
- The comparison uses Mathlib's `MorphismProperty.Over.pullbackComp` from
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction` and
  `Functor.sheafPushforwardContinuousComp'` from
  `Mathlib.CategoryTheory.Sites.Continuous`. Their full definitions were read.

Edge cases checked by inspecting the unrestricted binders and construction:
identity morphisms and arbitrary composites are included; schemes and test
objects may be empty; zero sheaves are included; nothing assumes nonempty
sections. The scheme universe `u` is arbitrary and the coefficient object
universe `u'` is independent; `Category.{u + 1} A` is the same size convention
as the recorded pushforward dependency. In particular there is no new equality
of site object and morphism universes. The construction is categorical and
places no characteristic restriction on schemes. There are no index-set or
degree bounds to check. There is no statement dispute or correction.

Searches (2026-10-16; machine-readable results in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder` with query
  `composition isomorphism of pushforward sheaves on small pro-etale sites given by restriction along pullback associativity`:
  eight hits, including `CategoryTheory.Functor.sheafPushforwardContinuousComp'`
  and generic module-sheaf pushforward comparisons; these give the general
  construction rather than a distinct pro-etale specialization to define.
- `msearch.py ... loogle` with query
  `Functor.sheafPushforwardContinuousComp, pullbackRightPullbackFstIso`:
  zero hits, unknown identifier `Functor.sheafPushforwardContinuousComp`.
- `msearch.py ... leansearch` with query
  `composition isomorphism for pushforward of sheaves along base change on small pro-etale sites`:
  eight hits, including `CategoryTheory.Functor.sheafPushforwardContinuousComp'`
  and its component formula; no reason to duplicate the upstream specialization.
- `msearch.py ... grep` with query
  `sheafPushforwardContinuousComp|lowerStarComp|pullbackRightPullbackFstIso`
  in `CategoryTheory`: 19 hits, including `Sites/Continuous.lean` and generic
  pullback-pasting lemmas. A focused direct `rg` also found the exact
  `MorphismProperty.Over.pullbackComp` in `MorphismProperty/OverAdjunction.lean`.
- Direct `rg` over the upstream `WeilConjectures` source found the exact
  definition at `SixFunctors/ProEtale/UpperLowerStar/Defs.lean:334` and its
  component formula at `UpperLowerStar/Iso.lean:83`.
- Literal search for the node id in the upstream source had no hits. Search
  of `dag/lean_names_upstream.json` did not list the exact declaration; the
  item's existing audit and direct source inspection supplied its location.
- Direct `rg` over `lean/Sheaf` found use of `ProEtale.lowerStarComp` in
  `Sheaf.AlgebraicGeometry.ComparisonDirectImage`, not another definition of
  this notion. The upstream declaration is therefore reused.

Validation: a scratch probe importing the existing `Iso` module was compiled
through `scompile.py Q53 def-sfb-finite-lower-star-comp` with auto-implicits
explicitly disabled. It checks the full types of the dependency, comparison,
and component formula. Compilation passed without warnings. `#print axioms`
on both the comparison and its section formula returned exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither reaches `sorryAx`.
No theorem was proved and no `sorry` was introduced.

Resumed-worker check (2026-10-16): reread the node, dependency declarations,
current blueprint and existing definition/component formula. The existing record
remains an exact match. The earlier attempt stopped during delivery-tool
worktree acquisition; this attempt reruns compilation and the required dry run.

## Second reading by Q53

I opened the node copy, the source blueprint place, the recorded dependency node,
and the upstream declarations before checking this item. The node's objects and
clauses, matched against the existing Lean, are:

- `h₁ : T ⟶ S` and `h₂ : S ⟶ R`, with arbitrary schemes `R S T : Scheme.{u}`.
  Lean binds exactly these objects and morphisms in the `Comp` section of
  `Defs.lean`; there are no properness, finiteness, weak-etaleness, or separation
  hypotheses.
- The coefficient category `A` and its category/abelian/Grothendieck assumptions
  are those of `def-sfb-finite-lower-star`. The declaration has the same `A` and
  category universe convention; the unused abelian and Grothendieck instances
  are omitted by elaboration. Thus the construction specializes to every
  coefficient category covered by the dependency.
- The pushforward composition clause is rendered by
  `ProEtale.lowerStarComp A h₁ h₂ : (h₁)_*[A] ⋙ (h₂)_*[A] ≅
  (h₁ ≫ h₂)_*[A]`. Lean's `⋙` is the node's “first `h₁`, then `h₂`”
  composition, hence agrees with `(h₂)_* ∘ (h₁)_*`.
- The right side is pushforward along the composite `h₁ ≫ h₂`, exactly the
  scheme composite in the node.
- The comparison is a natural isomorphism of sheaf-valued functors, so it is
  natural in the sheaf `G`, as required by the node's composition-isomorphism
  clause.
- For every `G : Sheaf (ProEt.topology T) A` and `V : R.ProEtᵒᵖ`, the supporting
  declaration `ProEtale.lowerStarComp_hom_app_hom_app` gives the component as
  `G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op`.
  `pullbackComp` has source the single pullback and target the iterated pullback;
  contravariance therefore restricts sections from
  `(V ×R S) ×S T` to `V ×R T`, the node's canonical-isomorphism direction.
  The definition passes its inverse as `eFG`, so this is the canonical pasting
  comparison rather than an arbitrary isomorphism.

No mismatch was found in the mathematical statement or in the first worker's
existing record. I kept that record unchanged and added this independent
reading. The component formula remains supporting verification evidence in
`Iso.lean`, rather than a second primary declaration in the `Defs` module. No
Lean module is written because the exact definition already exists upstream.
There are no new definition nodes, dependency modules, or statement corrections
to audit. The source is the blueprint node itself, not a Stacks tag; its parent
unit and chapter impose no further morphism hypotheses. I also read the shared
clone's exact `Defs.lean` and `Iso.lean` declarations and the framework note;
the signatures and canonical construction agree with the older checkout.

Edge cases remain covered: identity morphisms and arbitrary composites, empty
schemes and empty test objects, zero sheaves, and all characteristics are
allowed; there is no index set, degree, or nonemptiness assumption. The scheme
universe `u` and coefficient universe `u'` remain independent, with the same
`Category.{u + 1} A` convention as the dependency.

I independently repeated the three required kinds of search with different
queries (the machine-readable results are in `searches.jsonl`):

- LeanFinder: `natural equivalence between consecutive direct images of sheaves
  and direct image along composite induced by fibre product associativity`.
  Eight hits include `Functor.sheafPushforwardContinuousComp'` and generic
  module-sheaf comparisons, not a new pro-etale definition to write.
- LeanSearch: `restriction of sheaves functor composition canonical natural
  isomorphism from base change pasting`. Eight hits include the generic
  comparison's component formula and unrelated scheme-module restrictions.
- Grep through `msearch.py`: `pullbackComp|sheafPushforwardContinuousComp` in
  `CategoryTheory`, 25 hits, including the canonical `Over.pullbackComp` and
  generic sheaf pushforward comparison.
- Direct `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found the exact
  upstream pro-etale declaration and its component formula; the project uses
  this declaration rather than defining another one.

I read the actual data of `Over.pullbackComp`, constructed with
`pullbackLeftPullbackSndIso`, and the generic comparison's definition. There is
no hollow definition or new proof. The existing upstream docstrings describe
the canonical construction; no newly generated module needs a blueprint
source docstring. The node's `lean.statement` agrees verbatim with the
existing defining signature. The bound universes, coefficients, and scheme
morphisms were also checked in the elaborated type through `scompile.py`;
compilation was clean. Both the comparison and its component lemma have only
`propext`, `Classical.choice`, and `Quot.sound` in `#print axioms`.
