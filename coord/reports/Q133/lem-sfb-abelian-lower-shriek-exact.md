## Worker report

The module `Sheaf.CategoryTheory.AbelianLowerShriekExact` states
`CategoryTheory.Functor.abelianLowerShriek_additive_shortExact`, with its sole
proof `sorry`. The node statement and all other original fields are unchanged;
only its `lean` record is supplied. No new definitions or dependency modules.

Hypothesis and conclusion correspondence:

- Small-site universes: explicitly bound `u w`; `C D : Type u` with
  `SmallCategory` instances. Both the object and arrow sets fit the common
  small-site bound. Coefficients are `AddCommGrpCat.{max u w}`, allowing any
  further coefficient universe while containing the sites. A common upper
  bound represents sites originally presented at different smaller levels.
- The sites are `J : Precoverage C`, `K : Precoverage D`, with
  `hJ : J.IsSiteForCoverings` and `hK : K.IsSiteForCoverings`; sheaves use the
  generated topologies `J.toGrothendieck`, `K.toGrothendieck`.
- The functor is `F : C ⥤ D`. Cocontinuity is exactly
  `F.IsCocontinuous J.toGrothendieck K.toGrothendieck`, the first clause of the
  recorded special-cocontinuity definition; none of its other special clauses
  is assumed. Stacks continuity is `hcover` together with the stated global
  pullback preservation, which implies preservation of covering pullbacks.
- Existence of all fibre products and equalizers is `[HasPullbacks C]` and
  `[HasEqualizers C]`. Preservation of their universal properties is
  `[PreservesLimitsOfShape WalkingCospan F]` and
  `[PreservesLimitsOfShape WalkingParallelPair F]`, respectively. These classes
  do not demand all pullbacks/equalizers in D, only that image limit cones are
  limits there. No terminal object in either category is assumed.
- `hcontinuous` is an existential conclusion, not an additional hypothesis.
  It records the sheaf-theoretic consequence of Stacks continuity needed to
  form Mathlib's precomposition functor. The latter is literally
  `@sheafPushforwardContinuous ... F AddCommGrpCat ... hcontinuous` and sends
  a sheaf N to `F.op ⋙ N.obj`, as its source definition shows.
- For every chosen `A : Sheaf J ... ⥤ Sheaf K ...`, the adjunction binder
  `A ⊣ ...sheafPushforwardContinuous...` is the required natural Hom
  bijection; it imposes no choice of a particular construction for A.
- Additivity is `∃ _ : A.Additive, ...`. The witness is used as a class
  hypothesis solely to elaborate the standard `S.map A` (additivity implies
  preservation of zero morphisms). It is a conclusion, not an assumption.
- Every sequence is `S : ShortComplex (Sheaf J ... AddCommGrpCat ...)` with
  `S.ShortExact`; this means exactness, a monomorphic first arrow and an
  epimorphic second arrow, i.e. the two zero ends of the written sequence.
  Its conclusion `(S.map A).ShortExact` applies A to its three objects and
  its two maps. This is exactly preservation of every short exact sequence.
- No slice equivalence or terminal-object hypothesis appears. No set-valued
  exactness assertion, or finite-limit preservation for set-valued colimits,
  is used as a conclusion.

Dependency declarations read and used:

- `def-weil-size-convention`: its recorded metatheoretic convention has no Lean
  declaration/module; the explicit universe parameters implement it.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: actual covering-presieve
  site axioms with bind composition and only covering pullbacks.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`,
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings`: its first clause
  is Mathlib's `Functor.IsCocontinuous`; its next clauses give the same
  cover-image and covering-pullback formulation of continuity used here.
  The full special-cocontinuity predicate would be strictly stronger and is
  deliberately not used as a hypothesis.
- Mathlib `Sites.Continuous`, `Functor.sheafPushforwardContinuous`: canonical
  precomposition on sheaves, with `Functor.IsContinuous` its typing witness.
- Mathlib `ShortComplex.ShortExact`, `ShortComplex.map`, and `Functor.Additive`:
  the standard sequence, image and additive-functor notions.

Proof dependencies: private imports retain
`WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf`,
Mathlib `Sites.Pullback` (the recorded
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`),
`Limits.Preserves.FunctorCategory` (`preservesFiniteLimits_of_evaluation`),
`Sites.Limits` (sheaf inclusion creates limits), and `Sites.Sheafification`
(exact sheafification). `lem-sfb-almost-filtered-abelian-colimits` currently
has no Lean record or Mathlib match, so no module can yet be imported for it;
its precise use remains in the theorem's proof docstring. It is a proof-only
prerequisite, not an object needed to type the present statement. The recorded
upstream continuity theorem has the older strict composition instances; the
statement here retains the current site interface, as does the already landed
`sheafPullback_preserves_pullbacks_and_equalizers`. Its continuity conclusion
can instead use the general generated-topology continuity criterion from
Mathlib, rather than adding those older strict instances.

Edge cases checked mathematically before writing: empty source/target sites;
empty comma categories (abelian colimit is the zero group); disconnected
categories with pullbacks and equalizers but no terminal object; zero sheaves
and the zero short exact sequence; identity functors; arbitrary chosen left
adjoints isomorphic to the constructed one. There are no nonemptiness, terminal
object, local equivalence or representable-flatness constraints that exclude
these cases. For a discrete site with multiple objects, arbitrary coproducts
of abelian groups give the expected exact left adjoint. Both limit-shape
hypotheses refer to universal properties, not to equality of chosen objects.

Searches made:

- `msearch.py leanfinder`: "The left adjoint to precomposition on abelian
  sheaves along a continuous cocontinuous functor preserving pullbacks and
  equalizers is additive and exact without terminal objects". Eight hits:
  continuous/cocontinuous adjunctions and sheafification compatibility; no
  theorem proving this abelian exactness criterion.
- `msearch.py loogle`: `"sheafPullback", "PreservesFiniteLimits"`. Three hits
  in Mathlib `Sites.Pullback`; reading their full context shows extra
  `RepresentablyFlat` and presheaf-Kan-extension finite-limit preservation
  assumptions. None is the node's statement.
- `msearch.py grep`: `lowerShriek|lower_shriek|[Pp]reserves.*[Ee]qualizer`
  under `CategoryTheory/Sites`. Seven hits, chiefly equalizer conditions and
  unrelated sheaf results; no abelian lower-shriek exactness theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id and abelian
  lower-shriek exactness, and in `dag/lean_names_upstream.json`: no existing
  declaration of the item. The module `LocalSliceModuleShriekExact` cites
  this node as a prerequisite; it proves a different module-sheaf assertion
  with additional slice hypotheses. `SiteLeftAdjointConnectedLimits` concerns
  set-valued pullbacks/equalizers, not abelian exactness.
- `rg` for the proposed declaration name across Mathlib, both project roots
  and the upstream-name index: no clash.

Source inspected: `literature/stacks-project/sites-modules.tex`,
`lemma-exactness-lower-shriek` (Tag 04BH), hypotheses (a)-(c), conclusion and
proof. Its assumptions are precisely continuous, cocontinuous, and preservation
of existing fibre products and equalizers. The docstring gives all seven DAG
proof steps, including the almost-filtered abelian-colimit input, the empty
case, the comparison of left adjoints and the cokernel adjunction argument.

No statement correction or disputed statement.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
