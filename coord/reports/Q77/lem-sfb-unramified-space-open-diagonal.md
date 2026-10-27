## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedSpaceOpenDiagonal` states
`AlgebraicGeometry.AlgebraicSpace.unramified_space_open_diagonal`, with `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
The node changes only in its `lean` field.

Source read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-diagonal-unramified-morphism` (Tag 05W1), lines 7508–7575, and
`lemma-unramified-local` (Tag 03ZK), lines 7423–7471. Part (1) of 05W1 has a
scheme target here; clause (7) of 03ZK, using its identity target chart, gives
exactly the hypothesis in the node. The seven proof steps of the node appear
in the theorem docstring, including the scheme tests in each descent step.

Hypothesis and clause correspondence:

- The arbitrary scheme S is `{S : Scheme.{u}}`.
- The S-scheme T is `(T : Over S)`; its structure morphism to S is part of T.
- The algebraic space A over S is `(A : AlgebraicSpace S)`, the recorded fppf
  sheaf with representable diagonal and an etale surjective scheme atlas.
- The morphism f : A → T is `(f : A.obj.obj ⟶ yoneda.obj T)`: a natural
  transformation of functors of points over S, exactly the stipulated morphism.
- Every scheme V over S and chart V → A is quantified in `hf` by
  `∀ (V : Over S) (a : yoneda.obj V ⟶ A.obj.obj)`.
- The representable etale requirement on that chart is `IsEtale a`; this is
  the dependency's scheme-test definition, not a condition on geometric points.
  There is no surjectivity requirement on individual charts.
- The composite V → T is `yoneda.preimage (a ≫ f)`, an arrow in `Over S`.
  Its underlying scheme map is `.left`. The required unramifiedness is
  `IsUnramified (yoneda.preimage (a ≫ f)).left`: locally finite type and
  open-immersion scheme diagonal, precisely the recorded scheme notion.
- The relative self-product is the codomain of `pullback.diagonal f`, the
  categorical pullback in presheaves of sets. Thus it is evaluated on every
  test scheme, and it retains restriction maps and scheme structures.
- The conclusion is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (pullback.diagonal f)`.
  Unfolding the recorded definition quantifies over every `Z : Over S` and
  `b : yoneda.obj Z ⟶ pullback f f`, and supplies a scheme `U : Over S`,
  a projection `p : U ⟶ Z`, a map to A, and an `IsPullback` square of presheaves,
  together with `IsOpenImmersion p.left`. This is exactly representability of
  Z ×_(A ×_T A) A by an open subscheme of Z: an open immersion identifies U
  with the open subscheme on its image. The explicit clause is the definition
  of the main conclusion, so is not duplicated as a second conjunct.

Dependency declarations used (full signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`, and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  by the recorded chart predicate and the proof's scheme-etale inputs.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `CategoryTheory.Limits.pullback.diagonal` supplies the canonical diagonal.
  There is no privately chosen map or replacement definition.

The stated proof dependencies are retained as plain imports:
`Mathlib.AlgebraicGeometry.Pullbacks` (scheme fibre products),
`Mathlib.CategoryTheory.Limits.MorphismProperty` (etale finite-limit calculus),
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`
(`AlgebraicGeometry.Etale.of_comp_of_surjective_etale`), and
`Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
(`AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`). The composition,
open-immersion-to-etale, and base-change inputs also occur in the already
publicly imported Etale module. No proof dependency is omitted for a cycle.

Edge cases checked before writing:

- If A is represented by a scheme, the assertion recovers the open diagonal
  of the scheme unramified morphism by the identity source chart.
- Empty A and empty Z are permitted. The empty equality locus is an open
  subscheme, and no nonemptiness hypothesis was introduced.
- For A = T ⊔ T, the equality locus of sections choosing different summands
  is empty; the conclusion does not assert equality of all sections.
- Nonreduced Z and nonreduced chart schemes are allowed. The `IsPullback`
  condition is a natural-transformation universal property on all schemes,
  not equality on field-valued or geometric points.
- No separation, Noetherian, finite presentation, quasi-compactness, or
  surjectivity hypothesis on f was added. All test schemes and values use
  the same arbitrary `u` as the existing algebraic-space size convention.

Searches (2026-10-24):

- `msearch.py ... leanfinder "An unramified morphism from an algebraic space
  to a scheme has representable open immersion diagonal"`: eight hits,
  including `FormallyUnramified.isOpenImmersion_diagonal`, but all relevant
  diagonal results have scheme source and target.
- `msearch.py ... loogle "AlgebraicGeometry.FormallyUnramified,
  AlgebraicGeometry.IsOpenImmersion"`: two hits, the scheme diagonal instance
  and its converse. Neither states the algebraic-space result.
- `msearch.py ... leansearch "The diagonal of an unramified morphism of
  algebraic spaces is a representable open immersion"`: eight hits; scheme
  unramified, separated and immersion diagonal results, no exact match.
- `msearch.py ... grep "AlgebraicSpace|isOpenImmersion_diagonal|Unramified.*diagonal"
  AlgebraicGeometry`: two hits in Mathlib's scheme FormallyUnramified module.
- `rg` of the project `lean/WeilConjectures` for unramified/open/diagonal
  names and `rg` for this node id: scheme results and no node attachment.
  `dag/lean_names_upstream.json` also has no exact algebraic-space result.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for unramified diagonal and
  `IsRepresentableWith.*IsOpenImmersion`: existing general representable-open
  notions and consumers of this missing lemma, no exact statement.
  The adjacent `lem-sfb-space-unramified-open-diagonal` is the converse
  implication and has no Lean record; it does not duplicate this result.

Validation: prescribed `scompile.py Q77 lem-sfb-unramified-space-open-diagonal`
compiled the delivered module on the server in 2.6 seconds, with no errors or
unexpected warnings. Its local attempt reported ENOSPC; the wrapper's normal
server confirmation succeeded. Only the theorem proof is postponed.

## Second reading by Q77

A separate rereading of the node, the file, both source passages, and the
three representation/unramified definitions confirms the correspondence above.
This pass was performed by the same dispatched worker; the brief prohibits
starting another agent, and the maintainer supplies independent review.

In particular, `IsEtale a` already includes representability, so no separate
or stronger chart condition is needed. Yoneda preimage applies to the actual
composite, not an arbitrary scheme arrow. The conclusion's `IsPullback` square
has upper-left `h_U`, upper-right A, lower-left `h_Z`, lower-right A ×_T A,
with the lower map equal to the arbitrary b. Therefore the open projection
is exactly the requested scheme base change. No source statement, hypothesis,
or conclusion required correction, and no mathematical mismatch was found.
