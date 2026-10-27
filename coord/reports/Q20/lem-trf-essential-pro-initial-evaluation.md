## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProInitialEvaluation`
states `CategoryTheory.essentiallyConstantPro_initial_evaluation`. Its sole theorem
has proof `sorry`; no definition or auxiliary theorem is introduced.

Hypothesis and conclusion correspondence:

- The categories are `{J : Type uJ} {C : Type uC}` with
  `[Category.{vJ} J] [Category.{vC} C]`. All four universes are explicit and independent.
- The functor and value are `(G : J ⥤ C) (X : C)`.
- The specified initial stage is `(i : J) (hi : IsInitial i)`.
  The unique morphism iota_j is the existing Mathlib map `hi.to j`.
- `(h : IsEssentiallyConstantProDiagram G X)` uses the dependency's exact predicate.
  Its first conjunct supplies `IsCofiltered J`, and its remaining conjuncts express
  existence of a natural cone and a retraction/factorization witness. As in the
  dependency's existing Hom-colimit consumer, the theorem then quantifies over
  every specified cone and witness. The existential content of h adds no constraint
  beyond cofilteredness and the explicit witness: those data construct h directly.
  No cone or retraction is selected from h for the conclusion.
- `∀ (u : (Functor.const J).obj X ⟶ G)` is the specified family of maps X → G(j)
  with precisely its required naturality, bundled as a natural transformation.
- `∀ (j₀ : J) (r : G.obj j₀ ⟶ X)` makes the assertion apply to every witness.
  The premise `u.app j₀ ≫ r = 𝟙 X` is r composed with u_j₀ equal to the identity.
- The other premise is exactly `∀ j, ∃ k, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
  G.map b = G.map a ≫ r ≫ u.app j`, the common-stage factorization of the node.
- `IsIso (u.app i)` is invertibility of the specified cone leg.
- The inverse w is written explicitly as `G.map (hi.to j₀) ≫ r`.
  `u.app i ≫ (G.map (hi.to j₀) ≫ r) = 𝟙 X` is w composed with u_i equal to 1_X.
  `(G.map (hi.to j₀) ≫ r) ≫ u.app i = 𝟙 (G.obj i)` is u_i composed with w equal to 1_G(i).
- `∀ j : J, u.app j = u.app i ≫ G.map (hi.to j)` is the asserted formula for
  every cone leg. Lean's composition notation reads from left to right.

Dependency declarations read and used:

- `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`,
  `CategoryTheory.IsEssentiallyConstantProDiagram`: its complete body is the
  cofilteredness conjunct, natural cone, stage, retraction identity and factorization.
  Both statement and proof depend on this node; its module is publicly imported.
- `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal`,
  `CategoryTheory.Limits.IsInitial` and `CategoryTheory.Limits.IsInitial.to`:
  initiality and its canonical unique outgoing arrows, with their signatures and
  docstrings checked in the source.

Source check: read `literature/stacks-project/categories.tex`, Definition
`definition-essentially-constant-diagram` (Tag 05PU), part (2)(a)-(b), including
the specified cone, retraction direction, and common earlier stage. The node is
the stated elementary consequence, with all three proof steps reproduced in the
theorem docstring. No source statement is changed.

Edge cases checked before writing:

- An empty J is excluded by the node's own initial object i, and also by cofilteredness.
- With a singleton index, the factorization at i forces r followed by u_i to be
  the identity, while the retraction premise supplies the other identity.
- A witness stage different from i is allowed. Initiality alone identifies the
  two composites i → k → i and i → k → j₀ used in the inverse calculation.
- An arbitrary category C, including one with zero objects or a one-object category,
  is allowed. No additive, limit-existence, or eventual-transition-isomorphism
  hypothesis appears. All categories may have distinct object and morphism universes.
- Arbitrary specified cones and arbitrary valid witnesses remain universally
  quantified, so there is no replacement by a conveniently chosen cone or inverse.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query "Given an essentially constant pro diagram
  with a specified cone and retraction witness, the leg at an initial object is an
  isomorphism with inverse given by the retraction composed with the initial transition"
  returned eight hits. The closest is `Limits.IsLimit.isIso_π_app_of_isInitial`;
  the others concern limit projections or `Functor.IsEventuallyConstantTo`.
- `msearch.py ... loogle '"IsInitial", "IsLimit"'` returned five hits, including
  the same limit-cone lemma and unrelated disjoint coproduct criteria.
- `msearch.py ... leansearch` with query "An essentially constant pro diagram
  evaluated at an initial object has cone leg an isomorphism" returned eight hits
  concerning chosen limits, eventual constancy, and cones from initial stages.
- `msearch.py ... grep` with regex
  `IsEssentiallyConstantPro|isIso_π_app_of_isInitial|initial.*[Ee]ssentially|[Ee]ssentially.*initial`
  in Mathlib/CategoryTheory returned seven hits, primarily finally-small results
  and the limit-cone lemma. Its full signature requires `IsLimit c` and does not
  state the specified witness formula, so it is not this node's statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for essential constancy and initiality
  found the recorded definition, the Hom-colimit result, the cofinal-restriction
  equivalence, and consumers, but no theorem with this specified-witness conclusion.
  Read the definition and relevant existing consumer signatures in full.
- `rg -n 'lem-trf-essential-pro-initial-evaluation' lean/WeilConjectures` returned no
  hits. A name search for `essentiallyConstantPro_initial_evaluation` in Mathlib,
  both project roots and `dag/lean_names_upstream.json` returned no hits.

There are no node faults, statement disputes, new nodes, or dependency repairs.

## Second reading by Q20

No second worker reading was performed: this dispatcher assignment explicitly
prohibits starting other agents and requires direct delivery. The maintainer's
independent review reads this delivery. The hypothesis and clause mapping above
records the worker's own check, not an independent review.
