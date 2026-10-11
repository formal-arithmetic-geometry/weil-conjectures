## Worker report

The module `Sheaf.AlgebraicGeometry.LimitAffineTransition` states
`AlgebraicGeometry.exists_limit_affine_transition`, with proof `sorry` only.
No definitions, extra nodes, or dependency modules were needed. The item node
changes only in `lean`.

Hypothesis and conclusion correspondence:

- A directed set I is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Stacks directed sets are nonempty
  (01YX explicitly uses this); nonemptiness is part of the notion, not an
  additional restriction. No antisymmetry is imposed.
- The inverse system of schemes and its identities/composition laws are
  `(D : Iᵒᵖ ⥤ Scheme.{u})`. An arrow from i to j in Iᵒᵖ means j ≤ i
  in the original preorder.
- Every transition is affine:
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- Existence of the scheme limit with its actual projections is
  `∃ c : Cone D, Nonempty (IsLimit c) ∧ ...`.
- Every projection is affine: `∀ i : Iᵒᵖ, IsAffineHom (c.π.app i)`.
- Every stage 0 and every open U₀ (not necessarily affine or quasi-compact)
  are the binders `(i : Iᵒᵖ) (U : (D.obj i).Opens)`.
  `opensDiagram D i U` has objects `D.map j.hom ⁻¹ᵁ U` for `j : Over i`.
  The thin category `Over i` is exactly the upper tail of the original
  preorder, with the unique arrow to i recording the inequality.
- The inverse image under the projection with the restricted projections
  is Mathlib's `opensCone D c i U`; its apex is `c.π.app i ⁻¹ᵁ U` and
  its legs are the restrictions `resLE` of the original legs.
  `Nonempty (IsLimit (opensCone D c i U))` states precisely the limit
  universal property in schemes.
- Affineness of every restricted transition is
  `∀ {j k : Over i} (f : j ⟶ k),
  IsAffineHom ((opensDiagram D i U).map f)`.
- The affine special case is the implication with premise
  `∀ i : Iᵒᵖ, IsAffine (D.obj i)` and an isomorphism
  `e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ))`.
  Here `D.op ⋙ Scheme.Γ` is the direct system of global-section rings.
  The equation for each i asserts that e identifies the projection with
  the spectrum of the ring coprojection, using the canonical map
  `ΓSpec.adjunction.unit.app (D.obj i) : D.obj i ⟶ Spec Γ(D.obj i, ⊤)`.
  Under the affine premise this canonical map is an isomorphism.
  Equality of schemes in the source is interpreted as the canonical
  projection-compatible isomorphism, not literal equality of bundled data.

Dependencies and definitions read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. Read the full structures and docstrings.
- `def-weil-pbc-scheme-conventions` is a conventions-only record with no
  declaration/module. Its affine clause uses `IsAffineHom` from
  `Mathlib.AlgebraicGeometry.Morphisms.Affine` and `IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`; no private predicate is introduced.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit` and
  `colimit.ι`, `Mathlib.CategoryTheory.Limits.HasLimits`, together with
  `Cone` and `IsLimit` for the dual universal property. Read the `limit`
  and `Cocone` declarations from which the dual declarations are generated,
  and the `IsFiltered` signature/docstring.
- Mathlib `opensDiagram` and `opensCone` from
  `Mathlib.AlgebraicGeometry.AffineTransitionLimit` supply the exact
  restricted functor and cone. Their complete definitions were read.
  This single import supplies all definitions actually used in the file.

Source: read Stacks https://stacks.math.columbia.edu/tag/01YX and
https://stacks.math.columbia.edu/tag/01YW online because the cited local
`literature/stacks-project/limits.tex` is not present on this machine.
The declaration docstring carries all nine proof steps and their DAG dependencies.

Edge cases checked before writing:

- Empty index sets are not directed sets in the cited Stacks convention;
  `[Nonempty I]` records that convention. The node's proof also mentions
  a possible empty diagram separately, but its statement is about directed sets.
- A singleton index gives the original scheme and its identity projection;
  the affine case becomes the usual affine scheme/global sections identification.
- Empty schemes are allowed; there are no nonempty-point hypotheses. In the
  affine case their global-section ring may be the zero ring, whose spectrum
  is empty; no nontriviality hypothesis excludes it.
- Empty opens and the full open are allowed. The former yields the empty
  restricted cone, the latter the tail of the original cone. Opens need not
  be affine, compact, or separated.
- Preorders need not be antisymmetric. All universes and variables are explicit;
  the arbitrary `u` follows the universe convention of Mathlib's restricted
  diagrams. No finiteness, Noetherian, characteristic, or field assumption.

Searches made:

- `msearch.py` LeanFinder: "An inverse system of schemes with affine transition
  morphisms has a limit with affine projections and inverse images of opens
  commute with the limit". Eight results, including `isAffineHom_π_app`,
  all assuming a supplied limit cone; none supplies general existence.
- `msearch.py` Loogle:
  `CategoryTheory.Limits.HasLimit, AlgebraicGeometry.IsAffineHom`:
  zero hits.
- `msearch.py` grep:
  `hasLimit|HasLimit|isLimitOpensCone|isAffineHom_π_app`, AlgebraicGeometry:
  16 hits, including the opens API and affine-scheme limits; no existence
  result for general schemes with affine transitions.
- `msearch.py` LeanSearch: "Existence of inverse limits of schemes with affine
  transition maps": service unavailable (Internal Server Error), recorded
  as unavailable rather than as a mathematical negative result.
- `rg` in `WeilConjectures` and `lean/Sheaf` for
  `limit_affine_transition|hasLimit.*[Aa]ffine|affine.*[Hh]asLimit|lem-weil-pbc-limit-affine-transition`:
  only proof-docstring citations in existing Sheaf modules.
- Read and searched the source overlay
  `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`
  for `01YX|01YW|HasLimit|hasLimit|exists.*[Ll]imit`: results concern a
  supplied limit cone or other limit properties, not the desired existence.
- Checked the proposed declaration name against Mathlib, WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: server `scompile.py M1 lem-weil-pbc-limit-affine-transition
.../LimitAffineTransition.lean` succeeded in 1.8 seconds, with no warnings
or errors. No statement dispute or statement correction.

## Second reading by M1

I reread the node statement clause by clause against the Lean declaration
`AlgebraicGeometry.exists_limit_affine_transition`.

- The directed index is rendered by `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`; this matches the Stacks directed-set
  convention, with no antisymmetry or finiteness added.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`; arrows therefore encode the
  stated inverse-system direction. The affine-transition hypothesis is exactly
  `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- Existence of the limit and its cone is
  `∃ c : Cone D, Nonempty (IsLimit c)`. The projection clause is exactly
  `∀ i, IsAffineHom (c.π.app i)`.
- For each stage and arbitrary open, the Lean binders are
  `(i : Iᵒᵖ) (U : (D.obj i).Opens)`. The conclusion uses Mathlib's
  `opensCone D c i U` and requires `Nonempty (IsLimit ...)`, then requires
  `IsAffineHom` for every map of `opensDiagram D i U`; these are precisely the
  restricted inverse-image cone and affine restricted transitions.
- The affine-stage clause has the exact premise `∀ i, IsAffine (D.obj i)` and
  supplies an isomorphism
  `e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ))`, with the displayed equation
  against each `c.π.app i` and `ΓSpec.adjunction.unit.app`. This is the
  projection-compatible categorical form of the source's canonical equality.

I checked edge cases: `[Nonempty I]` excludes the empty index as required by the
Stacks definition; singleton and preorder (non-antisymmetric) indices work;
empty schemes and zero rings are not excluded; empty and full opens are covered;
no characteristic, Noetherian, separated, quasi-compact, or field assumptions
were introduced; universes are explicit and shared.

I searched Mathlib, the source overlay, `WeilConjectures`, and `lean/Sheaf`
(using LeanFinder/Loogle/grep searches recorded in the worker report). No
existing declaration states this existence theorem; the Mathlib affine-transition
lemmas all assume a supplied limit cone. The dependency declarations and
`opensDiagram`/`opensCone` definitions were inspected and are the intended ones.

No mismatch was found, so no Lean or node correction was needed. The module
compiles cleanly with `scompile.py`; the only proof placeholder is the required
statement `sorry`.
