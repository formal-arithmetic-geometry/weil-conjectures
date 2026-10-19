# Stage-2 repair: lem-trf-nodal-geometric-fibres-reduced

## Worker report

The returned head 22cbfe7bf6cd contained a stage-1 report and no Lean declaration.
This delivery supplies `Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced`,
with theorem `AlgebraicGeometry.nodal_geometric_fibres_reduced` and the explicit
canonical helper `AlgebraicGeometry.Scheme.Hom.nodalCompletedLocalScalar`.
The theorem has the sole postponed proof, `by sorry`. The helper has real data:
it composes the scalar-to-stalk map of `Spec Ω`, the structure morphism on stalks,
and the canonical map from the local ring to its maximal-ideal completion.
Its scalar equation on the ring equivalence expresses the requested Ω-algebra
isomorphism, including the specified coefficient action.

I read Stacks `curves.tex` Tag 0E37 (`lemma-facts-about-nodal-curves`,
lines 4546–4576), and the completed-local-ring discussion and Tag 0C47
(`definition-nodal`, lines 3780–3808). I also read the current main-20261015
blueprint ancestor `lem-trf-local-term-locality` and its proof, and the item's
recorded source and five proof steps. The source's reducedness argument checks
smooth or uv completed local rings over an algebraic closure. This item makes
that input explicit after every algebraically closed extension. The existing
statement and the five-step proof are preserved; only `lean` changes.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`.
- A scheme C over k: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  This is its structure morphism, as allowed by the recorded finite-type definition.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the two clauses of
  `def-weil-finite-type-morphism`. No separatedness hypothesis is present.
- Every algebraically closed extension Ω/k: `∀ (Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k))`.
  Affine-spectrum duality identifies g with the ring map k → Ω; between fields
  this is injective, and equivalently supplies the recorded `Algebra k Ω`.
  This quantifies over every extension structure, not only a chosen algebraic closure.
- The base change C_Ω: `pullback (C := Scheme.{u}) f g`, with structure map
  `pullback.snd f g`. All pullbacks specify their ambient category explicitly.
- Either empty: the first alternative is `IsEmpty ↥(pullback ... f g)`.
- Every irreducible component has dimension 1: the second alternative starts with
  `∀ Z ∈ irreducibleComponents ↥(pullback ... f g), topologicalKrullDim Z = 1`.
  Z has the subspace topology; this does not replace pure dimension by the weaker
  assertion that the whole scheme merely has dimension 1.
- Every closed point: `∀ x : ↥(pullback ... f g), x ∈ closedPoints ... → ...`.
  There is no condition on other points in this hypothesis.
- Smooth at x over Ω: `x ∈ (pullback.snd f g).smoothLocus`.
  Local finite presentation is inferred from local finite type over a Noetherian
  field by `Noetherian.lean:266–275`; it is not a further hypothesis.
- Or the completed nodal local ring: the existential `e` is a ring equivalence
  from `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  (X.presheaf.stalk x)` to `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`,
  with both variables explicitly typed in `MvPowerSeries (Fin 2) Ω`.
  `∀ a : Ω, e (q.nodalCompletedLocalScalar x a) =
  Ideal.Quotient.mk _ (MvPowerSeries.C a)` is exactly preservation of Ω-scalars.
  An arbitrary ring isomorphism alone would have omitted this part of the node.
- Geometric reducedness: `GeometricallyReduced f`. I opened
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`, whose class field is
  `geometrically IsReduced f`, and `Geometrically.Basic`, whose definition
  quantifies over every field and every morphism `Spec L ⟶ Spec k`, with any
  pullback square. Thus its conclusion says precisely that C_L is reduced for
  every L/k, independently of the selected pullback model.
- No properness, separatedness, connectedness, marking, nonemptiness or
  characteristic condition is imposed. All universes and variables are explicit;
  geometric fields use the scheme universe, as in Mathlib's geometric properties.
  The test-field universe is not independently smaller than that of k or C.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs:170–180`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType:38–47`, and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact:37–47`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs:90–101`;
  ring maps are encoded contravariantly as maps of affine spectra in the signature.
- `def-weil-algebraic-closure`: the required notion is `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic:58–65`; algebraicity of Ω/k is not assumed.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:94–115`.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible:105–108`, maximal irreducible subsets.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension:35–41`, applied to each component's subtype.
- `def-sbc-smooth-morphisms`: `Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth:57–65`, and
  `Scheme.Hom.smoothLocus`, `mem_smoothLocus`, at lines 303–309.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic:167–173`; its ring structure and
  canonical scalar map are from `Mathlib.RingTheory.AdicCompletion.Algebra:98–118`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic:84–87`, here indexed by `Fin 2`.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  `Mathlib.AlgebraicGeometry.Properties:68–85`, with its stalk characterization.
- `def-weil-closed-points`: `closedPoints`,
  `Mathlib.Topology.JacobsonSpace:37–43`, definitionally closed singletons.

The declared proof inputs are imported: the published finite-purely-inseparable
criterion, the upstream smooth-geometrically-reduced result, and Mathlib's
Noetherian, finite-type, completion-flatness/local-ring, faithfully-flat,
power-series-domain, and affine-pullback APIs. The theorem docstring follows all
five node proof steps and names every nontrivial input used there. The scalar
helper and module docstrings carry the source and blueprint id as well.

Searches run in this repair:

1. `msearch.py` LeanFinder: "A finite type nodal curve over a field is
   geometrically reduced". Eight hits, including `Algebra.IsGeometricallyReduced`,
   its reducedness consequence, and Weierstrass-curve facts. None states this
   scheme theorem with its completed-local-ring hypotheses.
2. `msearch.py` Loogle: `GeometricallyReduced`. Zero hits, with the explicit
   diagnostic "unknown identifier 'GeometricallyReduced'"; this is not evidence
   of absence, and I therefore opened the existing scheme definition directly.
3. `msearch.py` grep: `nodal|ordinaryDouble|ordinary.double`, subdirectory
   `AlgebraicGeometry`: zero Mathlib hits.
4. `msearch.py` LeanSearch: "A scheme of finite type over a field with only smooth
   points and ordinary nodes after algebraically closed base change is
   geometrically reduced". Eight hits giving algebraic geometric-reducedness
   definitions and tests, not the nodal scheme assertion.
5. `rg` in the source project and `lean/Sheaf` for nodal, geometric reducedness,
   the item id and the proposed declaration names, and in the upstream name index.
   The source has the general `GeometricallyReduced` API and smooth case; the side
   library has `HasNodalGeometricFibres` and nodal-family results. The existing
   fibre predicate imposes nonemptiness and connectedness and records only a ring
   equivalence; it cannot replace the exact hypothesis of this item. The existing
   completed-ring/model helpers merely abbreviate the Mathlib constructions used
   directly here. No declaration states this item's assertion. No existing
   canonical map with the type of `nodalCompletedLocalScalar` was found.

Edge cases checked: the empty scheme and empty geometric base change satisfy the
empty alternative and are reduced; the affine line uses the smooth alternative;
the affine uv curve uses the nodal alternative and is reduced by injection into
the product of its axes; finite disjoint unions are allowed and need not be
connected. Characteristic 2 causes no change to the uv model. The quantifier
includes trivial extensions and arbitrary purely inseparable extensions. A
nonreduced doubled line fails the smooth/nodal condition, so the hypothesis has
not become vacuous. No new statement correction or disputed statement is needed.

## Second reading by Q36

I performed a separate clause-by-clause rereading of the completed module against
the unchanged node and Stacks 0E37/0C47. This is the author's second pass; the
maintainer supplies the independent review, as in the dispatcher brief.

The field binder, C and its structure morphism, and both finite-type classes
match the opening sentence exactly. The Ω/Field/IsAlgClosed/g quantifier matches
all algebraically closed extensions via affine-spectrum duality, including all
choices of the k-map. The actual fibre product is the object whose components,
closed points, stalks and completion appear throughout. I checked the parentheses
of the empty-or-conjunction hypothesis: the closed-point clause is inside the
same second alternative as the dimension clause, and its smooth-or-nodal
alternative is evaluated at each closed point individually. There is no global
choice that would force all points to be of one kind.

I checked that dimension is imposed on every maximal irreducible subset, not just
on the entire topological space. `closedPoints` uses closed singletons exactly as
the dependency node says. Smooth-locus membership is relative to the second
projection to `Spec Ω`. No local-finite-presentation assumption was added: its
instance is derived from finite type over a field. Completion is at the maximal
ideal of that same local ring. Both model variables range in `Fin 2`, and the
relation is the principal ideal generated by their product.

The first draft used a bare ring equivalence. That omitted "as an Ω-algebra";
the final file repairs it with the explicitly constructed scalar map and the
scalar-preservation equation on e. I opened the scalar helper's body: it passes
Ω through the stalk of its own spectrum, then through q's stalk map, then into
the local completion. The equation compares it to the constant-coefficient map
into the quotient, so it specifies precisely the intended coefficient action.
No arbitrary map, existence choice, extra structure or postponed definition data
is used. The first drafts also had ambiguous pullback type coercions; the final
signature explicitly selects `Scheme.{u}` and uses the underlying point type.

Finally I opened the full `GeometricallyReduced` definition and its underlying
`geometrically` definition. Their quantifier is every field L and morphism
`Spec L ⟶ Spec k`, so the conclusion preserves the arbitrary-extension clause.
The listed absence of properness, separatedness, connectedness and marking is
respected. Empty schemes, characteristic 2, disconnected curves and inseparable
extensions remain included. I verified that only the item's `lean` field differs
from the repository node, its recorded signature is copied verbatim from the
file, and both declarations have source/blueprint docstrings. The theorem's
five-step proof docstring matches the existing node proof; no theorem is proved
in this stage.

Return repair checklist: H2/H3 are addressed by the actual theorem, complete Lean
record and exact clause mapping above; H1/H11 by the worker report and substantive
second reading; H8 by module, helper and theorem source/blueprint docstrings,
including the full natural-language proof plan. Every delivered module is
compiled through `scompile.py`, followed by the prescribed `deliver2.py` dry run
and delivery.
