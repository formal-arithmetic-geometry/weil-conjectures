## Worker report

The delivery states precisely the missing parts of the node in
`Sheaf.AlgebraicGeometry.ShiftedEtaleLinesLocality`, using the existing upstream
notion and existing theorems for the other clauses. No definition or theorem is
copied. Two new theorems have `sorry` proofs; definitions have no postponed data.
The node statement and all other fields are unchanged except `lean`.

Hypothesis and clause correspondence:

- An arbitrary commutative ring is `{A : Type (u + 1)} [CommRing A]`.
  `{X : Scheme.{u}}` is an arbitrary scheme, without separation, finiteness,
  nonemptiness or coefficient-characteristic hypotheses. These are the universes
  of the recorded ordinary etale coefficient category, not the pro-etale site.
- The ordinary unbounded category is the recorded `DerivedCategoryModule A X`,
  definitionally `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`.
  Tensor is the recorded `derivedTensor (ModuleCat A) X`; the unit is the existing
  `constantComplex A X`. No bounded subcategory is used.
- The inline definition of line shape is exactly upstream
  `IsShiftedRankOneLocalSystem M n`: its existential sheaf is locally constant
  by `Scheme.IsLocallyConstantSheaf`; its stalk condition quantifies over
  `(Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)` and requires
  `Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of A A)`;
  its final conjunct is `Nonempty (M ≅ (DerivedCategory.singleFunctor _ 0).obj L⟦n⟧)`.
  Parentheses in the source put the shift on the derived single object.
  `n : ℤ` includes all positive, zero and negative shifts.
- Clause (1): the existing `IsShiftedRankOneLocalSystem.isInvertible` states
  tensor invertibility. The new `exists_shiftedEtaleLine_inverse` strengthens
  the witness exactly as the node requires: `∃ N`, shape `(-n)`, and isomorphisms
  of BOTH ordered derived tensors with `constantComplex A X`. This is existence
  of a genuine two-sided inverse; any other tensor inverse is isomorphic to it.
- Clause (2), arbitrary morphism: existing
  `IsShiftedRankOneLocalSystem.leftDerivedUpperStar (g : Y ⟶ X)` has no etale,
  smoothness or finiteness restriction on `g`. It states preservation of the
  same shape `n`. Existing `leftDerivedUpperStarShiftSingleIso g L n` states
  the displayed derived isomorphism from pullback of `L[n]` to `(g^*L)[n]`.
  `L(g^*)` is the upstream left derived inverse image; it is canonically the
  termwise derived exact inverse image (`leftDerivedUpperStarIsoMapDerivedCategory`).
- Clause (2), tensor: existing `IsShiftedRankOneLocalSystem.tensor` takes
  shapes `a,b : ℤ` and concludes shape `a+b` of the recorded derived tensor.
  These are the node's `m,n`. No coefficient-finiteness assumption is present.
- Clause (3): `shiftedEtaleLines_descent` binds `{ι : Type w}`, schemes `U`,
  maps `v`, and `[∀ i, AlgebraicGeometry.Etale (v i)]`. The hypothesis
  `hv : ∀ x : X, ∃ i y, (v i).base y = x` is exactly joint surjectivity.
  There is no `Nonempty ι` requirement, no finite subcover and no bound on `M`.
- Its first conjunct universally quantifies `M,n` and assumes shape `n` of
  every `L(v i)^* M`. The conclusion gives local constancy, every separably
  closed stalk isomorphic to `A`, and the derived isomorphism with the shifted
  single object of EXACTLY `(DerivedCategory.homologyFunctor _ (-n)).obj M`.
  These three conjuncts, by the existing definition, say shape `n` with the
  prescribed sheaf `H^(-n)(M)` itself, not an unspecified sheaf. The existing
  `of_jointlySurjective` is also recorded for the direct shape-only interface.
- Its second conjunct quantifies arbitrary `K,K'` and `α : K ⟶ K'`, assumes
  `IsIso` of every derived inverse-image map, and concludes `IsIso α`.
  The family universe `w` is independent, so all small families are covered.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its inherited
  locally ringed space data and local affine condition, and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, together with
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `constantComplex`,
  `DerivedCategory.isInvertible`. The category is the existing Mathlib
  unbounded localization, not a new category.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, the existing K-flat derived tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`. The latter
  identifies this functor with cohomology of every representing complex.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.IsLocallyConstantSheaf`, `Scheme.LocallyConstantDatum`. Its datum is
  an etale cover on which localized restrictions are constant, exactly the node.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the
  affine-local etale ring-map condition, equivalent to the node's formulation.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalkDiagram`,
  `pointedEtaleStalk`. The recorded definition allows arbitrary categories with
  the needed colimit but assumes algebraically closed points. Here the upstream
  line-shape notion uses Mathlib's `Scheme.pointSmallEtale` / `Point.sheafFiber`
  on separably closed points. Its fiber is the SAME opposite pointed-etale-
  neighbourhood colimit; in the module category all required colimits exist.
  This is an existing more general interface to the same stalk construction,
  not a private copy or a change to the dependency's meaning.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (separable polynomials split),
  and `IsSepClosure`; the former is precisely the condition used here.
- `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local`:
  `IsShiftedRankOneLocalSystem`, its `isInvertible`, `leftDerivedUpperStar`,
  `leftDerivedUpperStarShiftSingleIso`, `of_jointlySurjective`; the existing
  general notion makes a new definition unnecessary.
- `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace`:
  `IsShiftedRankOneLocalSystem.tensor`. This theorem needs only `CommRing A`,
  despite the later affine-space application using additional hypotheses.

Proof dependency modules with recorded declarations are imported (plain imports
when used only for the proof plan), including bounded-above flat K-flatness,
constant-complex stalk exactness, derived pullback/stalk comparison, geometric
field-extension comparison, module tensor closedness, inverse-image exactness,
localized tensor restriction and ringed-site modules. The remaining recorded
Mathlib/source proof tools are public transitive imports: algebraic closures,
small etale site and cover lifting, single-degree truncation, cohomological
isomorphism detection, conservative pullback and localized inverse image.
`lem-pur-sheaf-line-evaluation-inverse-pair` and
`lem-sf-exact-functor-derived-triangulated` have no recorded Lean declaration or
Mathlib match, so have no module to import yet; they are not needed to TYPE
these two statements. The existing upstream locally-constant invertibility and
exact-derived interfaces already supply the constructions used in the plan.

Edge cases checked before writing: zero coefficient ring (no `Nontrivial A`),
empty scheme, empty index family covering the empty scheme, negative and zero
shifts, infinite covers, arbitrary morphisms, unbounded derived objects and
arbitrary small index universes. On an empty site every sheaf is zero by the
empty covering condition, hence so is its derived unit; the inverse statements
remain meaningful. The stalk condition is vacuous only on the empty scheme,
where this is correct. The proof plan for an arbitrary index universe can
select one covering member above each point of `X`, giving a `Type u` cover
for the existing upstream descent tools. No point is selected on an empty
scheme. No statement correction or dispute was necessary.

Searches (actual runs, logged by msearch):

- LeanFinder: `Shifted rank one locally constant etale sheaves are tensor
  invertible with inverse shifted by the negative degree and descend along
  jointly surjective etale covers`: 8 hits, on monoid/module pullbacks,
  condensed monoidal categories and tensor Kaehler equivalences; no full match.
- Loogle: `"IsInvertible", "shiftFunctor"`: 0 hits.
- LeanSearch: `etale shifted rank one local system tensor inverse descent`:
  8 unrelated hits on etale algebras, tensor linear equivalences and shift
  localization; no matching statement.
- Mathlib grep via msearch: `IsShiftedRankOneLocalSystem|shift.*[Ii]nvertible|
  [Ii]nvertible.*shift` in CategoryTheory: 0 hits.
- Direct project grep for `IsShiftedRankOneLocalSystem`: upstream
  `SmoothDuality/Local.lean` defines exactly the notion and all listed local
  operations; `SmoothDuality/AffineSpace.lean` gives tensor stability. These
  declarations were opened in full and reused. No upstream declaration gives
  the inverse's line shape or explicitly the chosen cohomology sheaf.
- Direct grep for `lem-sf-shifted-etale-lines-locality` in `WeilConjectures`:
  no hits. Searches for shifted lines in `Sheaf` found finite Tate-line and
  normalized affine-line results, with different objects and hypotheses.
- DAG grep for `line shape|shifted rank.one local system|
  IsShiftedRankOneLocalSystem`: this node and its smooth-dualizing consumer;
  no separate definition node or exact existing statement attachment.
- Direct Mathlib/upstream/Sheaf search for the two new declaration names:
  no clashes.

Validation: the module is checked through the required `scompile.py` wrapper;
the dry run and delivery results are recorded by the launcher tools. Every
postponed proof has its source and a step-by-step proof docstring matching the
node's proof. No helper axiom, data choice from a postponed existence proof,
local notation, local instance or private definition is added.

The first dry run compiled cleanly but rejected the six reused upstream names
in `lean.declarations`: its static upstream name index does not contain them,
and its public-import traversal scans only `Sheaf.*`. The record now lists
only the two declarations owned by this delivery. The existing interfaces
remain explicitly identified in `lean.note` and above, and remain available
through the unchanged public imports. No Lean statement was changed.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
