## Worker report

Repair of c73ed0dc5cff, addressing H1 and H2. The sandbox initially contained only
brief markers. This packet contains the theorem module, its node with a `lean`
record and the added landed dependency `def-trf-nodal-geometric-fibres`, and this
report. All other node fields are copied from the current main branch: in
particular no split-summary or creator-metadata edit is delivered. I make no claim
that the maintainer-owned `created` field has been corrected.

The file is `lean/Sheaf/SixFunctors/TraceFormula/ProjectiveNodalFamilyGeometry.lean`.
It states `AlgebraicGeometry.projective_nodal_family_geometry` with `sorry` and
constructs `AlgebraicGeometry.nodalSingularBaseChangeMap` by `pullback.map`, with
actual morphism data and the identity commutativity equations. The latter is a
helper of this item's base-change clause, recorded in `lean.declarations`.

Clause-by-clause correspondence:

* Noetherian Y: `[IsNoetherian Y]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with the finite
  Noetherian affine-cover description in the node.
* Projective f in the blueprint convention: `[IsHProjective f]`, using the
  recorded upstream class, rather than replacing it with properness.
* Flatness and finite presentation: `[Flat f]` and
  `[LocallyOfFinitePresentation f]`. H-projectivity implies properness and thus
  quasi-compactness and separatedness; these supply the global finite-presentation
  conditions without additional hypotheses.
* Every geometric fibre nonempty and connected: `hN : HasNodalGeometricFibres f`.
  Reading its full definition shows `ConnectedSpace` on `pullback f g` for every
  algebraically closed field Ω and `g : Spec Ω ⟶ Y`. ConnectedSpace includes
  nonemptiness. This is the existing Q119 definition, not a duplicate.
* Pure dimension 1: that same definition says the geometric fibre has topological
  Krull dimension 1. Under H-projectivity it is Noetherian of finite type over a
  field. Each irreducible component therefore has dimension 0 or 1. A dimension-0
  component is a singleton closed point and is disjoint from all other components;
  since there are finitely many components it is open as well. Connectedness then
  forces the entire fibre to be that point, contrary to dimension 1. Consequently
  all components have dimension 1. This explains why the existing dimension-1
  helper is exactly the pure-dimension condition in this context.
* Ordinary double points at nonsmooth points: the helper literally quantifies
  `x ∉ (pullback.snd f g).smoothLocus` and requires a ring isomorphism from
  `AdicCompletion (IsLocalRing.maximalIdeal stalk) stalk` to
  `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`. The coefficient field is
  the same Ω that defines the geometric fibre.
* Open relative smooth locus: `IsOpen (f.smoothLocus : Set X)`; U is the actual
  Mathlib relative smooth locus, not a chosen open or an extra hypothesis.
* A closed singular subscheme: `∃ (S : Scheme.{u}) (i : S ⟶ X),
  IsClosedImmersion i ∧ ...`. Its structure map is `i ≫ f`.
* Underlying set X minus U: `Set.range i = (f.smoothLocus : Set X)ᶜ`.
* Unramified over Y: `LocallyOfFiniteType (i ≫ f) ∧
  IsOpenImmersion (pullback.diagonal (i ≫ f))`, exactly the recorded inline
  unramified-morphism notion.
* Finite underlying fibres: `∀ y : Y, Set.Finite ((i ≫ f) ⁻¹' {y})`.
* Every Noetherian base change: the universal `Y₁`, `g : Y₁ ⟶ Y`, and
  `[IsNoetherian Y₁]` are INSIDE the existential for S and i. Thus the same S
  works for every base change. For `pullback.snd f g`, the statement lists
  `IsHProjective`, `Flat`, `LocallyOfFinitePresentation`, and
  `HasNodalGeometricFibres`, preserving all the original properties.
* New smooth locus equals the preimage of U:
  `(pullback.fst f g) ⁻¹ᵁ f.smoothLocus = (pullback.snd f g).smoothLocus`.
* The same S base-changed to Y₁ is closed, unramified and supported exactly on the
  new nonsmooth locus: `nodalSingularBaseChangeMap f i g` has domain
  `pullback (i ≫ f) g` and codomain `pullback f g`. Its definition is the
  canonical induced map from i, identity on Y₁ and identity on Y. The conclusions
  are `IsClosedImmersion` of this map, the inline unramified conjunction for its
  structure map `pullback.snd (i ≫ f) g`, and range equal to the complement of
  `(pullback.snd f g).smoothLocus`. There is no unrelated existential T or map.
* No assertion that taking reduction commutes with base change: no reduction
  assertion is made. The singular scheme and its base changes may be nonreduced.

The only postponed proof is the named theorem above. Its docstring gives all four
DAG proof steps, including the relevant node ids. There is no sorry in a definition.
The signature in `lean.statement` is extracted verbatim from the final source.
All binders, schemes, fields used by the imported helper, and universe u are
explicit. There is no extra equality of universes or small-field bound: the common
arbitrary scheme universe and geometric tests follow the existing Mathlib/Q119
size convention, which represents schemes and base changes in any common universe.

Dependency declarations read and used:

* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective.IsHProjective`
  (declaration `AlgebraicGeometry.IsHProjective`; source read with
  `scompile.py --source` because the older checkout lacks this module).
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with the
  stalkwise interpretation in `Flat.iff_flat_stalkMap`.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (Mathlib leaf).
* `Mathlib.AlgebraicGeometry.Geometrically.Basic` and the geometric-properties
  leaf: geometric tests use the existing scheme universe, pullbacks and fields.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, projections and `pullback.map`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; with `IsOpenImmersion` and
  `pullback.diagonal` this is the exact recorded unramified notion.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
* `Sheaf.AlgebraicGeometry.NodalGeometricFibres`:
  `AlgebraicGeometry.HasNodalGeometricFibres`, read in full with its docstring.
* `WeilConjectures.Mathlib.Topology.KrullDimension.topologicalKrullDimAt` and
  `topologicalKrullDim` were inspected for the dimension notion; only the global
  dimension in the canonical nodal helper is needed, as explained above.
* The reduction dependency's `Scheme.nilradical` and
  `Scheme.IdealSheafData.subscheme` are not used: the statement explicitly
  disclaims a reduction/base-change claim.

Proof imports preserve the stated proof plan:
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`,
`Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`,
`WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`,
`WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete`, and
`Mathlib.AlgebraicGeometry.Fiber`. The first-Fitting definition and nodal-family
fitting theorem currently have no recorded Lean module, so no import can yet be
added for them. Mathlib base-change leaves are supplied by the property imports.

Edge cases checked: smooth families allow the empty singular scheme; an empty Y
makes geometric-fibre tests vacuous and allows empty X; an empty X over a nonempty
Y is excluded by the nonempty-fibre condition. A zero-dimensional isolated
component would contradict connectedness and dimension 1. Singular base changes
such as xy=t followed by t=s² yield a possibly nonreduced singular scheme
Spec k[s]/(s²), which the conclusion permits. Identity and nonflat base changes
are both quantified without an extra assumption. All characteristics, including
2, are allowed by the node equation uv.

Searches performed with `msearch.py` for the item:

* LeanFinder: "projective flat locally finitely presented nodal family smooth
  locus unramified singular subscheme finite fibres base change". Eight hits
  were generic smoothness/base-change results, none the theorem.
* Loogle: "Scheme.Hom.smoothLocus, IsHProjective, IsFinite,
  FormallyUnramified, IsClosedImmersion". No hits; remote index reported unknown
  unqualified Scheme.Hom.smoothLocus. Local source inspection supplied the name.
* grep: `nodal|singularLocus|Fitting|ordinary double point` in Mathlib
  AlgebraicGeometry: no hits.
* `rg` in the upstream WeilConjectures sources and shared `lean/Sheaf` found the
  existing nodal-geometric-fibre definition and the different nodal-resolution
  theorem. The item theorem has no existing match. The earlier candidate helper
  was deleted before delivery to avoid a duplicate definition.

Sources checked: Stacks curves.tex, lemma-nodal-family (0C59) and
lemma-base-change-nodal-family (0C5B), and the node's detailed four-step proof.
No statement correction, new definition node, or dependency repair is required.

## Second reading by Q71

I reread the node, the final module and the full imported nodal-fibre definition.
H1 is repaired by the real module, one sorry theorem, complete lean record, this
worker report and this second reading. H2 is repaired by delivering no
split_report or creator-metadata change; the delivery wrapper rebases the packet
onto current main and preserves maintainer-owned fields. This report describes
only files actually included.

The second reading found that the first draft had chosen a fresh singular scheme
in each base change. I replaced it with the single S outside the universal binder
and the actual `nodalSingularBaseChangeMap f i g`, whose source is S ×_Y Y₁.
The map is constructed by `pullback.map`; its structure map is the second
projection. I checked the finite-fibre clause, open smooth-locus clause,
unramified conjunctions, projectivity/flatness/finite-presentation and complete
nodal-fibre condition before and after base change. The pure-dimension equivalence
under connectedness and finite type is explained above. The reduced-subscheme
commutation claim is absent, as required. Source and node statements stay fixed.

Validation: the final module, including all recorded proof imports, passed
`scompile.py Q71 lem-trf-projective-nodal-family-geometry` in both sandbox and
library positions with no errors and no warnings. The canonical map is a real
definition; the theorem is the sole sorry. Delivery preflight and compile are run
again through `deliver2.py --no-push` before the final push.
