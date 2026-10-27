## Worker report

The module `Sheaf.AlgebraicGeometry.LCIUnramifiedSingularNodalRecognition` states
`AlgebraicGeometry.lci_unramified_singular_nodal_recognition`, with its sole proof
`sorry`. It adds no definitions and changes only the item's `lean` record. The
mathematical statement, statement dependencies and proof plan are unchanged.

I read the item, all fourteen statement dependencies and their recorded declarations,
the recorded proof-dependency declarations, and Stacks `curves.tex`,
`lemma-nodal-family` (0C59) and `lemma-nodal-lci` (0C4E), including the reverse
implications. The sources give exactly this geometric-fibre recognition argument.
There is no statement dispute or dependency-interface fault.

The node's hypotheses and clauses correspond as follows.

| Node text | Lean rendering |
| --- | --- |
| Schemes T and B and morphism g | `{T B : Scheme.{u}} (g : T ⟶ B)` |
| g flat | `[Flat g]` |
| g locally finitely presented | `[LocallyOfFinitePresentation g]` |
| Every algebraically closed field Ω and every geometric point y | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (CommRingCat.of Ω) ⟶ B)` in `hfibres` |
| Geometric fibre C_y | `pullback (C := Scheme.{u}) g y`, with structure morphism `pullback.snd g y` |
| Fibre empty or pure of dimension one and a local complete intersection | `IsEmpty (...) ∨ ((...).IsPureDimension 1 ∧ ...)` |
| Affine open cover | `∀ z : pullback (C := Scheme.{u}) g y, ∃ U : (...).affineOpens, z ∈ U.1 ∧ ...`; affine neighbourhoods at every point constitute precisely a cover |
| Chart algebras finitely generated over Ω | The existential witness `ft : @Algebra.FiniteType Ω Γ(..., U.1) ...` |
| Chart algebra's specified Ω-structure | `(((pullback.snd g y).appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of Ω)).inv.hom).toAlgebra`; this is induced by the fibre projection, not an arbitrarily chosen algebra structure |
| Chart algebras local complete intersections in the cited sense | `@Algebra.IsLocalCompleteIntersection Ω Γ(..., U.1) ... ft`, using the dependency's exact definition and that same induced algebra structure |
| Z is the first-Fitting singular subscheme | `Scheme.firstFittingSingularSubscheme g`, the canonical inclusion associated to the glued first Fitting ideal |
| Z to B unramified | `hSing : IsUnramified (Scheme.firstFittingSingularSubscheme g ≫ g)` |
| For every such Ω,y and every nonsmooth point z | The conclusion quantifies over Ω, its field and algebraic-closure instances, y, and `z : pullback (C := Scheme.{u}) g y`, followed by `z ∉ (pullback.snd g y).smoothLocus → ...` |
| z is closed in C_y | `z ∈ closedPoints (pullback (C := Scheme.{u}) g y)` |
| Completed local ring at z for its maximal-ideal-adic topology | `AdicCompletion (IsLocalRing.maximalIdeal ((...).presheaf.stalk z)) ((...).presheaf.stalk z)` |
| Isomorphic to Ω[[u,v]]/(uv) | `Nonempty (... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}))`, with the explicit power-series types in the file |
| Both conclusions hold | The closed-point assertion and the ring-isomorphism assertion are conjoined |
| Empty fibres impose no condition | `IsEmpty` is the first alternative in `hfibres`, and the conclusion has no points z to quantify over in that case |

The ambient universe `u` is explicit and shared by the schemes and the geometric
fields, following the recorded geometric-point and pullback interfaces. There is no
independent smaller test universe, finite bound on chart families, characteristic
restriction, quasi-compactness, nonemptiness or separatedness assumption. All variables
are explicitly bound; `set_option autoImplicit false` enforces this.

Dependency declarations used (each signature and docstring read in the source):

| Dependency | Module and declaration |
| --- | --- |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with scheme morphisms in its category |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation` |
| def-weil-geometric-point | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline algebraically closed fields and morphisms from their spectra, as the dependency record specifies |
| def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension` |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`; scheme pullbacks supplied by `Mathlib.AlgebraicGeometry.Limits` |
| def-weil-pbc-complete-intersection-over-field | `WeilConjectures.RingTheory.CompleteIntersectionOverField`: `Algebra.IsLocalCompleteIntersection`, whose principal-open cover uses `Algebra.IsGlobalCompleteIntersection` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Scheme.Hom.smoothLocus`, the open locus smooth over the base for locally finitely presented morphisms |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; ring structure from `Mathlib.RingTheory.AdicCompletion.Algebra` |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, with `Fin 2` as variable index and `MvPowerSeries.X` as u,v |
| def-trf-first-fitting-singular-subscheme | `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`: `Scheme.firstFittingSingularSubscheme` |
| def-weil-unramified-morphism | `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified` |
| def-weil-closed-points | `Mathlib.Topology.JacobsonSpace`: `closedPoints` |

The recorded proof modules are imported privately:
`Sheaf.AlgebraicGeometry.NodalCurveLCICriterion` (`nodal_curve_lci_criterion`),
`Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion`
(`unramified_over_field_iff_local_criterion`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
(`unramified_baseChange_restrict_open`), together with Mathlib closed immersions and
algebraic closures. The finite-type and pullback proof inputs are already public
statement imports. The proof-dependency nodes for differential base change, general
Fitting pullback, and field-curve Fitting/smooth preparation have no recorded Lean
module on this base; no unrecorded declaration for them is invented. The declaration
docstring carries all five proof steps and the relevant dependency ids.

Edge cases checked mathematically before writing:

- Empty source or empty geometric fibre: the hypothesis accepts the empty alternative,
  and the conclusion is vacuous. No closed point is required to exist.
- Smooth affine line: its rank-one differential module has unit first Fitting ideal,
  so the singular subscheme is empty; there are no nonsmooth points to test.
- The ordinary node uv=0: the fibre is pure one-dimensional and a hypersurface; its
  first-Fitting singular subscheme is the reduced origin, unramified over Ω, and the
  required completed local ring is Ω[[u,v]]/(uv), including characteristic two.
- The cusp v²=u³: its singular subscheme is nonreduced, so the unramified hypothesis
  excludes it (also in characteristics two and three).
- A double line: its singular subscheme is positive-dimensional, hence not unramified
  over Ω; its generic nonsmooth point is therefore not a counterexample. Closedness
  is a conclusion, never a premise on z.
- Nonempty zero-dimensional fibres fail pure dimension one. Disconnected fibres and
  arbitrarily large affine covers are permitted: no connectedness or finite-type
  global hypothesis was added.

Searches actually run:

- `msearch.py ... leanfinder`: query "A flat locally finitely presented morphism with
  pure one dimensional local complete intersection geometric fibres and unramified
  first Fitting singular subscheme has closed nonsmooth geometric fibre points with
  completed local ring Omega[[u,v]]/(uv)". Result: OK, eight hits, on smooth morphisms,
  smooth relative dimension, standard smoothness, and the algebraic smooth locus.
  None states the recognition result.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.Scheme.Hom.smoothLocus, AdicCompletion`. Result: OK, zero hits.
- `msearch.py ... grep`: query
  `nodal|unramified.*singular|singular.*unramified`, subdirectory `AlgebraicGeometry`.
  Result: OK, zero Mathlib hits.
- `rg` of the project `WeilConjectures` and `Sheaf/AlgebraicGeometry` for nodal,
  unramified/singular combinations, and `IsLocalCompleteIntersection`: related nodal
  modules and the fieldwise `NodalCurveLCICriterion` exist, but no relative recognition
  theorem does. The fieldwise criterion is imported as a proof input and its affine
  local-complete-intersection formulation is followed exactly here.
- Exact id search in `lean/WeilConjectures`: no hit. Exact proposed declaration and
  module name search in `lean/Sheaf`, `lean/WeilConjectures`, Mathlib and
  `dag/lean_names_upstream.json`: no hit.
- `rg -l firstFittingSingularSubscheme` found only its owning module, the fieldwise
  criterion, `NodalBranchSchemeRepair`, and `GraphConeGluing`; none supplies this theorem.

Validation: every compile used the prescribed `scompile.py Q38
lem-trf-lci-unramified-singular-nodal-recognition ...` wrapper. The first compile exposed
ambiguous category inference for direct pullback terms. Explicit `(C := Scheme.{u})`
on those terms repaired the elaboration without changing the statement. The next run
compiled both the sandbox and final module successfully (3.1 s and 6.7 s), with no
errors or unexpected warnings.

## Second reading by Q38

I reopened the final module and node for a separate second pass. The dispatcher
explicitly prohibits starting other agents; this is a second reading by the same worker,
with the maintainer's independent delivery review still to follow.

The scheme/morphism and flat/finitely-presented binders match the first sentence.
The geometric-field quantifiers, pullback direction and its second projection match
the geometric-fibre clause. The `IsEmpty` alternative and the conjunction in the
other alternative retain exactly the empty-or-pure-one-dimensional-LCI assumption.
The pointwise affine neighbourhood formulation is precisely an affine cover, and
both finite generation and LCI use the same canonical Ω-algebra structure. I checked
its map direction explicitly: Ω maps into Γ(Spec Ω,⊤) through `ΓSpecIso.inv`, then to
Γ(C_y,U) through the projection's `appLE`. Thus there is no arbitrary algebra structure.

The singular subscheme is the recorded canonical first-Fitting construction, available
because local finite presentation implies local finite type. Its composite with g,
not its inclusion alone, is assumed unramified. The conclusion ranges over all
nonsmooth points, with closedness in the conclusion, followed by the completion at the
stalk's maximal ideal. The power-series quotient uses exactly two variables, their
product, and the same Ω as the geometric point. A ring isomorphism is precisely the
node's requested isomorphism; no unspecified coefficient compatibility was added.
The source has no further characteristic, properness or nonemptiness hypothesis.

The only mismatch found in the first pass was Lean category inference; the explicit
scheme-category annotation fixed it. This second pass found no remaining mismatch,
no missing dependency notion, and no required statement correction or new node.
