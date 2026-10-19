## Worker report

`Sheaf.TraceFormula.NodalOpenLocus` states `AlgebraicGeometry.nodalOpenLocus`.
The only theorem proof is `sorry`; its docstring contains all eight DAG proof steps,
including their dependency citations. Three real Prop-valued helper definitions belong
only to this node's interface and are listed in `lean.declarations`.

I read the full node, all eight statement dependencies and their lean/mathlib_match records,
the recorded dependency signatures and docstrings, and Stacks `curves.tex`,
`lemma-locus-where-nodal`, lines 4738–4775 (Tag 0DSC). The source constructs a maximal nodal
open for a flat locally finitely presented morphism, compatible with arbitrary base change.
Our node specializes to pure one-dimensional nonempty geometric fibres and spells out the
pointwise geometric meaning; its statement and dependency lists are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and the named morphism are `(Y T : Scheme.{u}) (p : Y ⟶ T)`.
- Flatness is `[Flat p]`; local finite presentation is
  `[LocallyOfFinitePresentation p]`. No properness, quasi-compactness, connectedness,
  reducedness, or nonemptiness of the total space is imposed.
- `hgeom` quantifies over `t : T` and an arbitrary algebraic closure `Ω` of its residue
  field, encoded by `[Field Ω] [Algebra (T.residueField t) Ω]`
  `[IsAlgClosure (T.residueField t) Ω]`. The actual geometric fibre is the scheme pullback
  along `Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫`
  `T.fromSpecResidueField t`. Its nonempty underlying type is required to satisfy
  `Scheme.IsPureDimension 1`. This retains the exact residue-field-closure hypothesis,
  rather than assuming dimension preservation under larger algebraically closed extensions.
- The open subscheme is `∃ U : Y.Opens`, with its canonical inclusion `U.ι`.
  `HasOnlySmoothOrNodalGeometricFibres (U.ι ≫ p)` tests every geometric point over every
  algebraically closed field in the scheme universe. Each point must be in the smooth
  locus of the geometric-fibre structure morphism or be an ordinary node.
- `IsOrdinaryNode Ω X x` requires `x ∈ closedPoints X` and a ring isomorphism from
  `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)`
  to `MvPowerSeries (Fin 2) Ω` modulo `Ideal.span {X 0 * X 1}`. Thus closedness is explicit,
  the completion uses the maximal ideal, the coefficient field is the geometric field,
  and the two formal variables and their product are literal Mathlib constructions.
- Largestness is `∀ V : Y.Opens, HasOnlySmoothOrNodalGeometricFibres (V.ι ≫ p) → V ≤ U`.
  This compares every qualifying open, with no auxiliary choice of its points or charts.
- Arbitrary base change is `∀ (T' : Scheme.{u}) (g : T' ⟶ T), ...`.
  Its open is the inverse image `pullback.fst p g ⁻¹ᵁ U` on the genuine base-changed source,
  whose structure map is `pullback.snd p g`. The first base-change clause says this open
  has the nodal fibre property; the second says it is largest among all opens with that
  property. This characterizes equality with the maximal open for the new family without
  introducing a chosen open from an existence theorem.
- The precise geometric-fibre assertion quantifies again over every `t` and every
  algebraic closure `Ω` of `κ(t)`. For every point `x` of that pullback, its projection
  lies in `U` iff it satisfies `IsSmoothOrOrdinaryNode` for the second projection.
  The smooth locus and nodes are those of the whole geometric fibre.
- The last conjunct states the final iff literally: every point of the scheme-theoretic
  fibre projects into `U` iff every point outside the smooth locus of the geometric fibre
  satisfies `IsOrdinaryNode Ω`. The right side uses the node predicate itself, rather
  than hiding the singular-point premise in another disjunction.

Recorded dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Flat.iff_flat_stalkMap` verifies its agreement with the dependency's local-ring definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, with the geometric-point map specified by the
  `def-weil-geometric-fibre` record; its projections are `pullback.fst` and `pullback.snd`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, checking every
  irreducible component's subspace Krull dimension, as its source docstring states.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `Scheme.Hom.smoothLocus`, the recorded smooth notion at points for LFP morphisms.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, with the
  ring structure for the stalk as its own module; no new completion is defined.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.

The five available project proof dependencies are imported without `public`:
`FirstFittingSingularSubscheme`, `DthFittingSmoothLocus`, `PresentationFittingIdeal`,
`NodalPointLocalCriterion`, and `RelativeDimensionBaseChange`. Mathlib proof interfaces
are imported too, including affine fibre products, Kaehler-differential base change,
faithfully flat spectrum surjectivity, the field-extension flatness instances,
finite-type affine charts, quasi-separated/permanence properties, and Zariski's lemma.
The proof-only nodes `lem-trf-finite-residue-point-closed-in-fibre`,
`lem-trf-lci-pointwise-criterion`, `lem-trf-syntomic-locus-base-change`, and
`lem-trf-unramified-locus-base-change` have no recorded Lean statement or Mathlib match
in the inspected DAG, so no nonexistent module is imported for them. They are not needed
for typing this stage-2 statement. No statement dependency requires repair.

Edge cases: empty fibres are permitted by the explicit `Nonempty` antecedent and are
vacuously pure-dimensional; an empty total space or an empty base is permitted; the empty
open is a candidate in largestness. A smooth family permits the whole open; a nodal
singularity has the `uv` completion in every characteristic, including characteristic two.
A cusp has a different completed local ring, and the double line is nonreduced with a
nonisolated singular locus; neither is silently accepted as a node. The pointwise test
includes nonclosed smooth points while requiring nodes to be closed. Arbitrary base
change includes the identity, nonreduced bases, and empty schemes. Test fields and
schemes share the scheme universe `u`, with no independent smaller test universe.
All declarations bind their variables and the universe explicitly.

Searches actually run with the prescribed wrapper:

- LeanFinder: `A flat family of curves has a largest nodal open locus compatible with
  arbitrary base change`. Eight hits: `UniversallyOpen.of_flat`, flatness and its
  base-change/composition interfaces, and smooth-relative-dimension base change.
  None states a nodal-open theorem.
- Loogle: `AlgebraicGeometry.Scheme.Hom.smoothLocus`. Seven hits give `smoothLocus`,
  its pointwise criterion, whole-space criterion, density results, and its inverse image
  under an open immersion. This is the smooth part only and is reused.
- Mathlib grep: `nodal|ordinary.double.point|semistable` in `AlgebraicGeometry`.
  Zero hits.
- `rg` over project `lean/Sheaf` and upstream `WeilConjectures` for nodal terminology,
  and `grep -rn` for this node ID: no upstream statement of this item. Related side
  statements include `NodalCurveLCICriterion`, `FormalLocalStructureNodalFamily`, and
  `HasNodalGeometricFibres`. The last also requires nonempty connected fibres and dimension
  one; it cannot encode an arbitrary open whose fibres may be empty or disconnected.
- `rg` over Mathlib, upstream, side Lean, and `dag/lean_names_upstream.json` for the new
  declaration names found no conflicts. Related nodal criterion modules spell out the
  completion condition inline and do not define the present ordinary-node predicate.

During the final self-check I made closedness explicit in the node predicate, separated
all five conclusions as top-level conjuncts, quantified the precise assertion over every
algebraic closure, restored the exact fibre-dimension premise, and expanded the complete
proof docstring and proof imports. The initial draft's stronger dimension premise and
its residue-fibre-only pointwise draft are not in this delivery. No node statement changed,
no statement is disputed, and no additional DAG nodes or dependency modules were needed.
The final module is compiled only through the authorized `scompile.py` wrapper; delivery
uses `deliver2.py`, including its server preflight and separate per-file compilation.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
