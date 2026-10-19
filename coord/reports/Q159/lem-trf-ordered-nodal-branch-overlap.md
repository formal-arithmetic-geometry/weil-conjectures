## Worker report

The module `Sheaf.AlgebraicGeometry.OrderedNodalBranchOverlap` states
`AlgebraicGeometry.exists_ordered_nodal_branch_overlap`, with its proof `sorry`.
Two real helper definitions give the standard coordinate global sections and their
pulled-back principal germ ideals. They are construction helpers of this node,
recorded in `lean.declarations`, not additional notions or postponed theorems.
The theorem docstring includes all eleven steps of the DAG proof.

The node statement is unchanged. Its statement dependencies gain the already landed
`def-trf-strict-semistable-curve` because its `strictNodalRing` and
`StrictSemistableModel.nodal` supply exactly the standard nodal algebra and model.
No new node, dependency repair, statement correction or disputed statement is needed.

Clause-by-clause correspondence:

1. A separably closed field K is `(K : Type u) [Field K] [IsSepClosed K]`.
2. The valuation subring with fraction field K is `(V : ValuationSubring K)`.
   Mathlib's definition is a subring with `x ∈ V ∨ x⁻¹ ∈ V` for every x in K;
   the fraction field and total ordering of ideals are consequences, not extra
   hypotheses. `[Finite (PrimeSpectrum V)]` is exactly the finite-chain condition.
3. S is always `Spec (.of V)`; X and Y are arbitrary `Scheme.{u}` with
   `[IsAffine X] [IsAffine Y]`. The structure map is `f : X ⟶ Spec (.of V)`.
   `[Flat f] [LocallyOfFinitePresentation f]` state flatness and finite presentation:
   between these affine schemes quasi-compactness and quasi-separatedness hold
   automatically, so local finite presentation is equivalent to finite presentation.
4. `hfib` quantifies over every algebraically closed field Ω in the scheme universe
   and geometric base point `g : Spec (.of Ω) ⟶ Spec (.of V)`. Its first conjunct
   `(pullback f g).IsPureDimension 1` gives pure dimension one, including empty fibres.
   Algebraic closures of residue fields live in this same universe; the standard
   geometric-fibre condition is preserved under algebraically closed extension.
5. The second conjunct of `hfib` quantifies over each point z outside
   `(pullback.snd f g).smoothLocus`. It asserts `Nonempty` of the ring equivalences
   from the maximal-ideal `AdicCompletion` of the local ring to
   `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`. This is the stated nodal
   completion, with no smoothness or connectedness requirement added to the fibre.
   The existential equivalence is proof data, not a chosen object definition.
6. `hcomponents` quantifies over every s and closed Z whose underlying set belongs
   to `irreducibleComponents (f.fiber s)`. It requires `Smooth` of the composite
   of `(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι` with
   `f.fiberToSpecResidueField s`, exactly the reduced component over κ(s).
7. `(c : V) (hc : c ≠ 0)` is the nonzero thickness. The chart target is the existing
   `(StrictSemistableModel.nodal (A := .of V) c).scheme`, definitionally
   `Spec (V[u,v]/(uv-c))`. Its `.baseMap` is induced by the coefficient homomorphism.
8. `p : Y ⟶ X` and `h : Y ⟶ ...` have `[Etale p] [Etale h]`; `hover` states
   `h ≫ model.baseMap = p ≫ f`. Thus they are S-morphisms for the same structure
   map on Y, with no independently chosen incompatible base structure.
9. `(y : Y)` and `hy : p y ∉ f.smoothLocus` give y and its nonsmooth image x.
   `horigin` states that both coordinates pulled back to Y evaluate to zero in
   κ(y). This is equivalent to both coordinates vanishing in κ(h(y)), because
   the induced residue-field map is injective. `Fin 2` indexes precisely u and v.
10. The existential opens U and Y0 have `IsAffineOpen` witnesses, `p y ∈ U`,
    `y ∈ Y0`, and `e : Y0 ≤ p ⁻¹ᵁ U`. The restricted morphism p0 is the canonical
    `p.resLE U Y0 e`, and `Surjective` states its surjectivity.
11. W is `pullback p0 p0`; r1 and r2 are its canonical `pullback.fst` and
    `pullback.snd`. The displayed structure map `r1 ≫ Y0.ι ≫ p ≫ f` is W → S.
    Every s, every component Z of its fibre, and every `IsGenericPoint ξ Z` are
    quantified. The point in W is the canonical image under `.fiberι s`.
    For each `i : Fin 2`, the equality of `strictNodalCoordinateIdeal` along
    `r1 ≫ Y0.ι ≫ h` and `r2 ≫ Y0.ι ≫ h` states the required equality of principal
    ideals in the local ring of W at that image. The helper first pulls the
    coordinate global section along the indicated map, then takes its germ and
    `Ideal.span` of that singleton. It never takes the local ring of the fibre.
    Restriction to Y0 is the composition with `Y0.ι`, so these are exactly the
    restricted u0 and v0 of the node. The two equalities are expressed uniformly
    by universal quantification over the two-element type.
12. The conclusion contains only those existential opens, surjectivity and
    fibre-generic ideal comparisons. It asserts neither descent of ideals nor
    an étale nodal chart on U.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the dependency also records
  `IsSepClosure`, whose signature and docstring were read; no closure is used here).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd` (geometric and ordinary fibres).
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and `.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`
  with its commutative ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `.X`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`; it supplies the recorded
  reduced induced subscheme interface, using the existing `vanishingIdeal` construction.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `.evaluation`,
  `Scheme.Hom.residueFieldMap` (evaluation is germ followed by residue).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial` (via the existing chart module),
  and its multivariate counterpart in the existing standard nodal model.
- `Sheaf.TraceFormula.StrictSemistableCurve`: `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`.

All recorded, available proof-dependency modules are imported non-publicly.
`lem-trf-normal-topologically-noetherian-components` currently has no Lean record
or Mathlib match, so no module for that proof-only prerequisite is imported.
No proof is attempted in this statement delivery.

Edge cases checked before writing: if V is a field, or c is a unit, the origin
condition is impossible since uv=c. The resulting implication is intentionally
vacuous; no extra nonunit hypothesis was inserted. X or Y empty is likewise
excluded by the supplied point y, not by an extra nonemptiness assumption.
Individual empty fibres have no generic component points and impose no condition;
pure dimension of an empty geometric fibre is true by the existing definition.
Disconnected schemes and reducible fibres are allowed. Both coordinate labels
are retained even in characteristic two. No Noetherian-ring, discrete-valuation,
properness, connectedness or smooth-generic-fibre hypothesis was added. The
ideals are in the total local ring even when the corresponding coordinate
vanishes on the fibre; this retains the thickness c rather than killing it.
All universes and variables are explicitly bound; no local notation or private
instances are needed.

Searches for reuse (2026-10-18):

- `msearch.py leanfinder`, query: "Etale nodal curve charts ordered branches
  principal ideals agree at generic points overlap over valuation ring".
  Eight hits: standard étale presentations, étale loci and universal factorization;
  no overlap-ordering theorem.
- `msearch.py loogle`, query: "IsNodal, ValuationSubring, Scheme.Hom.fiber".
  Zero hits; unknown identifier IsNodal.
- `msearch.py leansearch`, query: "nodal curve ordered branch ideals overlap
  generic fibre valuation ring". Eight valuation-ring and valuation-ideal hits;
  none stating the requested overlap comparison.
- `msearch.py grep`, query: "nodal|Nodal|ordered.*branch", restricted to
  Mathlib/AlgebraicGeometry. Zero hits.
- `msearch.py grep`, query:
  "strictNodalCoordinate|ordered_nodal_branch|branch.*overlap". Zero Mathlib hits.
- `rg` over upstream WeilConjectures and project lean/Sheaf for nodal, Nodal,
  nodalModel, ordered nodal branches and branch overlap located the strict nodal
  algebra, universal model, nodal completion hypotheses, and parent chart theorem.
  These were opened. Only the parent's proof docstring cites the present item;
  there is no existing declaration of it. Exact upstream `grep -rn` of the node
  id also gave no hit. The helper names do not occur in either source library.

Source verification: opened literature/stacks-project/curves.tex at
`lemma-etale-local-structure-nodal-family` (Tag 0CBY). It supplies only the initial
étale chart; the theorem docstring and this report preserve the node's explicit
attribution of the finite-height all-fibres ordering to an agent reconstruction.
The already split eleven-step node proof is copied into the theorem docstring;
no stronger assertion is attributed to Stacks or Temkin.

Validation: the required scompile.py wrapper was used throughout. The first two
attempts exposed coefficient-ring/category inference issues. Explicit
`(C := Scheme.{u})` and `(A := .of V)` annotations resolved them without changing
the statement, increasing resource limits, or adding hypotheses. Line-length
warnings were then corrected. The final per-file compile and delivery preflight
results are recorded by the delivery tools.

## Second reading by Q159

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
