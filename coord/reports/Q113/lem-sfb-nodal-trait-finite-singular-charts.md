## Worker report

The delivery states `AlgebraicGeometry.nodal_trait_finite_singular_charts` in
`Sheaf.AlgebraicGeometry.NodalTraitFiniteSingularCharts`. Its sole theorem has
proof `sorry`; no definition, instance, auxiliary theorem, or axiom is introduced.
The mathematical statement is unchanged. The docstring contains all seven DAG
proof steps with their cited nodes and source places.

Hypothesis-by-hypothesis correspondence:

- `R : Type u`, `[CommRing R]`, `[IsDomain R]`,
  `[IsDiscreteValuationRing R]` introduce the arbitrary DVR.
- `π : R`, `hπ : Irreducible π` specify its uniformizer.
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` is exactly the equivalence
  with generation of the maximal ideal. No completeness or excellence is assumed.
- `X : Scheme.{u}` and `f : X ⟶ Spec (.of R)` introduce the scheme over the trait.
  `FractionRing R` is its canonical fraction field; the special fibre is taken at
  `IsLocalRing.closedPoint R`, equivalently over the canonical residue field.
  Thus K and k need not be extra independently chosen fields or hypotheses.
- `[Flat f]` supplies flatness. `[LocallyOfFinitePresentation f]`,
  `[QuasiCompact f]` and `[QuasiSeparated f]` jointly supply finite presentation
  as expressly defined in def-sbc-locally-finite-presentation, including its
  quasi-separatedness clause (not separatedness of X).
- `hgeneric` is smoothness of the second projection of the base change along
  `Spec (FractionRing R) → Spec R`, so it is precisely smoothness of X_K/K.
- `hfib` quantifies over algebraically closed fields Ω and geometric base maps g;
  it asserts `IsReduced (pullback f g)` and `(pullback f g).IsPureDimension 1`.
  The empty scheme is reduced and its irreducible-component condition is vacuous,
  so this unconditional form is equivalent to the node's nonempty-fibre wording.
- `hnodal` quantifies over the same fibres and their points z. Its first premise
  `IsClosed ({z} : Set ↥(pullback f g))` retains the CLOSED geometric point
  restriction. Its second premise is nonmembership in the relative smooth locus.
  Its conclusion is a nonempty Ω-algebra equivalence from the maximal-ideal-adic
  stalk completion to `MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`. The Ω-algebra
  structure comes from the existing canonical `completedLocalScalarMap`, not
  an arbitrary coefficient field or an arbitrary ring equivalence.

Conclusion-by-conclusion correspondence, in the order of the conjunction:

1. `IsNoetherian X` is exactly quasi-compactness and local Noetherianity, as in
   Mathlib.AlgebraicGeometry.Noetherian (class extends both).
2. `Set.Finite {x : X | x ∉ f.smoothLocus}` is finiteness of the nonsmooth locus.
3. For each of these points, `IsClosed ({x} : Set X)` and
   `f x = IsLocalRing.closedPoint R` specify closed special-fibre points.
4. At every `x ∈ f.smoothLocus`, `IsRegularLocalRing (X.presheaf.stalk x)` asserts
   total-space local regularity, rather than regularity only in the fibre.
5. For every nonsmooth x the existential R', its ring/domain/DVR structures, φ,
   n, U, p, q and v give the pointed diagram. `Function.Injective φ`,
   `IsLocalHom φ`, and `Etale (Spec.map (CommRingCat.ofHom φ))` supply exactly
   the injective local etale extension. `Irreducible (φ π)` retains the original
   uniformizer. `1 ≤ n` is the required positive exponent.
   `StrictSemistableModel.nodal ((φ π)^n)` is the existing affine model whose
   algebra is `strictNodalRing (.of R') ((φ π)^n)`, definitionally the quotient
   R'[a,b]/(ab-(φ π)^n). Both p and q are etale and `p v = x` specifies the point.
   The equality of composites is exactly commutativity over S. The R'-structure
   on U is the displayed composite `q ≫ model.baseMap`, as in the recorded
   trait-model dependency: no independent unspecified structure map is used.
   The equation `model.baseMap (q v) = IsLocalRing.closedPoint R'` and
   `∀ i : Fin 2, Ideal.Quotient.mk _ (MvPolynomial.X i) ∈ (q v).asIdeal`
   say that q(v) is the origin (φπ,a,b). Indeed this prime contains the
   maximal ideal of R' and both coordinates; their generated ideal is maximal,
   with quotient the residue field of R', so these conditions specify exactly o.
6. The separate universal clause quantifies over EVERY diagram with exactly
   those conditions and concludes
   `IsRegularLocalRing (X.presheaf.stalk x) ↔ n = 1`.
   This is not a criterion merely for one existentially selected chart.
7. `∀ x, ringKrullDim (X.presheaf.stalk x) ≤ 2` gives the dimension bound at all
   points, including generic points. The following clause quantifies over z in
   `f.fiber (IsLocalRing.closedPoint R)` with singleton closed in that fibre and
   asserts dimension two of the TOTAL SPACE stalk at its image via `f.fiberι`.
8. The final finite-set clause uses negation of total-space stalk regularity.
   Its following clause gives closedness, special-fibre membership, and the same
   pointed diagram with `2 ≤ n` at every such point. This does not identify all
   nonsmooth points with nonregular points: the n=1 case is retained.

Dependency interfaces read and used:

- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`; the quasi-compact/quasi-separated clauses use
  the established Mathlib morphism classes, as specified by the node record.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` and
  `Scheme.Hom.smoothLocus`; Morphisms.Etale: `Etale`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`;
  Mathlib.AlgebraicGeometry.Fiber: `Scheme.Hom.fiber`, `fiberι`.
- Mathlib.AlgebraicGeometry.Properties: `IsReduced`.
- Sheaf.AlgebraicGeometry.PureDimension: `Scheme.IsPureDimension`.
- Mathlib.RingTheory.AdicCompletion.Basic: `AdicCompletion`;
  Mathlib.RingTheory.MvPowerSeries.Basic: `MvPowerSeries`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`, `IsNoetherian`.
- def-weil-regular-scheme's ring clause uses Mathlib's `IsRegularLocalRing`,
  exposed through Sheaf.AlgebraicGeometry.IsRegularScheme; no replacement
  regularity predicate is introduced.
- Mathlib.Algebra.Polynomial.Basic supplies the established polynomial
  construction; the existing two-variable model uses `MvPolynomial`.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`.
- def-weil-algebraic-closure's recorded Mathlib match includes `IsAlgClosed`,
  from Mathlib.FieldTheory.IsAlgClosed.Basic, the clause used here.
- Sheaf.TraceFormula.StrictSemistableCurve: `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`.
- Sheaf.AlgebraicGeometry.NodalPointEtaleLocality:
  `Scheme.Hom.completedLocalScalarMap`, owned by the live definition node
  `def-trf-completed-local-scalar-map` (Q139, existing:true).

The owning nodes `def-trf-strict-semistable-curve` and
`def-trf-completed-local-scalar-map` are already landed and are added to
stmt_deps, as allowed by brief-stage2 §5. They supply the existing model and coefficient
map actually used in the signature. No new definition node or dependency
repair is needed. All other node fields stay unchanged except lean.

The stated proof dependencies with available declarations are imported privately:
GenericFibrePointsSmooth, NodalFamilyFittingSingular, UnramifiedBaseChangeOpen,
UnramifiedFieldFibreDecomposition, FibreDimensionAfterBaseChange,
SmoothTraitCurveLocalProperties, TraitNodalEtaleDvrModel,
EtaleSmoothZeroDimensionalFibres, SmoothEtaleLocalSource and the recorded
Mathlib leaves. The two proof nodes lem-sfb-etale-stalk-invariants and
lem-sfb-dvr-binomial-local-geometry have no recorded declaration in the read
clone and are not required to elaborate the statement; their proof plan is
retained verbatim for stage 3. No downstream theorem is assumed in a hypothesis.

Edge cases checked before and after writing:

- X empty, empty generic or special fibres, and disconnected fibres: no
  Nonempty or connectedness hypothesis; empty geometric fibres meet hfib.
- A smooth family: both exceptional sets may be empty and chart obligations
  are then vacuous; dimension and closed-special-point conclusions still apply.
- A nodal model with n=1: its nonsmooth origin is regular in the total space;
  this is allowed by every clause. Models n≥2 satisfy the separate nonregular
  conclusions. n=0 is excluded only from the asserted nonsmooth pointed charts.
- Special-fibre generic points are covered only by the dimension upper bound;
  the equality-two clause requires closedness in the SPECIAL FIBRE, rather
  than closedness in X or an unstated rationality condition.
- Arbitrary residue characteristic and imperfect residue fields are allowed;
  no excellence, completeness, perfection, separatedness or properness binder.
- All geometric test fields and chart rings use the same universe u as R and
  X, so no independently smaller test universe can make the hypothesis vacuous.
  The canonical fraction field and algebraic closures exist in that universe.

Searches actually run (2026-10-24):

- msearch.py leanfinder: "A flat finitely presented nodal curve over a DVR with
  smooth generic fibre has finitely many singular points and pointed etale
  charts xy equals uniformizer power". Eight hits, including
  WeierstrassCurve.IsMinimal, WeierstrassCurve.IsGoodReduction,
  StandardEtalePair, StandardEtalePresentation, and
  Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial.
  None states arbitrary nodal-trait finiteness and all local-dimension clauses.
- msearch.py loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale".
  One hit, AlgebraicGeometry.Etale.instSmooth, only etale-implies-smooth.
- msearch.py grep: "nodal|singular.*finite|finite.*singular", subdirectory
  AlgebraicGeometry. Zero hits.
- msearch.py leansearch: "Finite nonsmooth locus and pointed etale nodal charts
  of a smooth generic curve over a discrete valuation ring". Eight hits:
  Algebra.smoothLocus, Algebra.etaleLocus,
  Algebra.etaleLocus_eq_unramfiedLocus_inter_smoothLocus,
  Algebra.isOpen_smoothLocus, AlgebraicGeometry.IsSmooth.casesOn,
  Algebra.smoothLocus_eq_univ_iff, Algebra.smoothLocus_comap_of_isLocalization,
  AlgebraicGeometry.IsEtale. No exact match.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  `nodal_trait_finite_singular`: no existing declaration. Searches for nodal
  models and completedLocalScalarMap located the two reused landed interfaces.
  The upstream-name index also has no main theorem-name match. No duplicate
  foundational definition is introduced.

Sources read: literature/stacks-project/models.tex, labels
example-blowup (0CDC), lemma-etale-local-at-worst-nodal (0CDD), and
lemma-blowup-at-worst-nodal (0CDE), particularly its first proof paragraph.
Their model, origin and regularity description agrees with the node.
No STATEMENT-DISPUTED issue or source-based statement correction was needed.

Validation: scompile.py successfully compiled the module under its sandbox and
intended library names using the default 60-second limit. Both autoImplicit
and relaxedAutoImplicit are disabled. The delivery dry run passed its server
preflight and per-file compilation (OK); the only postponed proof is the item's
theorem.

## Second reading by Q113

Worker self-check, with the node and final Lean source both open; the independent
review is the maintainer's subsequent review, not a claimed second agent.
I reread the closed-geometric-point premise, finite-presentation hypotheses,
coefficient-compatible completed local algebra, every existential chart field,
the universal regularity criterion, all-point dimension bound, special-fibre
closed-point equality, and final nonregular clauses against the original node.
The origin membership conditions specify the unique maximal prime (φπ,a,b),
and the common R'-structure is q followed by the existing base map. In
particular, no closed-point assumption was lost from hnodal, no n=1 node was
misclassified as nonregular, and no empty fibre was excluded. There was no
mathematical mismatch requiring a correction. A malformed import generated
from a multi-file Mathlib match was repaired before the successful compile;
the final imports use separate valid module names.

## Repair of returned delivery 3c0f1286fc5f

H2 repaired: replaced `lem-trf-nodal-point-etale-locality` in the item's
stmt_deps by `def-trf-completed-local-scalar-map`. Read the live owning
definition node and its existing:true binding to
`AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap` in
`Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`, then read that definition's
full signature, docstring and explicit composite. The statement needs this
canonical scalar map and does not use the nodal-point-locality theorem.
The definition node is now named explicitly in the dependency discussion.
No theorem statement, Lean source, or other node field changed in this repair.
The maintainer found the mathematical substance correct and requested only
this DAG dependency correction. Comparison with the current shared node
confirms that the delivery changes only stmt_deps and lean. The delivery
wrapper refreshes the current main branch and constructs the repaired commit
on that branch; it is not an unchanged re-push of the returned head.
