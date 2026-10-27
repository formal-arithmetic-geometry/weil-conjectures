## Worker report

The module `Sheaf.TraceFormula.NodalAdjunctionPreparation` states
`AlgebraicGeometry.nodal_adjunction_preparation`, with its sole proof `sorry`.
It defines no new notion and does not change the node statement or any dependency.
The theorem docstring carries all eight steps of the accepted proof plan.

Sources read: Stacks `curves.tex`, `lemma-nodal-lci` (0C4E) and
`lemma-facts-about-nodal-curves` (0E37); the recorded canonical adjunction statement
and its complete `FlatLCICanonicalAdjunction.lean` interface; the pointwise lci
criterion and regular-sequence neighbourhood interfaces. The current latest blueprint
`lem-trf-local-term-locality.md` and its proof were also read: this is an auxiliary
node of its previously accepted semistable-modification branch, not a direct
restatement of the latest unit. The node's source explicitly labels this preparation
as a synthesis of the Stacks inputs.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Finite-type morphism C → Spec k | `(C : Scheme.{u}) (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]`, exactly the two conditions in the dependency record |
| Pure dimension one | `(hpure : C.IsPureDimension 1)` |
| Every nonsmooth point is closed | `hnodal` quantifies over **all** `x : C`, assumes `x ∉ p.smoothLocus`, and concludes `IsClosed ({x} : Set C)` |
| Completed local ring k-isomorphic to k[[u,v]]/(uv) | The other conjunct of `hnodal` is a ring equivalence from `AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)` to `MvPowerSeries (Fin 2) k ⧸ Ideal.span {X 0 * X 1}`, satisfying the displayed scalar equation for every `a : k`. The scalar map is the structure map on global sections followed by the germ and the canonical map into the completion. Thus this is an isomorphism as a k-algebra, not merely an unconstrained ring isomorphism. |
| No separatedness or properness assumption | Neither occurs among the binders or hypotheses |
| C Noetherian (quasi-compact and locally Noetherian) | `IsNoetherian C`, whose class extends `IsLocallyNoetherian C` and `CompactSpace C` |
| C reduced | `IsReduced C` |
| p flat | `Flat p` |
| p finitely presented | `LocallyOfFinitePresentation p ∧ QuasiSeparated p`, together with the existing input `[QuasiCompact p]`; no redundant tautological output conjunct is introduced |
| All nonempty geometric fibres pure dimension one | `HasPureFlatLCIGeometricFibres p 1`; its recorded definition uses the pullback along the chosen algebraic closure of each residue field and quantifies over all irreducible components, so empty fibres are vacuous |
| Affine open cover by finite-type lci k-algebras | For every `x`, there exists `U : C.affineOpens` containing `x` and a finite-type witness `ft` for its coordinate algebra with the induced structure map, satisfying `Algebra.IsLocalCompleteIntersection k Γ(C,U.1)` with that same algebra structure and witness |
| Closed presentations into opens of affine n-space, regular equations of length n−1 | The same affine neighbourhood has `Nonempty (FlatLCIPresentation p 1 U.1)`. Its existing fields give `ambient : P ⟶ AffineSpace ... (Spec k)` open, `i : U.toScheme ⟶ P` closed, the factorization over k, local regular generators of `i.ker`, and `rank_eq : n = c + 1`, precisely c=n−1. Regularity is at every prime on the closed source, the usual locally-generated-by-a-regular-sequence condition. |
| T cut out by Fit_1 Ω | `(Scheme.firstFittingIdealSheaf p).subscheme`, with its recorded inclusion `Scheme.firstFittingSingularSubscheme p` |
| T finite disjoint union of Spec k | `∃ (I : Type u) (_ : Finite I) (e : (∐ fun _ : I ↦ Spec (.of k)) ≅ T), ...`. The equation on each summand states that this is an isomorphism **over k**, so the conclusion includes the scheme structure and excludes nilpotent thickening. |
| Support exactly nonsmooth locus | `Set.range (Scheme.firstFittingSingularSubscheme p) = (p.smoothLocus : Set C)ᶜ` |
| Smooth locus contains every generic point | For every irreducible component `Z` and `ξ : C`, `IsGenericPoint ξ Z → ξ ∈ p.smoothLocus` |
| Adjunction applies with d=1 | The flat/fp/purity conclusions and the affine `FlatLCIPresentation p 1` neighbourhoods supply every hypothesis of `exists_flatLCICanonicalAdjunction`. The final conjunct supplies its actual `F : FlatLCIAdjunctionSystem p 1` with `F.IsNormalized`. The structure includes the invertibility, local adjunction lines, coherent base change and normalized transitions. |
| Invertible K_C/k and canonical smooth identification with Ω¹ | `F.line (FlatLCIBaseChange.identity p)` is the original invertible module by `F.invertible`. The final `e` identifies its tensor restriction to the full smooth locus with `(p.smoothLocus.ι ≫ p).relativeDifferentials`. The auxiliary isomorphism `w` from the first exterior sheaf is fixed on every wedge by `w.hom.app V (exteriorSheafSection ... a) = a 0`. Finally `F.IsSmoothComparison ... (e ≪≫ w.symm)` imposes the dependency's exact determinant/conormal normalization. Thus neither the line nor its smooth comparison is an arbitrary module/map. |

Dependency declarations read and used:

- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed` (the algebraically-closed-field clause of the recorded match).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, used through the recorded pure-dimension predicates.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, with its actual ring/algebra structure from `.Algebra`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries` and `MvPowerSeries.X`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` and `AlgebraicGeometry.IsNoetherian`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `AlgebraicGeometry.QuasiSeparated`.
- `def-weil-geometric-fibre`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, used in `flatLCIGeometricFibre`.
- `def-weil-pbc-complete-intersection-over-field`:
  `WeilConjectures.RingTheory.CompleteIntersectionOverField`,
  `Algebra.IsLocalCompleteIntersection` and its `IsGlobalCompleteIntersection` definition.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`, used by `FlatLCIPresentation.regular`.
- `def-trf-first-fitting-singular-subscheme`:
  `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`,
  `Scheme.firstFittingIdealSheaf` and `Scheme.firstFittingSingularSubscheme`.
- `lem-trf-flat-lci-canonical-adjunction`:
  `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, `FlatLCIPresentation`,
  `HasPureFlatLCIGeometricFibres`, `FlatLCIAdjunctionSystem`,
  `FlatLCIAdjunctionSystem.IsNormalized`, `FlatLCIAdjunctionSystem.IsSmoothComparison`,
  `FlatLCIBaseChange.identity`, `exists_flatLCICanonicalAdjunction`.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `Scheme.Modules.IsInvertible`, supplied for the line by `F.invertible`.
- `def-sc-relative-differential-sheaf`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `Scheme.IsPureDimension`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used by `FlatLCIPresentation.closed`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.

Statement dependencies are public imports (directly or through the recorded adjunction
module's public dependencies). Already stated proof dependencies have plain imports:
`RegularSequencePrincipalNeighbourhood`, `LciPointwiseCriterion`,
`NodalCurveLCICriterion`, `NodalClosedPointsReduced`, `RelativeDimensionBaseChange`,
`UnramifiedFieldFibreDecomposition`, the upstream
`GlobalCompleteIntersectionEquidimensional` and
`GlobalCompleteIntersectionLocalRegularSequence`, and the relevant Mathlib modules.
The proof-only nodes `lem-trf-field-curve-fitting-smooth-preparation` and
`lem-trf-locally-algebraic-dimension-components` have no recorded module in the read
snapshot, so there is no module to import for those. They are retained verbatim in
the proof plan and node proof dependencies. No missing notion in the statement
requires a new node or dependency repair.

Edge cases checked mathematically before writing:

- Empty C: pure dimension one, all pointwise hypotheses, the affine neighbourhood
  assertion and geometric-fibre assertion are vacuous. Take the empty finite index
  for the singular subscheme. No nonemptiness or surjectivity binder excludes it.
- A smooth affine line: the nodal hypothesis is vacuous, Fit_1 Ω is the unit ideal,
  T is empty, and the zero-equation presentation has n=1 and c=0.
- `uv=0`: the differential presentation has relation `v du + u dv`, so Fit_1 is
  `(u,v)`, giving one reduced Spec k, in every characteristic including two. The
  standard chart has n=2, c=1.
- Smooth curves glued with doubled origin: finite type and pure dimension one remain
  allowed despite nonseparatedness. Neither hypotheses nor the adjunction interface
  require a separated structural morphism.
- Every irreducible component, including reducible and disconnected curves, is covered
  by the generic-point and geometric-fibre clauses. The single universe u follows
  the project's scheme convention and places no independent smaller bound on tests.

Searches actually run:

- `msearch.py ... leanfinder "A finite type nodal curve has a finite reduced singular
  subscheme and canonical adjunction line"`: eight hits, including
  `WeierstrassCurve.Affine`, `Affine.Nonsingular`, and Weierstrass coordinate-ring
  results; no statement of this general nodal-curve preparation.
- `msearch.py ... loogle '\"AlgebraicGeometry\", \"CompleteIntersection\"'`:
  zero hits.
- `msearch.py ... grep 'nodal|ordinary.double|canonical.*adjunction' AlgebraicGeometry`:
  one hit, `GammaSpecAdjunction.lean`, for the unrelated global-sections adjunction.
- `msearch.py ... leansearch "Finite type nodal curves over an algebraically closed
  field have a finite reduced singular subscheme and canonical adjunction line"`:
  eight hits, including `finite_irreducibleComponents_of_isNoetherian`, `IsReduced`,
  and finite-fibre results, none stating the item.
- `rg -n 'nodal|nodalAdjunction|nodal_adjunction' lean/WeilConjectures lean/Sheaf`:
  nodal criteria, nodal subcurve and modification results, not this conjunction.
- `grep -rn 'lem-trf-nodal-adjunction-preparation' lean/WeilConjectures` and targeted
  `rg` for the node id and proposed declaration in both library roots: no existing
  declaration for this node.

The normal module-mode server compilation through `scompile.py Q74
lem-trf-nodal-adjunction-preparation .../NodalAdjunctionPreparation.lean` passed for
both the sandbox and the final module name, with no errors or warnings. Explicit
`autoImplicit false` and `relaxedAutoImplicit false` are set. There are no helper
proofs or definitions, and no statement dispute or source correction is needed.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
