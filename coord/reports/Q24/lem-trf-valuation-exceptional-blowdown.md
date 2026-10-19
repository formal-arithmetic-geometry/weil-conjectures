## Worker report

The module `Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown` states
`AlgebraicGeometry.Temkin.valuation_exceptional_blowdown`, with one `sorry` and no
new definitions or proved lemmas. The informal statement is unchanged. The node's
statement dependencies gain three already landed nodes:
`def-trf-multipointed-curve`, `def-trf-multipointed-curve-modification`, and
`lem-trf-valuation-exceptional-closed-image-criterion`. The last owns the exact
closed-image and exceptionality predicates needed here; none is duplicated.
No dependency node is modified.

Source read: Temkin, *Stable modification of relative curves*, §1.2, the definition
preceding Lemma 4.4.5 and Lemma 4.4.5, and Proposition 4.4.6, printed pp. 32--33,
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf . The source constructs
an exceptional blowdown of the chosen exceptional component and proves its
semistability; the node spells out the associated fibre-generic bijection.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation subring V of K, with fraction field K | `(V : ValuationSubring K)`; its defining `mem_or_inv_mem'` is the valuation property and Mathlib provides `IsFractionRing V K` for the inclusion |
| Prime ideals form a finite chain | `[Finite (PrimeSpectrum V)]`; the chain property is automatic for valuation rings |
| T = Spec V, eta = Spec K | Base of `X Y` is `Spec (.of V)`; eta is always `Spec.map (CommRingCat.ofHom V.toSubring.subtype)` |
| Multipointed target (X,D) and source (Y,E) | `X Y : MultipointedCurve (Spec (.of V))`; curve/marking schemes and maps are the structure fields |
| Smooth generic target curve | `hX : Smooth (pullback.snd X.x ...)` |
| Etale generic target marking | `hD : Etale (pullback.snd X.d ...)` |
| Semistable eta-modification f | `f : Y.Hom X`, `hf : f.IsEtaModification ...`, and `hY : Y.IsSemistable` |
| B_f consists of fibre-component generic points whose image is closed in the entire original X | `f.closedImageFiberGenericPoints`; the first conjunct is `IsClosed ({f.curve z} : Set X.X)`, before the existential ordinary-fibre generic-point witness |
| Chosen z belongs to B_f | `z : Y.X` and `hz : z ∈ f.closedImageFiberGenericPoints` |
| z exceptional: contracted reduced component, geometrically P1, at most two marking/singular points | `hze : f.IsExceptionalFiberGenericPoint z`; the existing predicate uses a reduced closed component with its exact generic-point closure, a field-linear P1 isomorphism after algebraic closure, and the intersection with `Y.specialPoints` of encard at most 2 |
| Intermediate multipointed pair and compatible maps | `∃ (Y₁ : MultipointedCurve ...) (f₁ : Y₁.Hom X) (h : Y.Hom Y₁)` |
| f1 semistable eta-modification | `f₁.IsEtaModification ... ∧ Y₁.IsSemistable` |
| h eta-modification | `h.IsEtaModification ...` |
| f1 composed with h equals f as a pair | `h.curve ≫ f₁.curve = f.curve` and `h.marking ≫ f₁.marking = f.marking` |
| h contracts C_z to a point | `(h.curve '' closure ({z} : Set Y.X)).Subsingleton` |
| Every remaining B_f point maps into B_f1; the actual point map is bijective | `Set.BijOn h.curve (f.closedImageFiberGenericPoints \ {z}) f₁.closedImageFiberGenericPoints`; BijOn includes MapsTo, InjOn and SurjOn |
| B_f1 uses exactly the same closed-image rule and unchanged X | The very same predicate is applied to `f₁ : Y₁.Hom X` |

The ambient closure used in the contraction clause is exactly C_z, not its
horizontal closure over more base points: since f(z) is closed in X, its inverse
image is closed in Y, contains z, and is contained in Y_t by compatibility over T.
Thus closure of z in Y lies inside that ordinary fibre and equals the image of
the fibre component closure. It is nonempty because it contains z, so the
subsingleton image expresses contraction to one point.

The long definitional clauses at the end of the node are retained through the
landed definitions. `MultipointedCurve` requires flatness, local finite
presentation, quasi-compactness and quasi-separatedness on both structural maps,
pure fibre dimensions 1 and 0, and a closed marking immersion. It imposes neither
properness nor separatedness of the curve over T. `IsSemistable` uses the
algebraic-closure fibres, smooth-or-ordinary-double-point alternatives, etale
marking and relative smoothness of the marking. The ordinary-double-point
predicate uses the maximal-ideal completion and the two-variable nodal power
series algebra. `IsEtaModification` requires properness of both maps,
isomorphisms over schematically dense opens on both sides, and isomorphisms of
both generic fibres. Schematic density is injectivity on sections of every open.
The node's final explanation of stability is the existing `Hom.IsStable`; this
lemma adds no stability hypothesis or conclusion.

Dependency declarations inspected and used:

- `Sheaf.TraceFormula.MultipointedCurve`:
  `AlgebraicGeometry.MultipointedCurve`, with all its fields inspected.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, its canonical curve/marking base changes,
  `MultipointedCurve.IsSemistable`, `Hom.IsEtaModification`,
  `MultipointedCurve.specialPoints`, and the explanatory `Hom.IsStable`.
- `Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion`:
  `MultipointedCurve.geometricComponentInclusion`,
  `Hom.closedImageFiberGenericPoints`, `Hom.IsExceptionalFiberGenericPoint`.
  Its theorem is not assumed as a new hypothesis; this import supplies its
  previously landed definitions.
- The original Mathlib dependency records were read: `IsSepClosed` and
  `IsSepClosure` (`Mathlib.FieldTheory.IsSepClosed`), `Field`
  (`Mathlib.Algebra.Field.Defs`), `topologicalKrullDim`
  (`Mathlib.Topology.KrullDimension`), `LocallyOfFinitePresentation`, `Smooth`,
  `Etale`, `Flat`, `IsClosedImmersion`, `IsProper` in their recorded scheme
  morphism modules, `Spec` and `Spec.map` (`Mathlib.AlgebraicGeometry.Scheme`),
  `pullback` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`),
  `irreducibleComponents` (`Mathlib.Topology.Irreducible`), `AdicCompletion` and
  `IsAdicComplete` (`Mathlib.RingTheory.AdicCompletion.Basic`), and `MvPowerSeries`
  (`Mathlib.RingTheory.MvPowerSeries.Basic`). They enter through the public
  definition imports, so no unused direct imports were added.
- Stated proof dependencies are imported without `public`:
  `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal`
  (`AlgebraicGeometry.geometricallyReduced_etaNormal`),
  `Sheaf.TraceFormula.ValuationHorizontalCurveModels`
  (`AlgebraicGeometry.horizontal_curve_models`), and
  `Mathlib.AlgebraicGeometry.Noetherian` (the finite-type/Noetherian and finite
  irreducible-component facts recorded by the two Mathlib proof leaves).
  The finite-fibre domination, projective preparation, exceptional local
  criterion, polar-section, and normalized-graph proof nodes currently have no
  recorded Lean module; consequently there is no speculative import for them.
  They are proof inputs, not missing notions needed for the present signature.

Edge cases checked before writing:

- Empty markings are allowed without any nonemptiness binder.
- Empty curves, empty B_f and the height-zero case V = K remain covered; the
  exceptional witness hypotheses then exclude impossible applications. No
  positive height, nonempty marking, connectedness, or characteristic is added.
- X and Y may be nonproper and nonseparated over T. Properness is only that of
  the pair modifications, as in the source.
- The component's base point need not be closed in T; the closed-image condition
  is in the entire original X. The closure argument above does not require the
  base point to be closed.
- If B_f consists just of z, BijOn has empty domain and requires exactly an empty
  B_f1. Larger sets use the actual h point map; there is no arbitrary equivalence.
- All schemes and K use the explicit common universe u. No independent smaller
  test universe, residue-field restriction or extra field assumption is imposed.

Searches for an existing statement (2026-10-17 UTC):

- `msearch.py` LeanFinder: “Contract an exceptional projective line component of
  a semistable multipointed curve over a valuation ring preserving semistability
  and removing one closed image fibre generic point”. Eight results: projective
  valuative criterion, rational-map/function-field interfaces, and Weierstrass
  minimal/good reduction results. Their returned signatures do not state this
  marked relative-curve contraction.
- `msearch.py` Loogle: `"semistable"`; zero results.
- `msearch.py` grep: `exceptional|semistable|blowdown`, restricted to
  `Mathlib/AlgebraicGeometry`; zero results.
- `msearch.py` LeanSearch: “Exceptional blowdown of a semistable marked relative
  curve removes a single contracted rational component”; service UNAVAILABLE
  (rate limit exceeded). This is not counted as a no-match verdict.
- `rg` in `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `lem-trf-valuation-exceptional-blowdown|valuation_exceptional_blowdown|exceptional_blowdown`:
  only the downstream semistable-stable-contraction proof docstring mentions the
  item; no existing theorem. Broader searches for multipointed curves,
  exceptional components and closed-image generic points located the reused
  modules listed above. Read their full signatures and docstrings.

The module docstring carries all eight proof steps and their DAG inputs. One
proof-plan issue is reported for stage 3: the inherited Step 6 identifies the
reduced support of the contracted fibre, while the local-criterion node's current
statement expressly uses the scheme-theoretic fibre. An application in Step 7
must justify the required reducedness or use the precise support version of
Temkin's criterion; support equality alone does not justify scheme equality.
This does not alter the source-supported exceptional-blowdown statement, and no
additional hypothesis was inserted to hide the issue.

Validation: the single delivered file compiled cleanly with `scompile.py`, with
both the sandbox and library module checks successful. The only proof is the
required `sorry`; no auxiliary construction or theorem is introduced.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
