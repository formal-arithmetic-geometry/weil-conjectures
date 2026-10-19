## Worker report

The module `Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree` states
`AlgebraicGeometry.smoothTargetModificationExceptionalTree`, with one `sorry` and no new
definitions or proved theorems. The node's statement, proof, source, and proof dependencies
are unchanged. Its statement dependencies gain five already recorded nodes so the statement
uses their published definitions: `def-trf-modification`, `def-trf-projective-line-tree`,
`def-weil-pure-dimension`, `def-trf-orgogozo-induction-data`, and
`def-weil-pbc-scheme-reduction`.

I read the source, Temkin's *Stable modification of relative curves*, §1.2 (printed p. 2),
Lemma 4.4.2 (printed pp. 30–31), and Appendix B, Corollary B.2 (printed pp. 57–58),
in the [author's PDF](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf).
The lemma's reduction is local on the target; the proper curves used for the genus
calculation are auxiliary completions. The smooth-point case has one boundary point;
this delivery retains exactly the node's weaker bound of at most two.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field K, separably closed | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation ring V contained in K, with fraction field K | `(V : ValuationSubring K)`; its defining condition is membership of each element or its inverse, and its inclusion is `V.subtype`. This is a valuation subring of the specified field, not an unrelated abstract valuation ring. |
| Finitely many primes forming a chain | `[Finite (PrimeSpectrum V)]`; comparability of primes is automatic for a valuation subring, so no extra independent chain hypothesis is needed. |
| T = Spec V and eta = Spec K | Target `Spec (.of V)` and generic map `Spec.map (CommRingCat.ofHom V.subtype)` |
| W over T, flat and finitely presented | `(w : W ⟶ Spec (.of V))`, `[Flat w]`, `[LocallyOfFinitePresentation w]`, `[QuasiCompact w]`, `[QuasiSeparated w]`; all three finite-presentation properties are retained. |
| W has pure relative dimension one | `hWdim`, requiring `IsPureDimension 1` for every actual scheme fibre `w.fiber t` |
| Smooth generic fibre | `[Smooth (pullback.snd w (Spec.map (CommRingCat.ofHom V.subtype)))]` |
| Proper f, isomorphism generically and between schematically dense opens | `(f : Z ⟶ W)` and `hf : EtaModification ... f w`; unfolding gives `SchemeModification f`, its properness and dense-open isomorphism, plus invertibility of the canonical generic base-change map. |
| Schematic density means injectivity of O into j_*O | `SchemeModification.dense_open` uses `SchematicallyDenseOpen` both on the open of W and its inverse image in Z. That definition requires injective restriction on every ambient open, exactly the sheaf-injectivity condition. |
| Z over T, flat and finitely presented | The four properties on `f ≫ w`: `Flat`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` |
| Z has pure relative dimension one | `hZdim`, with `((f ≫ w).fiber t).IsPureDimension 1` at every t |
| Every geometric source fibre has only ordinary nodes as singularities | `hnodal`, for every algebraically closed `Ξ : Type u` and every `s : Spec Ξ ⟶ Spec V`, requires at every point either a genuinely smooth open neighbourhood or `Orgogozo.IsOrdinaryDoublePoint (pullback.snd (f ≫ w) s) z`. |
| Nodal completed local ring over the geometric field | `Orgogozo.IsOrdinaryDoublePoint` is a ring isomorphism from the maximal-ideal adic completion of the stalk to `Orgogozo.nodeRing Ξ`, together with the equation on every scalar. The latter ring is `MvPowerSeries (Fin 2) Ξ` modulo `(X 0 * X 1)`. No connectedness or nonemptiness of every fibre is smuggled into this condition. |
| x is smooth for W/T | `(x : W)` and `hx : ∃ U : W.Opens, x ∈ U ∧ Smooth (U.ι ≫ w)` |
| Scheme fibre Z_x has positive dimension | `hpositive : 0 < topologicalKrullDim (f.fiber x)` |
| Choose an algebraic closure Ω of κ(x) | `(Ω : Type u) [Field Ω] [Algebra (W.residueField x) Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic (W.residueField x) Ω]`; the last two conditions are precisely `IsAlgClosure` for fields. |
| Geometric point over x and composite s over T | The explicit term `Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫ W.fromSpecResidueField x` is the geometric point a of W; its composite with w occurs in `pullback.mapDesc`. |
| B is the reduced geometric modification fibre | `(pullback f a).nilradical.subscheme`, with its canonical inclusion `(pullback f a).nilradical.subschemeι`; the scalar structure map is that inclusion followed by `pullback.snd f a`. This is an actual construction, not an existential replacement. |
| B nonempty and connected | `IsProjectiveLineTree` includes `ConnectedSpace B`, hence `Nonempty B`. |
| B is a nodal curve | The same predicate includes `IsReduced B` and requires every closed nonsmooth point to have the scalar-compatible ordinary-double-point model. Its finite P1-component clause gives pure dimension one. |
| Finitely many irreducible components, each P1 over Ω | The predicate requires `(irreducibleComponents B).Finite` and a closed immersion from `ProjectiveLine (Spec Ω)` over Ω with image each component. As B is reduced, this gives exactly the reduced irreducible component with its scheme structure. |
| The dual graph is a tree, with all intersections counted | The predicate counts actual nodes, including self-nodes and separate parallel edges, requires finiteness of the node set and `#nodes + 1 = #components`. For this connected nodal curve this is precisely the connected acyclic incidence multigraph condition. |
| Boundary in the original Z_s, not the auxiliary compactification | Compose the reduction inclusion with `pullback.mapDesc f a w : pullback f a ⟶ pullback (f ≫ w) (a ≫ w)`. Its range is B inside the original `Z_s`. The second conjunct is `(range ∩ closure ((range)ᶜ)).encard ≤ 2`, with explicit parentheses around the complement. |
| No separatedness/properness over T, stability, or marking assumptions | There are no such binders. `QuasiSeparated` is retained only as part of finite presentation, not replaced by `IsSeparated`. Properness applies only to f through `EtaModification`. |

Dependency declarations and source modules read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the separably-closed clause of
  `def-kun-separably-closed`; `IsSepClosure` is not needed here).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; finite presentation also uses
  `QuasiCompact` and `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: read
  `AlgebraicGeometry.ProjectiveLine.TwistData` and the standard cover; the component
  conclusion uses the underlying `ProjectiveLine` already used by `IsProjectiveLineTree`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`, and
  `isAlgClosure_iff`; `Field` is Mathlib's standard class.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, and the existing `pullback.mapDesc` canonical morphism.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, with the
  completion ring used by `Orgogozo.IsOrdinaryDoublePoint`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `X`, `C`, used in the
  same recorded node-ring definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  used by the recorded modification predicate.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField` (only the first and
  third are needed in the formula).
- `Sheaf.TraceFormula.Modification`: `SchemeModification`, `EtaModification`;
  its dependency `Sheaf.TraceFormula.SchematicallyDenseOpen`:
  `SchematicallyDenseOpen`.
- `Sheaf.TraceFormula.ProjectiveLineTree`: `curveNodes`, `IsProjectiveLineTree`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.IsOrdinaryDoublePoint`,
  `Orgogozo.nodeRing`, `Orgogozo.localScalar`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring` and its inclusion.

The module imports every stated proof-dependency module without `public`: perfect
complexes, global sections of proper varieties, perfect direct-image base change,
torsion-freeness of invertible sections, genus-zero curves, nodal normalization adjunction,
projective modules over local rings, smooth geometric reducedness, and the relevant
Mathlib properness/Noetherian permanence modules. The three proof nodes
`lem-trf-nodal-contraction-euler-defect`,
`lem-trf-proper-normal-geometric-connectedness`, and
`lem-trf-valuation-modification-proper-completion` have no recorded declaration on the
read base; there is no unavailable proof-only import. Their roles remain in the full
eight-step proof docstring. They are not assumptions of the theorem.

Edge cases checked before writing:

- V = K is allowed. Its generic base change is the whole map, so generic invertibility
  excludes the positive-dimensional-fibre hypothesis; no false special case is asserted.
- Empty W admits no x. Empty Z or a zero-dimensional fibre cannot satisfy `hpositive`;
  the empty scheme has Krull dimension bottom. Empty and disconnected other fibres
  remain allowed by the pure-dimension and nodality hypotheses.
- One P1 component with no nodes satisfies the tree count; a self-loop, two parallel
  intersections, and a positive-genus component fail the appropriate clauses.
- No characteristic assumption occurs; K is only separably closed. Ω is algebraic over
  κ(x), so an arbitrary transcendental algebraically closed extension is not accidentally
  substituted for the specified algebraic closure.
- All schemes and test fields use the same arbitrary universe u, exactly as Mathlib's
  geometric scheme properties. There is no independent smaller universe making
  geometric tests vacuous. Every variable and universe is explicitly bound.
- The boundary uses the complement before closure and lies in the original geometric
  source fibre. In particular it is not computed in B itself, where it would vanish.

Searches for an existing theorem:

1. `msearch.py ... leanfinder` query:
   `A proper semistable modification of a relative curve over a valuation ring has rational tree exceptional fibre over a smooth point`.
   Eight hits: `WeierstrassCurve.IsGoodReduction`, `IsMinimal`, `minimal`,
   `exists_isMinimal`, `isGoodReduction_iff_isElliptic_reduction`,
   `instIsMinimalMinimal`, `isGoodReduction_iff`, `reduction`.
   None states the exceptional-fibre theorem.
2. `msearch.py ... loogle` query: `"IsProper", "Smooth", "tree"`.
   `OK 0 hit(s)`.
3. `msearch.py ... grep` query:
   `exceptional.*tree|rational.*tree|semistable.*modification`.
   `OK 0 hit(s)` in Mathlib.
4. `msearch.py ... leansearch` query:
   `Exceptional fibres over smooth points of semistable modifications of relative curves are projective line trees`.
   Eight hits: `Scheme.Hom.fiber`, `IsSmooth.casesOn`,
   `IsSmoothOfRelativeDimension.isSmooth`, `IsSmooth.recOn`,
   `instCanonicallyOverFiber`, `instIsAffineFiberOfIsAffineHom`,
   `IsSmoothOfRelativeDimension.casesOn`,
   `WeierstrassCurve.Projective.baseChange_nonsingular`.
   These are fibre/smoothness infrastructure, not this result.
5. Direct `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, with
   `smoothTargetModificationExceptionalTree|exceptional.*tree|rational.*tree|semistable.*modification`,
   found no same statement. The nearby `CurveP1TreeLocalCriterion` concerns proper
   marked curves of equal arithmetic genus; its full signature was read and it is
   not the relative valuation-base theorem. Its tree definition is reused.
6. Direct search for the exact node id in upstream `WeilConjectures` returned no hit.
   Source inspection found Mathlib's `pullback.mapDesc`, allowing the boundary to use
   an existing canonical map without a new helper definition.

No statement correction, missing notion, dependency-interface repair, or disputed
statement was needed. The theorem preserves the original hypotheses and the stated
bound rather than adding global properness or a global connectedness assumption.

Validation: `scompile.py Q13 lem-trf-smooth-target-modification-exceptional-tree` compiled
the sole delivered module cleanly (only its expected `sorry`); overlay dependencies
`ProjectiveLineTree` and `NodalNormalizationAdjunction` also compiled cleanly. The final
packet is checked again by the required dry-run delivery preflight before push.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
