## Worker report

This repairs the returned stage-2 delivery at immutable head `79e0499e78a6`.
The retained packet was inspected first and its required dry run passed mechanically
(commit `02bdffcb43`). The semantic self-check reproduced the returned conclusion gaps,
so the packet was repaired before pushing. The current main node was read and compared:
all fields outside `lean` remain identical to current main. No natural-language node
statement was corrected.

`Sheaf.SixFunctors.TraceFormula.NodalEtaleChart` defines the helper
`AlgebraicGeometry.nodalOrigin` and states
`AlgebraicGeometry.exists_nodal_etale_chart`. Only the theorem has `sorry`.
The helper uses the two universal coordinates of the recorded nodal model and says their
germs belong to the maximal ideal, equivalently that their residues vanish. Its data is
an explicit predicate, not a choice or a postponed construction.

Source passages read for this repair: Stacks `curves.tex`, Tag 0CBY,
`lemma-etale-local-structure-nodal-family`, its statement and both proofs; ILO Exposé VI
§§1.1–1.4, 1.8 and Proposition 1.9 with proof (printed pp. 69–71, PDF pp. 75–77).
The coordinate-zero conclusion follows the recorded smooth-pair coordinate theorem,
whose full signature and Cartesian-square clause were read.

Every hypothesis of the node is represented as follows:

| Node hypothesis | Lean rendering |
| --- | --- |
| Locally Noetherian schemes X,Y | `{X Y : Scheme.{u}}`, `[IsLocallyNoetherian X]`, `[IsLocallyNoetherian Y]` |
| Log regular pair (Y,T), divisorial log structure | Dense open immersion `j : U₀ ⟶ Y`, `[IsOpenImmersion j]`, `hU : DenseRange j`, and `hlog : IsDivisorialFineSaturatedLogRegularPair Y U₀ j hU`; T is the closed complement of the image of j |
| Flat locally finitely presented f | `(f : X ⟶ Y)`, `[Flat f]`, `[LocallyOfFinitePresentation f]` |
| Nonempty connected one-dimensional nodal geometric fibres | `hNodal : HasNodalGeometricFibres f`, with its recorded geometric-fibre completion condition |
| f smooth over Y minus T | `hSmooth : ∀ x : X, f x ∈ Set.range j → x ∈ f.smoothLocus` |
| Effective Cartier divisor D in X | `(D : Scheme.{u}) (i : D ⟶ X) (hCartier : IsEffectiveCartierCenter i)`, whose definition uses an invertible quasi-coherent ideal and its closed subscheme |
| D etale over Y | `[Etale (i ≫ f)]` |
| D supported in the relative smooth locus | `hD : ∀ d : D, i d ∈ f.smoothLocus` |

Every conclusion clause is represented as follows:

| Node conclusion | Lean rendering |
| --- | --- |
| Every geometric point x over y | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)`; y is its composite with f |
| Etale source/base neighbourhoods, compatible with f | `V : Y.Etale`, `v : W ⟶ X`, `Etale v`, `w : W ⟶ V.left`, and `v ≫ f = w ≫ V.hom` |
| The neighbourhood contains the chosen geometric point | `xW : Spec (.of Ω) ⟶ W`, `xW ≫ v = x`; its composite with w is the base geometric lift |
| Smooth unmarked case | `(Scheme.SpecToEquivOfField Ω X x).1 ∈ f.smoothLocus`, outside `Set.range i`, and `Smooth w` |
| Empty marking on smooth unmarked neighbourhood | `∀ z : W, z ∉ Set.range (pullback.snd i v)` |
| Marked point | `(Scheme.SpecToEquivOfField Ω X x).1 ∈ Set.range i` |
| Etale V-map to the relative affine line | `e : W ⟶ AffineSpace (ULift (Fin 1)) V.left`, `Etale e`, and `e ≫ (AffineSpace.over ...).hom = w` |
| D intersect W is exactly z=0 as a closed subscheme | `IsPullback g (pullback.snd i v) ((AffineSpace ...).zeroLocusSubschemeι {AffineSpace.coord V.left (ULift.up 0)}) e`; this is scheme-theoretic, not only equality of support |
| Nonsmooth case, marking removed | Underlying image of x outside `f.smoothLocus`, and the same explicit empty-pullback-marking condition as in the smooth unmarked case |
| Etale nodal model uv=h over V | `h : Γ(V.left, ⊤)`, `m : W ⟶ pullback nodalModelBaseMap (nodalBaseMap h)`, `Etale m`, and the equality to w after the projection; the imported model is the actual polynomial quotient |
| Chosen point sent to u=v=0 | `nodalOrigin h (m (Scheme.SpecToEquivOfField Ω W xW).1)`; both coordinates vanish in the residue field, not in the local ring |
| h invertible on V minus T_V | Every germ of h at a point of the range of `pullback.snd j V.hom` is a unit |
| h is a divisorial section | The final equality `h = ε.1 * (c a).1`, with `c a : divisorialSections j V` and ε a unit, gives precisely this membership |
| Fine saturated chart and unit factorization | Existential `P`, its `CommMonoid` structure, `IsFineSaturatedMonoid P`, `c : P →* divisorialSections j V`, the prescribed `IsDivisorialStalkChart` at every pointed geometric stalk, and `ε`, `a` with the displayed equality |
| All three neighbourhoods carry a fine saturated base chart | The same `P`, `c`, saturation and stalk-chart clauses are outside and before the disjunction of the three cases, on the very same V |

The chart and neighbourhood data are conclusions, not stronger input hypotheses. Factoring
these common existential data before the three alternatives expresses the node's refinement
clause in all cases. The nonsmooth alternative uses that same chart c for its factorization.
No separate helper definition of a chart is introduced: the recorded log-regular-pair
interface is used directly. No new nodes or dependency modules are necessary.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`;
- `Sheaf.AlgebraicGeometry.LogRegularPair`,
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`, `divisorialSections`,
  `divisorialStalk`, `strictLocalRing`, `divisorialGerm`, `IsFineSaturatedMonoid`,
  and `IsDivisorialStalkChart` (including the pushout chart definition);
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`;
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`;
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`,
  `AlgebraicGeometry.HasNodalGeometricFibres`;
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` (the Mathlib match of
  `def-nagata-effective-cartier-ideal`); used through the imported
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`,
  `AlgebraicGeometry.IsEffectiveCartierCenter`;
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`;
- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`, and
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.SpecToEquivOfField`;
- `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace` and
  `AffineSpace.over`; the coordinate zero subscheme is the existing
  `Scheme.zeroLocusSubscheme`/`Scheme.zeroLocusSubschemeι` construction;
- `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`,
  `nodalModelRing`, `nodalModelBaseMap`, `nodalBaseMap` and
  `exists_etale_nodal_local_model` (the model declarations occur in the statement);
- Proof imports: `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`,
  `Scheme.Hom.exists_etale_smooth_pair_coordinates`, and
  `Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular`,
  `nodal_family_fitting_singular`. Both are non-public proof-only imports.

Searches made in the original packet were retained in `searches.jsonl`. During repair:

- `msearch.py ... leanfinder "Etale local normal forms of a nodal family with etale Cartier markings and a fine saturated divisorial base chart"`: eight hits, including `StandardEtalePair`, `StandardEtalePresentation` and `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`. Their signatures supply standard algebra presentations, not the family chart with marking and divisorial-chart clauses.
- `msearch.py ... loogle "AlgebraicGeometry.AffineSpace, AlgebraicGeometry.Etale"`: no hits.
- `msearch.py ... grep "nodal|semistable|ordinary.double.point" AlgebraicGeometry`: no Mathlib hits.
- `rg` for `nodalOrigin|exists_nodal_etale_chart|HasDivisorialFsChart|lem-trf-nodal-etale-chart` over project `lean/Sheaf` and upstream `WeilConjectures`: no existing matching declaration. Direct source inspection found the coordinate zero-locus construction and the smooth-pair Cartesian square, both reused rather than redefined.

Edge cases checked: D empty eliminates the marked case and leaves the explicit empty
marking condition in both other cases. T empty makes the entire family smooth by hSmooth,
so there is no nonsmooth case. Empty X or Y makes geometric-point conclusions vacuous.
Disconnected schemes are allowed; no global connectedness is imposed beyond the recorded
connected geometric fibres. For the smoothing uv=π at the closed node, u and v have zero
residues but nonzero germs: the repaired nodalOrigin states exactly the residue condition.
For h a unit there is no point u=v=0, consistently with smoothness of that fibre. A constant
h=0 on a nonempty chart meeting the dense complement would contradict hSmooth and the unit
condition; it is not incorrectly admitted as a globally smooth-away-from-boundary model.
The marked test W=A¹_V and D=(z) satisfies the Cartesian square, whereas a thickening (z²)
has the same support but fails that square, so the old support-only gap is removed.
Geometric points and schemes use the shared universe u, matching the explicit convention
of the recorded geometric-fibre node; `ULift (Fin 1)` gives exactly one coordinate.

## Second reading by Q83

I re-read the saved packet against the unchanged current main node, all statement-dependency
records, the source declarations and the specified source passages. This second reading is
performed in this session: the dispatcher's instruction prohibits starting other agents.
The returned head's three defects were real. The old marked clause only compared point
sets; it now has `Etale e` and an actual Cartesian square with the coordinate zero subscheme.
The nonsmooth clause now removes D explicitly. The common fs chart is now scoped before
the alternatives, so it applies also at smooth and marked points and the nodal factorization
uses that same c. The provisional helper `HasDivisorialFsChart` was eliminated in favor of
the exact existing expanded chart interface.

The full self-check also found retained errors beyond the latest short return: the old
signature omitted smoothness off T, quantified only over topological points and did not
require a source lift in the smooth unmarked case. It now binds hSmooth, quantifies over
the recorded geometric-point data and requires an actual lift xW with equality as morphisms.
The old nodalOrigin incorrectly required zero local germs. The uv=π test detects the error;
maximal-ideal membership now gives the intended zero coordinates of the chosen point.

I checked conjunction/disjunction scope in the final signature: the same V, W, v, w, xW,
P and c are present in all three branches. The marked square's top map has domain
D×_XW, its left map is its inclusion in W, its right map is the coordinate-zero inclusion,
and its bottom map is e. The nonsmooth model map is over w; the origin condition uses the
image of xW, not an unrelated point. Chart stalk tests use the prescribed divisorial germ.
All hypotheses are those of the node, including flatness, local finite presentation,
nodal geometric fibres, log regularity, effective Cartier marking, etaleness and smoothness
conditions. No projectivity or properness is added. The theorem docstring now carries the
four natural-language proof steps, with the named proof dependencies and the shrinking
argument for invertibility. All variables/universes are explicit and Lean lines are at most
100 characters. No node-statement correction or STATEMENT-DISPUTED flag is needed.
