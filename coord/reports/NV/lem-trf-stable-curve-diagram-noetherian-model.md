## Worker report

Repair of the return at e2dfcc8bc68e. The retained sandbox had only dispatcher marker
files, no module, node binding, or report. This delivery supplies the complete theorem
`AlgebraicGeometry.exists_normal_affine_finite_type_model_of_stable_curve_diagram`
in `Sheaf.TraceFormula.StableCurveDiagramNoetherianModel`, with a single `sorry` proof.
No definition is introduced and no mathematical statement or proof edge is changed.
The only node changes are `lean` and addition of the two landed definition prerequisites
`def-trf-multipointed-curve` and `def-trf-multipointed-curve-modification` to `stmt_deps`.
The delivery wrapper rebases the packet on current newtargets-dag.

Source read: Temkin, Stable modification of relative curves, arXiv:0707.3953v3,
§1.2 (printed p. 2), §3.1 and Remark 3.1.1(ii) (pp. 14–15), the normal approximation
paragraph of Proposition 3.5.2 (p. 20), Lemma 5.1(ii) (p. 34), and the first paragraph
of the proof of Theorem 1.2 (p. 35). The archival PDF is absent locally; the primary
PDF was opened at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf.
The finite-list, normal affine refinement, common-open, and reduced-total-space
expansions are exactly the agent-written nine-step DAG argument, not claimed to be
verbatim assertions of that PDF. All nine steps and their dependencies are carried
in the theorem docstring. The module docstring identifies the same source.

Hypotheses and definitions were matched individually:

| Node clause | Lean rendering |
| --- | --- |
| S is normal | `hnormal : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)` |
| S is integral and affine | `[IsIntegral S] [IsAffine S]` |
| (C,D) is a multipointed S-curve | `C : MultipointedCurve S`; its `X,D,x,d,i,comm` retain both objects, structure maps, and inclusion |
| Both structure maps are flat and finitely presented | Existing fields `flat_X, lfp_X, qc_X, qs_X` and `flat_D, lfp_D, qc_D, qs_D` |
| Pure relative dimensions 1 and 0 | Existing `pure_X` and `pure_D`; each component of each ordinary fibre has `topologicalKrullDim` 1 or 0 |
| Marking is a closed immersion | Existing field `closed : IsClosedImmersion C.i` |
| Smooth generic curve | `hCη : Smooth (C.x.fiberToSpecResidueField (genericPoint S))` |
| Etale generic marking | `hDη : Etale (C.d.fiberToSpecResidueField (genericPoint S))` |
| J finite, a source pair and compatible morphism for every j | `J : Type u`, `[Finite J]`, `Cj : J → MultipointedCurve S`, `f : ∀ j, (Cj j).Hom C` |
| Each f_j an eta-modification | `hf` uses `IsEtaModification (S.fromSpecResidueField (genericPoint S))` |
| Properness on curve and marking, schematic density on each part, generic isomorphisms | The existing `IsEtaModification` requires `IsProper f.curve`, `IsProper f.marking`, opens with injective restriction on every open on both source and target, and `IsIso` of both canonical maps on the specified generic fibre |
| Sources semistable | `hsemi : ∀ j, (Cj j).IsSemistable` |
| Nodal singularities | Existing `IsSemistable` uses smooth-or-`Orgogozo.IsOrdinaryDoublePoint` on `pullback P.x (Orgogozo.geometricPoint T t)`; the latter uses `AdicCompletion` at the maximal ideal and a scalar-compatible ring equivalence to `MvPowerSeries (Fin 2) Ω ⧸ (uv)` |
| Marking etale and in relative smooth locus | The last two clauses of existing `IsSemistable`: `Etale P.d` and `∀ e, P.i e ∈ P.x.smoothLocus` |
| Specified subset and stability on it | `Jst : Set J`, `hstable : ∀ j, j ∈ Jst → (f j).IsStable (...)` |
| Stability means no contracted P1 component with at most two special points | Existing `IsStable` quantifies over a closed immersion of the projective line over the algebraic closure with irreducible-component image, over that field; an intersection cardinality at most 2 forbids a subsingleton image under the geometric curve map |

Every conclusion clause is present:

| Node conclusion | Lean rendering |
| --- | --- |
| Normal integral affine model S0 | Existential `S₀`, conjuncts `IsIntegral S₀`, `IsAffine S₀`, and the explicit domain/integrally-closed stalk condition |
| Finite type over Z | `t₀ : S₀ ⟶ Spec (.of (ULift.{u} ℤ))` with `LocallyOfFiniteType t₀ ∧ QuasiCompact t₀`; ULift is the usual size lift of Z |
| Dominant map taking generic point to generic point | `s : S ⟶ S₀`, `IsDominant s`, `IsGenericPoint η₀ Set.univ`, `s (genericPoint S) = η₀` |
| Multipointed model pair, smooth generic curve and etale generic marking | `C₀ : MultipointedCurve S₀`, followed by `Smooth (C₀.x.fiberToSpecResidueField η₀)` and `Etale (C₀.d.fiberToSpecResidueField η₀)` |
| All model sources and morphisms | `Cj₀ : J → MultipointedCurve S₀`, `f₀ : ∀ j, (Cj₀ j).Hom C₀` |
| All model arrows semistable eta0-modifications | For every j, `(f₀ j).IsEtaModification (S₀.fromSpecResidueField η₀)` and `(Cj₀ j).IsSemistable` |
| Selected model arrows stable | `∀ j, j ∈ Jst → (f₀ j).IsStable (S₀.fromSpecResidueField η₀)` |
| Original target pair is its pullback | `eC : C.X ≅ pullback C₀.x s`, `eD : C.D ≅ pullback C₀.d s`, with equalities on second projections for the structure maps and on first projections for the marking inclusion |
| Original sources are their pullbacks | For every j, `eCj,eDj` give the corresponding two isomorphisms and all three structure/inclusion equations |
| Entire diagram is recovered | `eCj.hom ≫ (f₀ j).curveBaseChange s = (f j).curve ≫ eC.hom`, and the analogous marking equation; the target comparisons are shared by every j |
| One common dense open U0 | `∃ U₀ : S₀.Opens, Dense (U₀ : Set S₀) ∧ ...` |
| Isomorphism of each curve and marking over that open | `IsIso (pullback.snd (f₀ j).curve (C₀.x ⁻¹ᵁ U₀).ι)` and `IsIso (pullback.snd (f₀ j).marking (C₀.d ⁻¹ᵁ U₀).ι)` for every j; these are the inverse-image opens in the respective target schemes |
| Every total space reduced | `IsReduced C₀.X ∧ IsReduced C₀.D ∧ (∀ j, IsReduced (Cj₀ j).X ∧ IsReduced (Cj₀ j).D)` |

All 13 original statement dependencies were opened, including their statement,
recorded binding, declaration signature, and docstring. The reused declarations are:

| Dependency | Module; declaration |
| --- | --- |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension; `topologicalKrullDim` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties; `AlgebraicGeometry.IsIntegral` |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation; `AlgebraicGeometry.LocallyOfFinitePresentation` |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth; `AlgebraicGeometry.Smooth` |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion; `AlgebraicGeometry.IsClosedImmersion` |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale; `AlgebraicGeometry.Etale` |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `AlgebraicGeometry.LocallyOfFiniteType`, with `QuasiCompact` |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat; `AlgebraicGeometry.Flat` |
| def-weil-geometric-fibre | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; `pullback`; Mathlib.AlgebraicGeometry.Fiber supplies the ordinary generic fibres |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic; `AdicCompletion` |
| def-weil-pbc-multivariate-power-series | Mathlib.RingTheory.MvPowerSeries.Basic; `MvPowerSeries` |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper; `AlgebraicGeometry.IsProper` |
| def-trf-multipointed-curve (added landed prerequisite) | Sheaf.TraceFormula.MultipointedCurve; `AlgebraicGeometry.MultipointedCurve` |
| def-trf-multipointed-curve-modification (added landed prerequisite) | Sheaf.AlgebraicGeometry.MultipointedCurveModification; `MultipointedCurve.Hom`, `.curveBaseChange`, `.markingBaseChange`, `MultipointedCurve.IsSemistable`, `MultipointedCurve.Hom.IsEtaModification`, `.IsStable` |

The semistable predicate reaches the original completion and power-series dependencies
through `Sheaf.Paper.OrgogozoInductionData`, whose exact scalar-compatible definition
was read. There is no duplicate predicate. Proof dependency modules with bindings are
imported non-publicly. The only proof dependency without a current binding is
lem-trf-stable-modification-stability-field-descent; it is named in the docstring and
its import will be supplied when it is stated. No dependency import cycle was introduced.

Edge cases checked: J empty still supplies the base curve model, normal base, common
dense open, and reducedness of C0 and D0; the reducedness clauses are outside the
universal quantifier over J. Empty markings are allowed by MultipointedCurve and all
marking isomorphism clauses. Empty curves are also allowed by the pure-dimension
predicate's vacuous component condition. Jst may be empty or all of J. The base is
nonempty by IsIntegral. Already-isomorphic modifications are included. No properness
or separatedness of the curves over the base, connectedness, or characteristic
restriction is added. Finite J in Type u loses no finite cardinality; it can always
be reindexed by Fin n. Both characteristic zero and positive characteristic bases
map canonically to the size-lifted Spec Z.

Searches, made with the prescribed tools:

- msearch.py leanfinder: “Finite diagram of semistable multipointed curve modifications
  descends to normal affine finite type scheme”: 8 hits, all affine-transition-limit
  eventual-morphism/equality declarations; none states this diagram model theorem.
- msearch.py leansearch: “Noetherian approximation of stable marked curve modifications”:
  8 hits on IsNoetherian and its constructors/projections; no matching theorem.
- msearch.py loogle: `AlgebraicGeometry.MultipointedCurve, AlgebraicGeometry.IsIntegral`:
  0 hits, unknown project-only identifier MultipointedCurve.
- msearch.py grep: `semistable|multipointed|stable.*modification` in AlgebraicGeometry:
  no Mathlib implementation of this diagram theorem.
- rg in upstream WeilConjectures for semistability, multipointed curves and stable
  modifications, plus the exact item id: no existing declaration for this statement.
- rg in lean/Sheaf finds the landed MultipointedCurve, MultipointedCurveModification,
  SemistableMultipointedPair, MarkedCurveFiniteTypeModel and StableModificationSpreading.
  Their source signatures were read. The first two supply the definitions used;
  the model/spreading theorems have different conclusions (single unmodified pair,
  or valuation-ring quasi-model), not this normal finite-type finite diagram.

No STATEMENT-DISPUTED issue remains. No new definition node or dependency repair
module is needed. H1/H2 are repaired by the module and complete exact-signature binding;
H3 by the explicit clause match above; H8 by source and all-nine-step proof docstrings;
H11 by the careful rereading below. Compile and dry-run evidence is appended below.

## Second reading by NV

Under the current direct-delivery brief no additional agent was started; the maintainer
provides the independent review. This section records the same worker's separate second
pass, not a claim that another worker read the packet. I reopened the complete final
node and final Lean file and compared every row above against the actual term.

That pass found and fixed four defects in the initial scratch signature before delivery:
(1) identity maps had been used for eta-modification; these would force global
isomorphisms and were replaced everywhere by the canonical maps from the residue
fields of the generic points; (2) normality of S0 had been omitted and is now the
explicit stalk condition, identical to the hypothesis on S; (3) the common-open
clause must use the inverse image in each target curve and marking, not the base
open's inclusion as a morphism to a curve; (4) the universal J clause was
parenthesized so the reducedness of the target is still asserted when J is empty.
The unused-Fintype warning was removed by the mathematically exact `[Finite J]`.

I checked that the target isomorphisms are chosen once, that every source comparison
commutes with them on both parts of the arrow, and that all marking inclusions and
structure maps are retained. Model normality, integrality, affineness, finite type,
dominance, generic points, generic smoothness and etaleness, source semistability,
selected stability, the common dense open, and all reducedness clauses are present.
The added prerequisites are already landed, and their exact definitions match the
inline notions in the node. No statement correction is made.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NV
lem-trf-stable-curve-diagram-noetherian-model
<module-file>` compiled the final file in sandbox and its library path, with the
expanded proof imports, cleanly on 2026-10-17. Output: overlay
Sheaf.TraceFormula.StableModificationConstructibility [3.2 s], sandbox
Sheaf/Stage2/Sandbox0.lean [3.9 s], library
Sheaf/TraceFormula/StableCurveDiagramNoetherianModel.lean [40.1 s]. No errors or
warnings. The prescribed 60-second per-file limit was retained.

First dry-run preflight found the signature record included the terminal `:=`;
removed that delimiter to match the preflight signature convention exactly. The
UTC date was taken from `date -u +%F` (2026-10-17) as required by the brief.

Required dry run: `deliver2.py NV lem-trf-stable-curve-diagram-noetherian-model
--no-push` returned `OK (dry run): commit 0b56b974c0 passes the preflight and
compiles; nothing pushed`. It staged exactly the item module, item node, and
this report.
