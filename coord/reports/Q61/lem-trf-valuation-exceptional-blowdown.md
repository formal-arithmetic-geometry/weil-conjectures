## Worker report

The delivery states `AlgebraicGeometry.Temkin.valuation_exceptional_blowdown` in
`Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown`. Its only proof is `sorry`.
The public helper `MultipointedCurve.Hom.closedImageFibreGenerics` is the set B_f
introduced by this very node. It is a real set comprehension, with no postponed
proof or chosen data. It is recorded in `lean.declarations`, as permitted for a
helper belonging to the owning notion. No independent definition node is needed.

The TeX statement is unchanged. The only node changes are `lean` and the addition
of the already landed `def-trf-multipointed-curve` and
`def-trf-multipointed-curve-modification` to `stmt_deps`. No dependency module or
statement correction is delivered. No repair note for this item was present.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| K is a separably closed field | `(K : Type u) [Field K] [IsSepClosed K]` |
| V is a valuation subring of K with fraction field K | `(V : ValuationSubring K)`; its inclusion is `V.toSubring.subtype` and Mathlib supplies `IsFractionRing V K` |
| Prime ideals of V form a finite chain | `[Finite (PrimeSpectrum V)]`; comparability is already a property of a valuation subring |
| T = Spec V and eta = Spec K | `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.toSubring.subtype)` |
| X,D and Y,E are multipointed T-curves | `(X Y : MultipointedCurve (Spec (.of V)))`, the landed structure with flat, finitely presented curve and marking, pure fibre dimensions 1 and 0, closed marking, and compatibility |
| Smooth generic X and etale generic D | `hX` and `hD`, on the second projections of the canonical generic pullbacks |
| Compatible morphism of pairs f | `(f : Y.Hom X)` includes both structure-map equations and the marking square |
| f is an eta-modification | `hf : f.IsEtaModification ...`, with properness of both maps, schematic density of the opens and their preimages, and invertibility of both canonical generic maps |
| Source pair semistable | `hY : Y.IsSemistable`, including ordinary completed node rings, etale marking, and marking in the relative smooth locus |
| z generic in a fibre component C_z | `t`, `C`, `hC`, `z`, `hz : IsGenericPoint z C`; the node's ambient point z is `Y.x.fiberι t z` |
| z lies in B_f | The previous row and `hclosed : IsClosed ({f.curve (Y.x.fiberι t z)} : Set X.X)` give exactly B_f membership |
| Closed image in the entire original X | The helper uses `IsClosed ({f.curve y} : Set Q.X)`, not closedness in a fibre |
| f contracts C_z | `hcontract : (f.curve '' (Y.x.fiberι t '' C)).Subsingleton`; C is nonempty by hC, so subsingleton image is exactly a one-point image |
| Geometric C_z is P1 | `hexceptional` supplies a closed immersion from the canonical `ProjectiveLine` over the residue-field algebraic closure, commuting with the scalar structure map; its range is exactly the inverse image of `Y.x.fiberι t '' C` under the geometric fibre projection |
| At most two distinct marking or singular points | `(Set.range i ∩ Y.specialPoints t).encard ≤ 2`, using the landed union of the geometric marking and nonsmooth locus |
| Intermediate multipointed pair and its maps | Existential `Y₁`, `f₁ : Y₁.Hom X`, `h : Y.Hom Y₁` |
| f_1 is a semistable eta-modification | `f₁.IsEtaModification ... ∧ Y₁.IsSemistable` |
| h is an eta-modification | `h.IsEtaModification ...` |
| f_1 h = f as pairs | `h.curve ≫ f₁.curve = f.curve` and `h.marking ≫ f₁.marking = f.marking` |
| h contracts C_z | `(h.curve '' (Y.x.fiberι t '' C)).Subsingleton` |
| Every remaining w maps into B_f1 and the map is bijective | `Set.BijOn h.curve (f.closedImageFibreGenerics \ {Y.x.fiberι t z}) f₁.closedImageFibreGenerics` |
| B_f1 uses unchanged original target | Both `f` and `f₁` have codomain X; the same helper tests closedness in `X.X` |
| Empty marking, nonproper and nonseparated curves allowed | The landed `MultipointedCurve` places no properness or separatedness assumption on the structural curve map and has no nonempty marking assumption |
| Contextual definition of stability | The imported dependency also supplies `Hom.IsStable`; the theorem does not assume or conclude stability, as the node does not ask for either |
| Geometric fibres, Krull dimension, completion, power series | The shared interfaces use `pullback`, `Scheme.IsPureDimension` with topological Krull dimension, and `Orgogozo.IsOrdinaryDoublePoint`, which uses maximal-ideal `AdicCompletion` and `MvPowerSeries (Fin 2)` modulo uv, compatibly with scalars |
| Schematic density | Shared `Hom.IsEtaModification` requires injectivity of the restriction map on sections over every ambient open, both downstairs and upstairs |

The geometric range equality tests the entire inverse image of C, rather than a
single geometric component mapping onto C. In semistable geometric fibres the
reduced closed structure on this set is unique: the closed immersion from P1
therefore says exactly that the geometric reduced component is P1. It neither
assumes descent to P1 over the nonclosed residue field nor chooses an arbitrary
geometric component. Boundary points are counted on the component itself, not
on a normalization. `Set.BijOn` includes MapsTo, InjOn and SurjOn for the actual
map h.curve, without introducing an arbitrary bijection.

Dependency declarations read and reused:

- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `Hom.IsEtaModification`, `IsSemistable`,
  `specialPoints`, the canonical base-change maps, and the contextual `Hom.IsStable`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`; the node also records
  `IsSepClosure`, which is not needed by this theorem.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring` and its
  fraction-ring instance.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, with quasi-compactness and quasi-separatedness
  in the landed multipointed structure.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `smoothLocus`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections; these are scheme-theoretic geometric fibres, not lift sets.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used in the landed
  pure-dimension structure.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; both are reused via
  the shared scalar-compatible `Orgogozo.IsOrdinaryDoublePoint`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveLine`, reused
  from the modification dependency, not a new model of projective space.
- `Field` is Mathlib's class in `Mathlib.Algebra.Field.Defs` (a mathlib leaf).

Proof-only imports are the two recorded and landed proof dependencies
`Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` and
`Sheaf.TraceFormula.ValuationHorizontalCurveModels`, plus
`Mathlib.AlgebraicGeometry.Noetherian` for the two Mathlib proof leaves.
The finite-fibre-domination, projective-preparation, exceptional-local-criterion,
nodal-polar-section and normalized-graph nodes have no `lean` or `mathlib_match`
record at this reading, so there is no corresponding module to import yet.
The theorem docstring preserves all eight proof steps and their dependency ids.
The stable-contraction consumer is not imported, avoiding its dependency cycle.

Edge cases checked before writing:

- Height zero V = K is allowed; eta is then the whole base and hf forces the
  canonical maps to be isomorphisms. A contracted fibre component cannot satisfy
  the hypotheses. No positive-height assumption was introduced.
- Empty Y or an empty selected fibre has no component satisfying hC. Empty X is
  also covered by the structure and compatible morphism. There is no hidden
  nonempty assumption on a curve or a marking.
- Empty marking is allowed; the special-point count then counts only singular
  points. Counts zero, one and two are included.
- Characteristic two and positive characteristic, including separably closed
  imperfect fraction fields, are allowed. No algebraically closed K or perfect
  residue-field assumption has been substituted.
- C is nonempty; the two Subsingleton conclusions really assert contraction to
  a point and do not permit an empty image in this context.
- If B_f is just the selected point, BijOn has empty source and forces B_f1 to
  be empty. No cardinal finiteness assumption on B_f is needed for the statement.
- Nonclosed image points are excluded only from B_f. No assertion that h
  contracts no further component with nonclosed image was added.
- All fields, schemes, algebraic closures and pullbacks use the same arbitrary
  universe u. There is no independent small test universe and no bound on u.

Searches made on this item (full tool results are kept by msearch.py):

- `msearch.py ... leanfinder "Contract an exceptional projective line component
  in a semistable multipointed curve over a valuation ring"`: eight hits about
  minimal Weierstrass models/reduction, no matching curve contraction.
- `msearch.py ... loogle "IsGenericPoint, Set.BijOn"`: zero hits; treated as
  supplementary, not evidence excluding existing general notions.
- `msearch.py ... grep "exceptional|semistable|blowdown" AlgebraicGeometry`:
  zero hits in Mathlib.
- `msearch.py ... leansearch "Generic points of fibre components with closed
  image under a curve modification"`: genericPoints, IsGenericPoint and their
  component API; reused those notions, no existing B_f or blow-down theorem.
- `rg` in upstream `WeilConjectures` and `dag/lean_names_upstream.json` for
  multipointed/semistable/blowdown and the proposed declaration names: no exact
  statement or names. The required grep for the item id upstream had no hit.
- `rg` in `lean/Sheaf` found the landed multipointed/modification declarations
  and the stable-contraction consumer. Their full signatures and docstrings
  were opened; no blow-down theorem or closed-image-set definition was found.
- DAG search found the existing multipointed and modification nodes, which are
  now added to stmt_deps. `python3 tools/blueprint_refs.py search exceptional`
  confirmed the blueprint route; its broad matches contain no existing Lean
  declaration of the single-component blow-down.

Source verification: opened the primary PDF
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf,
pp. 2, 32--33, including the definition preceding Lemma 4.4.5, that lemma and
Proposition 4.4.6's construction. The supplied TeX statement is consistent with
the intended construction. No statement dispute or counterexample was found.

Proof-plan fault for the maintainer/stage 3: the supplied step 6 identifies only
the reduced support of the scheme-theoretic fibre, while the current text of
`lem-trf-valuation-exceptional-local-criterion` explicitly does not substitute
that reduction. Step 7 therefore needs an additional reducedness argument or
review of that criterion interface before it constitutes a proof. This delivery
is a statement, has no such strengthened hypothesis, and does not silently claim
a theorem about reduced support proves the scheme-theoretic fibre condition.

Validation: `scompile.py Q61 lem-trf-valuation-exceptional-blowdown
lean/Sheaf/AlgebraicGeometry/ValuationExceptionalBlowdown.lean` compiled the
sandbox and library module cleanly (21.2 s and 3.5 s respectively); no warnings
or errors. The delivered theorem is intentionally unproved, as stage 2 requires.

## Second reading by Q61

The dispatcher forbids additional agents, and the maintainer supplies the
independent review. This section records the worker's own second pass, not a
claim of independent review. Reopened the target node and final module and
checked each row above against the source. In particular checked that the two
factorization equalities are both present, the intermediate map has the same
original target, schematic density includes source and target, the generic
maps are canonical, geometric P1 is the whole component, at most two uses
encard of a union/intersection, and BijOn is the actual h.curve. No mismatch was
found and no mathematical statement changed. Explicit auto-implicit options and
all universe binders are present; no local notation, private copy, hollow data,
extra theorem, or proof beyond the single required sorry occurs. The proof-plan
interface issue identified above is reported for the independent review.
