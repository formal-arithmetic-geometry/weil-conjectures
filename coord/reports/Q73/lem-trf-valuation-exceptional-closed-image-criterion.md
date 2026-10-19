## Worker report

This stage-2 delivery states `AlgebraicGeometry.Temkin.valuation_exceptional_closed_image_criterion`
in `Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion`. The theorem's entire
proof is `sorry`; its docstring reproduces all six proof steps of the current node. Three
auxiliary definitions give the canonical geometric inclusion, the set B_f, and the
exceptional-point predicate explicitly introduced by this node. They contain real terms,
not postponed data or existence choices. There is no new independent notion or DAG node.

The previous Q81 delivery was a stage-1 split with a reviewed proof plan, not a Lean
statement. The sandbox inherited here contained only launcher metadata. This delivery adds
a new stage-2 `lean` binding and module; it preserves the item's mathematical statement and
proof plan. The only other item change is adding the two already landed definition nodes
`def-trf-multipointed-curve` and `def-trf-multipointed-curve-modification` to `stmt_deps`.

Hypothesis-by-hypothesis comparison:

- The field K is `(K : Type u) [Field K]`; separable closedness is `[IsSepClosed K]`.
- The valuation subring V of K is `(V : ValuationSubring K)`. Its `mem_or_inv_mem'`
  is the stated valuation alternative, including the harmless zero case. Mathlib's
  `IsFractionRing V K` instance makes K its fraction field; this is not an extra hypothesis.
- The prime ideals form a finite chain: `[Finite (PrimeSpectrum V)]` supplies finiteness;
  ideals of a valuation ring are already linearly ordered. No discreteness, rank-one,
  Noetherian or excellence assumption is imposed.
- The base is exactly `Spec (.of V)`. The generic map from Spec K is
  `Spec.map (CommRingCat.ofHom V.toSubring.subtype)`.
- `(X Y : MultipointedCurve (Spec (.of V)))` gives the target and source pairs. The landed
  structure contains both schemes, their structure maps, the compatible closed marking,
  flatness, local finite presentation plus quasi-compactness and quasi-separatedness
  (full finite presentation), and fibrewise pure dimensions 1 and 0. It allows an empty
  marking and imposes neither separatedness nor properness over the base.
- `hX` is `Smooth` of the generic base-changed curve projection; `hD` is `Etale` of the
  generic base-changed marking projection. These are assumptions on the target pair.
- `f : Y.Hom X` gives compatible curve and marking morphisms over the base.
- `hf : f.IsEtaModification (...)` imposes properness on both maps, isomorphisms on
  schematically dense opens and the generic fibres, with sectionwise injectivity expressing
  schematic density. It is the landed definition, not a private copy.
- `hY : Y.IsSemistable` supplies nodal geometric fibres, the étale source marking and its
  containment in the relative smooth locus. The landed definition reuses
  `Orgogozo.IsOrdinaryDoublePoint`: the maximal-ideal completion is the scalar-compatible
  quotient of `MvPowerSeries (Fin 2) Ω` by the product of its two coordinates.

Clause-by-clause comparison of the defined objects and conclusions:

- `f.closedImageFiberGenericPoints` is a set of points z of the source scheme. Its first
  condition is `IsClosed ({f.curve z} : Set X.X)`, so closedness is in the ENTIRE original
  target, without replacing it by a fibre or by a normal target.
- The other condition is `∃ (t : T) (c : Y.x.fiber t),
  c ∈ genericPoints (Y.x.fiber t) ∧ Y.x.fiberι t c = z`.
  Mathlib defines `genericPoints A` by `closure {c} ∈ irreducibleComponents A`; this is
  exactly the node's generic point of an irreducible fibre component, without choosing
  representatives of components or assuming irreducibility of the whole fibre.
- `f.IsExceptionalFiberGenericPoint z` likewise gives t and c. It represents their component
  by a scheme C with `IsReduced C`, a closed immersion `i : C ⟶ Y.x.fiber t`, and
  `Set.range i = closure {c}`. These properties uniquely determine the reduced induced
  component up to its unique isomorphism over the fibre. The existential witnesses describe
  an isomorphism-invariant property, not a chosen or hollow construction.
- Contraction is `(Set.range (i ≫ Y.x.fiberι t ≫ f.curve)).Subsingleton`.
  The component is nonempty because its image is the closure of c, so this is exactly a
  singleton image rather than permitting an empty contracted component.
- Its geometric base change is the actual pullback of `i ≫ Y.x.fiberToSpecResidueField t`
  along `Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
  (AlgebraicClosure (T.residueField t))))`. The existential isomorphism e identifies this
  scheme with `ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t))))`.
  The equation for `e.hom ≫ pullback.snd` makes the isomorphism one over that field.
  This is the geometric base change of the reduced ordinary component, not its
  normalization, not merely geometric rationality, and not just one geometric subcomponent.
- `Y.geometricComponentInclusion t i` is constructed by `pullback.lift`. Its projections
  are the actual component inclusion into Y and the base-changed structure morphism;
  the equality is proved directly from `Y.x.fiber_fac` and `pullback.condition_assoc`.
  No arbitrary replacement of the canonical geometric inclusion is assumed.
- `(Set.range (Y.geometricComponentInclusion t i) ∩ Y.specialPoints t).encard ≤ 2`
  counts distinct points of the component lying in the UNION of geometric marking and
  singular locus of the ambient geometric fibre. The landed `specialPoints` uses
  nonsmooth points, which over the algebraically closed residue field are exactly the
  singular points here. A point that is both marked and singular is counted only once.
- `f.closedImageFiberGenericPoints.Finite` is the entire first conclusion, not just
  finiteness of its exceptional subset.
- The next conjunct is precisely `f.IsStable η ↔
  ∀ z ∈ f.closedImageFiberGenericPoints, ¬ f.IsExceptionalFiberGenericPoint z`.
- The final conjunct explicitly retains the stated particular consequence:
  `¬ f.IsStable η → ∃ z ∈ f.closedImageFiberGenericPoints,
  f.IsExceptionalFiberGenericPoint z`.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (and the recorded `IsSepClosure` companion
  was read); `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring` and its fraction-field
  instance, for the explicitly specified valuation subring of K.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiber_fac`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.Topology.Sober`: `genericPoints`, `IsGenericPoint`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` through the landed pure-dimension
  predicate used in `MultipointedCurve`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, through the landed ordinary-node
  predicate. The recorded signatures and source docstrings for all original `stmt_deps`
  were opened; no dependency interface needed repair.
- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `Hom.IsEtaModification`, `IsSemistable`, `specialPoints`,
  `Hom.IsStable`; this imports the landed scalar-compatible
  `Orgogozo.geometricPoint` and `Orgogozo.IsOrdinaryDoublePoint` interface and the upstream
  `AlgebraicGeometry.ProjectiveLine`.
- The stated Mathlib proof-dependency notions come through
  `Mathlib.AlgebraicGeometry.Noetherian` and the imported finite-type/compactness modules.
  The four Temkin statement-only proof dependencies have no Lean declarations yet, so no
  fictitious imports of them are added. All six proof steps and those node IDs remain in
  the main theorem docstring for stage 3.

Sources and edge cases:

I opened the primary PDF, https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf,
and read §1.2, the definitions and finiteness around Lemma 4.2.2, and all of Lemma 4.4.4.
The proof plan retains its normalization reduction: only the factor g has a normal target;
properness of the original f supplies closedness in the original X. No normality premise is
added to the item. The local archival PDF is still WANTED, as the node already records.
No statement correction or STATEMENT-DISPUTED finding is needed.

Checks before writing included: height zero (V = K), the identity modification, empty
marking, empty curves or fibres, disconnected fibres, and nonseparated or nonproper target
curves. An empty fibre supplies no c and no exceptional witness. The component's nonempty
closure prevents empty-image contraction. One or two geometric special points is exceptional;
three is excluded by `encard ≤ 2`. The definition uses the geometric field, so positive
characteristic and imperfect separably closed fields are retained. Distinct ordinary
components and markings are not collapsed. The source proof may choose the most special
point actually met by a component closure, not necessarily the closed point of all Spec V.
All variables and universes are bound explicitly; `set_option autoImplicit false` enforces
this locally.

Searches made with the required wrapper and direct source reads:

- `msearch.py ... leanfinder` with “A semistable modification of a multipointed curve over
  a finite height valuation ring is stable if and only if no exceptional fibre component
  has closed image in the target”: eight hits, including valuative-criterion existence,
  universally closed maps, closed points and finite global-section algebra results. None
  states this marked-curve criterion or the required exceptional-component condition.
- `msearch.py ... loogle '"semistable"'`: zero hits.
- `msearch.py ... grep 'exceptional.*component|stable.*modification|semistable'`:
  zero Mathlib hits.
- `msearch.py ... leansearch` with “Finitely many closed image fibre component generic
  points detect stability of a semistable marked curve modification”: eight hits. Read
  `genericPoints`, `IsGenericPoint`, `genericPoints.component`, and `genericPoints.finite`;
  reused the exact generic-point notion. No hit states the stability criterion.
- `rg` of semistable/multipointed/the exact item ID in upstream `WeilConjectures`: no
  statement match. Direct source reads of the recorded Mathlib declarations are listed
  above; the exact item ID and proposed declaration names have no upstream match.
- `rg` of multipointed/exceptional/stable in `lean/Sheaf`: found the landed
  multipointed-curve and modification modules, and the parent contraction theorem;
  the latter only cites this item in its proof plan and does not state the criterion.
  The landed underlying-pair variant is an alternative packaging, not this theorem.
- `tools/blueprint_refs.py search 'exceptional component'`: zero blueprint-node matches.
  Reading the DAG found the existing curve/modification definition nodes, both reused.
  Exact-name searches for all four proposed declarations in Mathlib/upstream/project
  declarations found no duplicate.

Validation: each delivered Lean module is checked through `scompile.py`; the module has
only the one expected theorem-level `sorry`. The required `deliver2.py --no-push` dry run
and final push are run after compilation and record checks.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
