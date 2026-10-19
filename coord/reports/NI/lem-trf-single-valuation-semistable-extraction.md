## Worker report

This repairs returned immutable head `8a469de1babc`. The only postponed theorem is
`AlgebraicGeometry.exists_singleValuationSemistableExtraction`, in
`Sheaf.TraceFormula.SingleValuationSemistableExtraction`. Its proof is `sorry`;
all definitions have actual data. The natural-language node is unchanged. Its
`stmt_deps` gains the already published `def-trf-strict-semistable-curve` and
`def-trf-modification`, and its `lean` record lists the complete repaired interface.
The saved node and current shared node differed only in `lean` when compared.
The delivery wrapper rebases the packet on current `newtargets-dag`.

The three return points are repaired as follows:

1. **Residual transcendence was an unconstrained Prop.** That field is removed.
   `valuationRestrictionHom O` is the actual inclusion from
   `O.comap (algebraMap K L)` to `O`, constructed with ring-hom composition and
   codomain restriction. Thus its source is exactly `O ∩ K`, not necessarily V.
   `CenteredValuation.residueMap` is Mathlib's `IsLocalRing.ResidueField.map` of
   this inclusion. `CenteredValuation.residualTrdeg` is `Algebra.trdeg` for the
   algebra induced by this canonical ring hom. The theorem assumes exactly
   `ν.residualTrdeg = (1 : Cardinal.{u})`.
2. **The valuation was not tied to the component generic point.** The record now
   supplies `component_mem`, `component_generic`, and a ring equivalence
   `componentField : C.Y.residueField componentGeneric ≃+* L`.
   `generic_comm` equates the restriction of the specified map along
   `Spec (O → L)` with `Spec componentField.toRingHom` followed by
   `C.Y.fromSpecResidueField componentGeneric`. This controls the scheme morphism
   and its field map, not just the image of the single point. For the reduced
   strict model with smooth generic fibre, the residue field at a component
   generic point is its component function field. A free extension of that field
   is excluded by requiring a ring equivalence.
3. **Nodal charts lacked base-map compatibility.** All local duplicate curve,
   nodal-ring and chart definitions are removed. The module imports the published
   `Sheaf.TraceFormula.StrictSemistableCurve` and uses `StrictSemistableCurve`.
   In that interface `StrictSemistableModel.baseMap` is the coefficient inclusion
   for both the polynomial and quotient nodal algebra. The chart's `over` field
   identifies its composite with the actual structure map. The old unconstrained
   nodal branch can no longer occur.

The complete hypothesis/clause match is:

- K is a field and separably closed: `{K : Type u} [Field K] [IsSepClosed K]`.
- V is a valuation subring of K with fraction field K: `V : ValuationSubring K`.
  Its `mem_or_inv_mem'` is the valuation axiom, and Mathlib already supplies
  `ValuationSubring.IsFractionRing`; the redundant fraction-representation
  hypothesis of the saved packet is removed.
- The prime ideals form a **finite** chain: `[Finite (PrimeSpectrum V)]`.
  Linearity of prime ideals is inherent to a valuation ring. The old `hchain`
  merely asserted comparability and omitted finiteness.
- The base is `Spec (.of V)` and its generic fibre is taken along the actual
  `Spec.map (CommRingCat.ofHom V.subtype) : Spec K ⟶ Spec V`.
  There is no independently selected generic point or unspecified field map.
- C is a flat finitely presented T-curve of pure relative dimension one,
  strictly semistable: `C : StrictSemistableCurve (Spec (.of V))`.
  Its fields are `flat`, `locally_finite_presentation`, `quasi_compact`,
  `quasi_separated`, `pure_relative_dimension_one`, and `chart`.
  Finite presentation is the conjunction of the three presentation/compactness
  fields. No separatedness or properness over T is introduced.
- Smooth generic fibre: `hCη : Smooth (pullback.snd C.structureMap
  (Spec.map (CommRingCat.ofHom V.subtype)))`.
- The component field is L: `{L : Type u} [Field L] [Algebra K L]` and
  `ν.componentField`. The identified component is maximal irreducible by
  `ν.component_mem`; its chosen point is generic by `ν.component_generic`.
- O is a valuation subring of that very field: `ν.O : ValuationSubring L`.
  `ν.extends_base` states that the base coefficients lie in O.
  `valuationBaseHom` is their canonical codomain-restricted inclusion.
  `ν.base_comm` says `ν.map` is a T-morphism for that inclusion.
  In combination with `ν.generic_comm` this also fixes the K-structure on the
  component field. Inverting nonzero V-elements fixes the full K-map.
- `ν.restriction_local` is proof data that the canonical inclusion of `O ∩ K`
  is local. This is intrinsic to restriction of a valuation: an element of
  `O ∩ K` whose image is invertible in O has inverse in K and O, hence in the
  intersection. Conversely units remain units under a ring homomorphism.
  Thus this field excludes no valuation in the node. It is used to construct
  the canonical residue map, rather than assuming an arbitrary residue algebra.
- The given valuation map is specified, not just asserted to exist:
  `ν.map : Spec (.of ν.O) ⟶ C.Y`; `generic_comm` is the prescribed generic map.
- Its centre is the image of O's closed point. Closedness is exactly
  `ν.centre_closed : IsClosed ({ν.map (IsLocalRing.closedPoint ν.O)} : Set C.Y)`.
- Residual transcendence degree one is `hν`, for the actual residue inclusion
  `κ(O ∩ K) → κ(O)` as described above. No free Prop occurs in the record.
- The output C' is again a strict semistable T-curve, bundled by
  `C' : StrictSemistableCurve (Spec (.of V))`.
- `b : C'.Y ⟶ C.Y` is over T by the conclusion
  `C'.structureMap = b ≫ C.structureMap`.
- It is an eta-modification by the published
  `EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) b C.structureMap`.
  `SchemeModification` includes properness, schematic density of U and its
  inverse image, and the isomorphism on that open. `EtaModification` additionally
  requires the **canonical induced** map on the entire generic fibre to be an
  isomorphism. The saved packet's topological density is replaced by the actual
  published schematic density predicate; no arbitrary fibre isomorphism is used.
- The lifted specified map, its centre, the irreducible fibre component and
  uniqueness are precisely `IsGenericValuationCentre ν b`.
  It asserts `lift ≫ b = ν.map`, a generic point z of an irreducible component Z
  of the fibre, and equality of its image with `lift (closedPoint O)`, followed
  by equality of every other lift with this one.
- The relevant fibre is over `C.structureMap (ν.map (closedPoint O))`.
  This corrects another saved-packet mismatch: the node says *its T-fibre*,
  which may be a special or intermediate fibre, not the generic base fibre.

The helpers `valuationRestrictionHom`, `valuationBaseHom`, the two valuation
methods, and `IsGenericValuationCentre` give the data explicitly introduced
inside this node's own statement. They belong to its module and are all listed
in `lean.declarations`, with source and blueprint docstrings. They introduce
no independent mathematical notion requiring another DAG node. There are no
new nodes or repaired dependency modules in this packet.

Dependency declarations read and used:

- `Sheaf.TraceFormula.StrictSemistableCurve`:
  `AlgebraicGeometry.StrictSemistableCurve`, `StrictSemistableChart`,
  `StrictSemistableModel.baseMap` and `strictNodalRing` (through the bundle).
  This imports Mathlib's flatness, finite presentation, quasi-compactness,
  quasi-separatedness, fibres, etaleness, polynomial and quotient rings, and
  the published `Scheme.IsPureDimension`.
- `Sheaf.TraceFormula.Modification`:
  `AlgebraicGeometry.SchemeModification`, `EtaModification`; this uses
  `Sheaf.TraceFormula.SchematicallyDenseOpen.SchematicallyDenseOpen` (declaration
  namespace `AlgebraicGeometry`) and the canonical pullback functor on slices.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`; the field structure on the former is reused.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring`, `comap`,
  `subtype`, its local-ring and fraction-ring instances.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic` (through the valuation import):
  `IsLocalRing.ResidueField.map`, using its full `IsLocalHom` argument.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- Mathlib's `irreducibleComponents`, `IsGenericPoint`, and `Spec` are used
  directly, with their recorded declaration signatures. In particular the
  mathlib-only component dependency needs no invented `lean` record.

Edge cases checked by mathematical inspection:

- If V=K, the generic map is the identity up to the canonical field/subring
  identification; finite prime spectrum includes the one-prime case.
- Restriction of O to K can be an overring/localization of V. The definition
  uses its actual intersection and does not require `O ∩ K = V` or localness
  of `V → O`.
- Empty fibres remain allowed by `IsPureDimension`; an empty curve admits no
  `CenteredValuation`, since its component generic point would be an element.
  No new nonemptiness condition is imposed on other fibres.
- Zero or nonzero nodal parameters are represented by the imported quotient
  chart; the coefficient projection is part of its chart equation in both cases.
- A field larger than the component function field cannot replace L because
  `componentField` must be an equivalence. The valuation map cannot be unrelated
  to that equivalence because `generic_comm` equates the entire maps.
- The generic-centre condition permits a centre over an intermediate prime of V.
- No restriction on residue characteristic, separatedness or properness of C/T
  has been added. Properness is required only for the modification b.

Source checked: the primary PDF
[Temkin, Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
§4.2 (definition using O ∩ K), §4.3, Proposition 4.3.1 and its two-stage proof,
pp. 27--29, opened online during this repair. The imported strict-chart and
modification source modules were read in full. The seven-step proof docstring
now follows the current node's expanded proof, including rational residue
restriction, the two blowup charts, globalization and schematic generic density.
No natural-language node correction or STATEMENT-DISPUTED is needed.

Searches in this repair:

- `msearch.py ... leanfinder "valuation subring residue transcendence degree one
  centred on a curve irreducible component"`: eight hits, consisting of discrete
  valuation ring cotangent-rank theorems, Weierstrass reduction notions, the
  scheme residue-field instance and formally unramified residue fields. None
  gives this extraction statement or a centred component valuation interface.
- `msearch.py ... loogle "ValuationSubring.comap, IsLocalRing.ResidueField.map,
  Algebra.trdeg"`: zero hits for the combined query. Individual declarations
  were located and their source signatures read with rg.
- `msearch.py ... grep "CenteredValuation|StrictSemistableCurve|residualTrdeg"`:
  zero Mathlib hits. Direct rg in the upstream WeilConjectures source and shared
  Sheaf source found the published strict semistable and modification modules,
  which are now reused. No upstream extraction theorem was found.
- Direct rg for `schematicallyDense|SchematicallyDense` found the published
  schematic-density and modification modules. Direct rg for `comap`,
  `ResidueField.map` and `Algebra.trdeg` found the canonical Mathlib operations
  now used. Direct rg for `CenteredValuation|valuationRestrictionHom|
  IsGenericValuationCentre` in both project source trees found no prior match.

Published proof dependencies `WeilConjectures.Blowup.Affine.ChartAlgebra` and
`Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal` are imported without
`public`, as required for postponed proofs. The former was read using
`scompile.py --source` because the old local upstream checkout lacks the file;
the server provides it. The latter was read in the shared source. Other proof
dependencies currently have no recorded Lean module, apart from etaleness which
is already exposed by the strict-curve module. No import cycle is introduced.

## Second reading by NI

Independent maintainer second reading, 2026-10-18, of immutable delivery
03a476007d59be03e587638d216792d7563ed50e. I did not write or previously review
this delivery. This section replaces the author's explicitly labelled self-check;
the Worker report above is preserved.

I read check-brief2.md in full, the packet, the snapshot item and all sixteen
statement dependencies, the delivered module and its seven declarations, and the
published declaration sources used by its imports. The substantive result is PASS.
The landing verdict is FIX solely to supply this independent second reading (H11).

Source: [Temkin, Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf), section 1.2,
the standing assumptions at the start of section 4 (printed p. 24), section 4.2
(printed pp. 26–27), and Proposition 4.3.1 and its proof (printed pp. 27–29).
The paper assumes finite height and a separably closed fraction field, permits
nonseparated curves, defines the residual degree using O intersect K, and constructs
the smooth and then fibre-generic centres. The node retains those hypotheses and
forgets the stronger blowup conclusion. I also read the local Stacks definitions
of Krull dimension, integral schemes, and finite presentation (0055, 01OK, 01TP).

Hypothesis and conclusion audit:

| Node clause | Exact Lean rendering and verdict |
| --- | --- |
| Separably closed field K | `[Field K] [IsSepClosed K]`; correct. |
| Valuation subring V with fraction field K | `V : ValuationSubring K`; its valuation axiom and existing `IsFractionRing` instance supply both requirements. |
| Finite chain of primes | `[Finite (PrimeSpectrum V)]`; prime ideals of a valuation ring are already linearly ordered. |
| T and its specified generic map | `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.subtype)`; canonical coefficient inclusion. |
| Flat finitely presented pure relative dimension one | `StrictSemistableCurve` fields `flat`, `locally_finite_presentation`, `quasi_compact`, `quasi_separated`, and `pure_relative_dimension_one`; correct. Quasi-separatedness belongs to finite presentation. |
| Strict semistability | The recorded bundle's `chart` uses polynomial and quotient nodal algebras. `StrictSemistableChart.over` equates the chart projection with the given structure map, including the nodal coefficient map. |
| Smooth entire generic fibre | `hCη : Smooth (pullback.snd C.structureMap (Spec.map (CommRingCat.ofHom V.subtype)))`; correct projection and map. |
| Actual component and function field | `component_mem`, `component_generic`, and the ring equivalence `componentField` identify L with the residue field at a genuine component generic point. For this reduced model that is its component function field. |
| Valuation on that field | `O : ValuationSubring L`; no arbitrary larger field extension can replace the component field. |
| Specified morphism over T | `extends_base`, the constructed `valuationBaseHom`, and `base_comm`; correct inclusion, not an arbitrary map. |
| Prescribed generic-point morphism | `generic_comm` equates the entire maps from Spec L using `componentField`, rather than only their underlying points. Together with `base_comm`, it fixes the K-structure. |
| Closed centre | `centre_closed` is closedness of the singleton image of `IsLocalRing.closedPoint O`; correct. |
| Restricted valuation and residue inclusion | `O.comap (algebraMap K L)` and `valuationRestrictionHom`; the ring map is composition followed by codomain restriction. |
| Residual transcendence degree one | `residueMap` is `IsLocalRing.ResidueField.map` of that inclusion; `residualTrdeg` uses its `toAlgebra`, and `hν` equates its `Algebra.trdeg` to cardinal one. |
| Strict output and morphism over T | Existential `C' : StrictSemistableCurve (Spec (.of V))`, `b`, and `C'.structureMap = b ≫ C.structureMap`; correct. |
| Eta-modification | Recorded `EtaModification` requires `SchemeModification` and invertibility of the canonical slice-category base change of b. The modification requires properness and schematic density on both opens. |
| Generic centre in its own T-fibre | `IsGenericValuationCentre` chooses z in the fibre over `C.structureMap (ν.map (closedPoint O))`, an irreducible component Z, and `IsGenericPoint z Z`, equating its image with the lifted closed point. |
| Unique lift of the specified map | The same predicate requires `lift ≫ b = ν.map` and equality of every other such lift. Properness and agreement on the generic point justify this uniqueness; no separatedness of C/T is assumed. |

The auxiliary proof field `restriction_local` adds no mathematical condition:
if an element of O intersect K becomes a unit in O, its inverse lies both in K
and O and hence in the intersection. This is exactly locality of the specified
inclusion. It is proof data needed for Mathlib's residue-field map, not an assumed
residue extension or an extraction hypothesis.

All statement dependencies were opened. Their recorded declarations are reused:
`IsSepClosed` (also listed alongside `IsSepClosure` in its node),
`topologicalKrullDim`, `Algebra.trdeg`, `IsIntegral`,
`LocallyOfFinitePresentation`, `Smooth`, `Spec`/`Spec.map`, `Etale`, `Field`,
`Flat`, `irreducibleComponents`, `Polynomial`, `IsProper`,
`Scheme.residueField`/`Scheme.Hom.residueFieldMap`, `StrictSemistableCurve`, and
`SchemeModification`/`EtaModification`. The field and component nodes have
Mathlib matches even without a separate lean record. The imported
`SchematicallyDenseOpen` tests injectivity of restriction on every ambient open;
`Scheme.IsPureDimension` tests component dimensions and permits empty schemes.
No dependency is privately restated in this delivery.

I compared all seven proof-docstring steps with the node's seven steps and read
the proof dependency statements. Step 1 uses the globalization, normality and
horizontal-model nodes; its O intersect K computation and flat generic density
are elementary. Step 2 uses flat going-down and the etale residue-field theorem;
normalizing a polynomial relation proves residue algebraicity. Step 3 uses the
value-group and globalization nodes and the actual affine chart algebra; the
two substitutions give the displayed equations. Step 4 uses etale base change
and composition and the closed-or-generic lifting clause of finite-fibre
valuation domination; normality supplies reducedness. Step 5 checks the
closed-point condition by Zariski's lemma before applying the normalized linear
residue node. Step 6 uses globalization and etale algebras over a field: the
transcendental residue gives the zero model prime, and localization makes every
prime above it minimal. Step 7 uses proper composition, the finite-prime-chain
open generic point and flatness for schematic density, and separatedness of b
for uniqueness. The nonseparated globalization is explicitly delegated to the
recorded globalization node; it is not inferred by silently adding separatedness.
The normality import uses another published strict-chart presentation; its
hypothesis is mathematically equivalent by changing the affine-base
identification and identifying the universal nodal pullback with the quotient
chart. No additional theorem is needed to type the delivered statement.
Only published proof-dependency modules are imported as proof imports; the other
proof nodes have no recorded module and are future proof work, not missing
statement prerequisites.

Edge cases checked: V = K (one prime); arbitrary finite valuation height;
restriction O intersect K strictly larger than V; intermediate as well as special
base fibres; arbitrary residue characteristic; reducible curves with a chosen
component; zero nodal parameters away from the generic singular locus; empty
fibres and empty C (the latter has no centred valuation). All named schemes and
fields live in arbitrary `u`; the residue field of a `Scheme.{u}` point and its
valuation subring are `u`-small. No independent test-object universe is silently
restricted, and there is no finite-type-as-an-algebra condition on L/K.

One-definition searches: I independently searched Mathlib, the upstream
WeilConjectures tree, and the group Sheaf tree for `CenteredValuation`,
`valuationRestrictionHom`, `IsGenericValuationCentre`, `residualTrdeg`, and
extraction/valuation variants. No pre-existing extraction interface was found.
The published chart and modification interfaces are reused. An independent
LeanSearch query for residual-degree-one valuation extraction returned Dedekind
valuations and Weierstrass reduction, not this statement. Loogle's
`ValuationSubring.comap` query returned the existing comap API, which this module
uses. The node also records LeanSearch, LeanFinder and grep searches; the worker
records LeanFinder, Loogle and direct source searches. No duplicate notion is
introduced by the node-owned inclusion maps and centre predicate.

Pilot gates: all definitions contain real data; precisely one theorem has proof
`by sorry`, with no local proof beyond it. Every declaration and the module have
source-place and blueprint docstrings; the theorem carries all seven proof
steps. All variables and universes are bound with autoImplicit disabled. All
Lean lines are at most 100 characters. `lean.statement` is verbatim the complete
theorem signature in the snapshot, and all seven interface declarations appear
in `lean.declarations`. No statement correction or citer audit is needed. The
route-pivot dropped list has empty intersection with stmt_deps and proof_deps;
there is no item route-pivot repair note in the inspected shared ref. No
infinity/dg/model-category machinery or pro-etale replacement is used.

Compiler reproduction, 2026-10-18:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NI
lem-trf-single-valuation-semistable-extraction
snapshot/lean/Sheaf/TraceFormula/SingleValuationSemistableExtraction.lean`
returned exit 0. The sandbox check took 4.7 seconds and the library-path check
5.3 seconds, with no diagnostics, under the wrapper's 60-second per-file limit.
The installed wrapper delegates to the server overlay and wire confirmation;
these are its actual current mechanics, despite the older local-overlay wording
in the brief. I also read the server-resolved
`WeilConjectures.Blowup.Affine.ChartAlgebra` using `scompile.py --source` and
checked `AffineBlowup.chartRing` itself. No global build, direct ssh, repository
edit, live Lean write, delivery or merge command was run. The immutable snapshot
and branch head were not changed.

Finding and repair: H11, the original second-reading section explicitly stated
that it was the author's self-check. This complete independent reading replaces
that section. No mathematical, Lean, dependency-record or statement-field
change is required.
