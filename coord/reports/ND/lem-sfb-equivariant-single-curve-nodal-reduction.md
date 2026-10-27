## Worker report

Stage 2 for `lem-sfb-equivariant-single-curve-nodal-reduction`, ND, 2026-10-22.
The live item is split and reviewed PASS by NF in stage 1, but has no Lean record.
The previous worker's inference that this prevents stage 2 was mistaken: this delivery
states the unchanged reviewed statement; it does not resplit it. The source and proof
are retained verbatim in the node. Only `lean` and additions to `stmt_deps` change.

The main module is `Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction`.
Its sole declaration is
`AlgebraicGeometry.exists_equivariant_single_curve_nodal_reduction`, with proof `sorry`.
The docstring carries all thirteen proof steps and their dependency names.
A second module defines `AlgebraicGeometry.HasQuasiSplitNodalFibres`, with real data
and no postponed theorem. No definition data is chosen from an existence theorem.

The public de Jong primary scan was read at
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf : printed pp.602--603
(Theorem 2.4 and Remark 2.5), 614--615 (Lemmas 5.5 and 5.7 and the preceding
definition), and 617 (one-curve case of Theorem 5.9).
The local PDF is already WANTED in the inherited source record.

### Every input hypothesis

| Node hypothesis | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| The schemes C and Y over k | `(Y C : Scheme.{u})`, structure maps `pY`, `pC` |
| Y integral, projective, geometrically integral | `[IsIntegral Y] [IsHProjective pY] [GeometricallyIntegral pY]` |
| Normal Y | `hnormal`: at every point the stalk is a domain and integrally closed |
| Finite type Y over k | Follows from H-projectivity: `IsHProjective.isProper` and the finite-type parents of properness; no extra hypothesis |
| C integral, proper and finite type over k | `[IsIntegral C] [IsProper pC]`; properness includes locally finite type and gives quasi-compactness |
| Proper dominant g:C→Y over k | `g`, `[IsProper g] [IsDominant g]`, and `hg : g ≫ pY = pC` |
| Geometrically integral generic curve | `[GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y))]` and `hdim` equating its Krull dimension to 1 |
| Finite group H | `(H : Type v) [Group H] [Finite H]`, without faithfulness |
| Compatible actions on k,C,Y,g | Monoid homomorphisms `σk`, `σC`, `σY`; `hC`, `hY` impose semilinearity, and `heq` equivariance of g |
| H-stable nowhere dense closed E | `E : Closeds C`, `hE`, `hEstable` |

Scheme actions are homomorphisms into `Aut`, with the standard composition law.
The scalar action on Spec uses the inverse group element, as required by contravariance.
This is the same semilinear convention as EquivariantCurvePencil and the existing
EquivariantMarkedPlurinodalFieldAlteration modules.

### Every output clause

| Node conclusion | Lean rendering |
| --- | --- |
| Finite extension e/k | Existential field and algebra on `e : Type u` and `Module.Finite k e` |
| Finite group G and surjection α:G→H | Existential `[Group G] [Finite G]`, `α : G →* H`, `Function.Surjective α` |
| G-action on e extending the prescribed k-action | `γ : G →* (e ≃+* e)` and its displayed compatibility on every `z : k` |
| e^ker(α)/k purely inseparable | `K : IntermediateField k e`, membership iff fixed by every element of `α.ker`, and `IsPurelyInseparable k K` |
| Integral V,B, and normal projective geometrically integral finite-type B/e | Existential integral instances; structure map q; `IsHProjective q`, `GeometricallyIntegral q`; the stalkwise normality conjunct. H-projectivity implies finite type |
| B and V carry compatible G-actions over e | `τB`, `τV`, scalar semilinearity of q and equivariance of v; the latter also makes the induced V→Spec e semilinear |
| The square gc=bv | `c ≫ g = v ≫ b` |
| The square is over k | `b ≫ pY = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k e))`; together with hg and the square, this also gives the equation for c |
| Both horizontal maps equivariant via α | The two equations involving `τB,b,σY` and `τV,c,σC` |
| b,c H-projective surjective alterations | Each is H-projective, proper, surjective and dominant; each is finite over an existential dense open of its target; its function-field algebra below is finite |
| Canonical function-field extension k(B)/k(Y) | `hb` identifies the generic points. The existential algebra is constrained by `algebraMap = (stalkSpecializes … ≫ b.stalkMap …).hom`, and is finite |
| Canonical function-field extension k(V)/k(C) | The identical construction using hc and c, with its finite-module condition |
| Their kernel fixed fields are purely inseparable | For each inclusion, an intermediate field has membership exactly when `Scheme.functionFieldAut (τB a.val)` or `Scheme.functionFieldAut (τV a.val)` fixes the element, and is purely inseparable over the original target field |
| v H-projective, flat and finitely presented | `IsHProjective v`, `Flat v`, existential `hfp : LocallyOfFinitePresentation v`. Projectivity supplies quasi-compactness and separatedness, hence quasi-separatedness, so this is finite presentation |
| Nonempty connected nodal geometric curves | `HasNodalGeometricFibres v`: every algebraically closed field-valued fibre is connected (including nonemptiness), has dimension 1, and every nonsmooth point has completed local ring Ω[[u,w]]/(uw) |
| Reduced geometric fibres of pure dimension one | A separate displayed universal conjunction of `IsReduced (pullback v t)` and `(pullback v t).IsPureDimension 1`. These are not silently inferred from the nodal predicate |
| Smooth geometrically integral generic fibre | `Smooth` and `GeometricallyIntegral` on `v.fiberToSpecResidueField (genericPoint B)` |
| Finitely many disjoint smooth sections | `m : ℕ`, `s : Fin m → (B ⟶ V)`, section identities hs, pairwise disjoint ranges, and each range contained in `v.smoothLocus` |
| G-stable union of sections | Image equality for `⋃ j, Set.range (s j)` under every τV(a). No fixed-label assumption |
| G-stable closed nowhere dense D | `D : Closeds B`, `IsNowhereDense`, and image equality under every τB(a) |
| Smooth over B\D | `Smooth` on the restriction of v to the open complement of D |
| Boundary containment | `c ⁻¹' E ⊆ v ⁻¹' D ∪ ⋃ j, Set.range (s j)` |
| Quasi-splitness | `HasQuasiSplitNodalFibres v`, defined in the new node and described below |
| Sections and fibre graphs may be permuted | No pointwise fixing of sections, components, nodes or branches is imposed. The existing strict-split-tower predicate is deliberately not used |
| Arbitrary base-change permanence | Universal quantification over every scheme B' and every morphism a:B'→B. The actual projection `pullback.snd v a` is H-projective and flat, locally finitely presented, has nodal, reduced, pure one-dimensional geometric fibres, and is quasi-split |
| Section permanence for those same sections | The canonical `v.baseChangeSection (s j) (hs j) a` satisfy the section identities, pairwise disjointness, and containment in the actual base-changed smooth locus |
| dim Y=0 | The final implication gives `IsIso q` (B identified with Spec e as an e-scheme) and `(D : Set B) = ∅` |

The function-field algebras and intermediate fields are existential presentations of
canonical objects, not arbitrary replacement inclusions: each algebra map is explicitly
fixed by the generic stalk map, and each intermediate field has exactly the invariant
membership condition. Function-field automorphisms use the published upstream
`Scheme.functionFieldAut`; no duplicate function-field or action construction is introduced.

### Dependency declarations used

All original statement-dependency nodes and their records were read. Their interfaces are:

- `Field` (Mathlib.Algebra.Field.Defs), `Algebra` (Mathlib.Algebra.Algebra.Defs).
- `AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties).
- `AlgebraicGeometry.IsProper`, `IsSeparated`, `UniversallyClosed`
  (Mathlib.AlgebraicGeometry.Morphisms.Proper and its imports).
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`
  (Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact).
- `AlgebraicGeometry.GeometricallyIntegral`
  (Mathlib.AlgebraicGeometry.Geometrically.Integral); the recorded dependency also covers
  geometric irreducibility and geometric reducedness.
- `topologicalKrullDim` (Mathlib.Topology.KrullDimension).
- `AlgebraicGeometry.IsHProjective`
  (WeilConjectures.AlgebraicGeometry.Morphisms.Projective).
- `AlgebraicGeometry.IsFinite` (Mathlib.AlgebraicGeometry.Morphisms.Finite).
- `AlgebraicGeometry.Surjective` (Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap).
- `AlgebraicGeometry.Scheme.functionField` (Mathlib.AlgebraicGeometry.FunctionField,
  publicly imported through the recorded WeilConjectures.AlgebraicGeometry.FunctionField).
  The recorded `functionFieldOfComponents` concerns the general reducible clause; this item
  uses exactly the arbitrary integral-scheme clause of that same node.
- `FieldExtension.degree` (Sheaf.FieldTheory.FieldTower) is the recorded tower node;
  its companion existing `Module.Finite`, `IntermediateField` and `IsPurelyInseparable`
  express the finite and radicial clauses, as that module's docstring specifies.
- `AlgebraicGeometry.Flat` (Mathlib.AlgebraicGeometry.Morphisms.Flat).
- `AlgebraicGeometry.LocallyOfFinitePresentation`
  (Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation).
- `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`
  (Mathlib.AlgebraicGeometry.Morphisms.Smooth).
- `CategoryTheory.Limits.pullback`, `pullback.snd`, `pullback.fst`
  (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback); these provide both fibre-product
  dependency nodes and geometric fibres. No alternate geometric-fibre set is used.
- `AlgebraicGeometry.IsClosedImmersion` is the recorded immersion interface, used inside
  H-projectivity and the normalization module's closed component embeddings.
- `Scheme.reducedNormalization`, `Scheme.fromReducedNormalization`
  (Sheaf.AlgebraicGeometry.ReducedNormalization).
- `AdicCompletion` (Mathlib.RingTheory.AdicCompletion.Basic/Algebra), and
  `MvPowerSeries` (Mathlib.RingTheory.MvPowerSeries.Basic), through the existing nodal predicate.
- Added landed nodes: `def-trf-nodal-geometric-fibres` uses `HasNodalGeometricFibres`
  (Sheaf.AlgebraicGeometry.NodalGeometricFibres); `def-weil-pure-dimension` uses
  `Scheme.IsPureDimension` (Sheaf.AlgebraicGeometry.PureDimension).
- The new quasi-splitness module uses the existing scheme-theoretic fibre projections
  (Mathlib.AlgebraicGeometry.Fiber), residueFieldMap (Mathlib.AlgebraicGeometry.ResidueField),
  reduced normalization, and Smooth. These are its own statement dependencies.
- Canonical ancillary constructions: `Scheme.functionFieldAut`
  (WeilConjectures.AlgebraicGeometry.StalkAut) and `Scheme.Hom.baseChangeSection`
  (WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection). Their source
  signatures, definitions and docstrings were read. The latter is the actual pullback lift.

All twelve distinct recorded modules of stated proof dependencies are imported privately,
including fields excellent, finite-type-localization excellence, projective base change,
projective properness, flat torsion-freeness, H-projective composition, the nodal Fitting locus,
projective-bundle conversion, marked semistable base change, generic finiteness on an open,
projective ample invertibles, and tensor invariant fields. The remaining Mathlib proof
leaves are supplied through those imports. The eight unstated sfb proof prerequisites have
no module to import; none is assumed as a hypothesis of this theorem.

### Edge cases and checks

- Empty E and m=0 are allowed; Fin 0 gives the empty marking. Smooth input curves and an
  empty D are allowed. No stability or genus lower bound is added to the statement.
- C and Y cannot be empty, as required by integrality. B and V are integral. Each geometric
  fibre is nonempty because the reused ConnectedSpace condition includes nonemptiness;
  pure dimension alone would not have supplied that condition.
- The quasi-split definition permits rational self-nodes and reducible nodal fibres.
  Requiring smooth components would be stronger and is not done. The two rational branches
  are the two actual normalization points, not two irreducible components.
- Trivial H, nonfaithful actions, and nontrivial action on k all remain included.
  Characteristic zero and positive characteristic use the same IsPurelyInseparable predicate.
  No separability or algebraic closedness of k is imposed.
- Group universe v is independent of scheme/field universe u; G is in max u v. Finite
  extensions e remain in u. Geometric-fibre tests use the standard Mathlib scheme universe.
- The arbitrary base B' may be empty, disconnected, nonreduced, or map entirely into D.
  The base-change assertion therefore does not demand integrality of the pullback, a smooth
  generic fibre, or nowhere denseness of a pulled-back D. These are not among the properties
  the node says persist under arbitrary base change.
- In dimension zero the implication gives an actual isomorphic structure map B→Spec e,
  together with empty D; hence the smooth-complement assertion makes v smooth everywhere.
- The only proof hole is the named item theorem. The new definition has no hole.

Searches executed with the launcher msearch.py, item/group bound to this delivery:

1. LeanFinder: “Equivariant nodal alteration of a relative curve with finite group action and
   purely inseparable invariant fields”: eight Weierstrass-curve hits, no matching alteration.
2. Loogle: `AlgebraicGeometry.HasNodalGeometricFibres, AlgebraicGeometry.IsHProjective,
   AlgebraicGeometry.IsNormal`: zero hits, unknown identifier for HasNodalGeometricFibres
   in the service's Mathlib-only environment; this is not evidence against the local project
   declaration, which was found and reused.
3. Mathlib grep: `equivariant.*nodal|nodal.*alteration|HasNodalGeometricFibres`
   in AlgebraicGeometry: zero hits.
4. LeanSearch for rational nodes and normalization branches: eight normalization-construction
   hits; no quasi-splitting predicate.
5. LeanFinder for “quasi split nodal curve rational singular points rational normalization
   branches”: eight Weierstrass-curve hits, no exact predicate.
6. Mathlib grep `QuasiSplit|quasi.split|RationalNodal` in AlgebraicGeometry: zero hits.
   The unmodified outputs of searches 4--6 are in the new node's mathlib_searches.
7. Project rg searches in both lean/WeilConjectures and lean/Sheaf found the existing
   nodal predicates, pure dimension, canonical stalk automorphisms, and canonical section
   base change, which are reused. The item id occurs only in the downstream plurinodal
   module's proof docstring, not an existing declaration.
8. DAG search found quasi-splitness only in the item, the downstream plurinodal theorem,
   and the quasi-splitting prerequisite, none a definition node. `blueprint_refs.py search
   quasi-split` returned zero blueprint nodes. The ancestor command reports None, retained
   in the new node's blueprint.from.node.

Validation: scompile.py compiled both delivered modules separately in dependency order,
including private-overlay and library checks. QuasiSplitNodalFibres: 1.6 seconds;
EquivariantSingleCurveNodalReduction: 2.6 seconds. No errors or unexpected warnings.

## New nodes

`def-sfb-quasi-split-nodal-fibres`, module
`Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`: the residue-field fibre's nonsmooth points
are rational and have exactly two rational normalization preimages. Source: the definition
preceding de Jong Lemma 5.7, pp.614--615. The new definition spells out the exact condition
used inline by the downstream plurinodal statement. It reuses its fibre, residue-field and
normalization objects rather than introducing replacements. Searches above and the raw
search records show no existing definition; HasStrictSplitNodalFibres is stronger because
it additionally requires smooth geometrically irreducible components. The item cites this
new node directly; no new theorem node or dependency module is needed.

## Second reading by ND

A separate source-and-signature pass by this worker was made after the clean compile;
this is not claimed to be a second agent's independent review. The current dispatch brief
forbids starting another agent and specifies the maintainer's independent delivery review.
I reread the node, new definition and both full source files. The tables above record every
input and output clause against its exact Lean occurrence. This pass verified in particular
that the function-field algebras are pinned to the canonical generic maps, fixed fields are
those of ker α (not the full group), projectivity is IsHProjective, pure dimension and
reducedness are explicit, and arbitrary base change uses the same sections by the canonical
baseChangeSection. Normal constants, semilinear scalar actions, and dimension-zero empty D
are retained. No statement correction or STATEMENT-DISPUTED flag is needed. No additional
mathematical mismatch was found in this pass.
