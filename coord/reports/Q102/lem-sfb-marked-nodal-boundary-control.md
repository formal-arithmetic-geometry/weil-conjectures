## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedNodalBoundaryControl` states
`AlgebraicGeometry.exists_markedNodalBoundary_control`, with its proof `sorry`, and defines
`AlgebraicGeometry.markedNodalBoundary` by an actual set union. The helper belongs to the
explicit construction requested by this node; it introduces no independent notion or DAG node.
Only the item's `lean` field is changed. No statement correction or dependency repair is needed.

I read the item, all statement-dependency statements and their recorded signatures/docstrings,
the stage-2 brief and conventions, and the current blueprint unit and direct-image statement.
The unit is the six-functor preservation statement, not this auxiliary geometric lemma.
The primary source is de Jong, *Families of curves and alterations* (1997), Remark 2.5,
printed p.603, https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf (publisher scan).
The node's eight-step proof is reproduced in the theorem docstring, with dependency ids.

### Hypotheses, clause by clause

| Node hypothesis | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| V and integral B | `(V B : Scheme.{u}) [IsIntegral B]` |
| Specified finite-type k-structure on B | `(pB : B ⟶ Spec (.of k)) [LocallyOfFiniteType pB] [QuasiCompact pB]` |
| Generic point eta | `genericPoint B`, the canonical generic point of an integral scheme |
| H-projective v | `(v : V ⟶ B) [IsHProjective v]` |
| Flat v | `[Flat v]` |
| Finitely presented v | `[LocallyOfFinitePresentation v]`; quasi-compactness and quasi-separatedness follow from `[IsHProjective v]` via the existing properness instance; thus finite presentation is fully imposed |
| Nonempty connected nodal geometric fibres, dimension one | `hnodal : HasNodalGeometricFibres v`; this recorded definition uses `ConnectedSpace` (including nonemptiness), dimension 1, and the completed local nodal ring |
| Reduced geometric fibres of pure dimension one | `hfibres`, for every algebraically closed `Ω : Type u` and `t : Spec (.of Ω) ⟶ B`, imposes `IsReduced (pullback v t) ∧ (pullback v t).IsPureDimension 1` |
| Smooth geometrically integral generic fibre | The two instances `Smooth` and `GeometricallyIntegral` on `v.fiberToSpecResidueField (genericPoint B)` |
| Quasi-split fibres | `hquasi : HasQuasiSplitNodalFibres v`, using the landed rational-node and rational-normalization-branch predicate |
| n markings, allowing zero | `(n : ℕ) (s : Fin n → (B ⟶ V))` |
| Section identities | `hs : ∀ i, s i ≫ v = 𝟙 B` |
| Disjoint markings | `hdisjoint : Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))` |
| Markings in relative smooth locus | `hsmooth : ∀ i, Set.range (s i) ⊆ (v.smoothLocus : Set V)` |
| Finite group, not necessarily faithful | `(G : Type w) [Group G] [Finite G]`, with no injectivity requirement |
| Actions on k, V, B | `σk : G →* (k ≃+* k)`, `σV : G →* Aut V`, `σB : G →* Aut B` |
| Compatibility, allowing semilinear field action | `hsemilinear` on `pB` and `hequiv` on `v`; together these give the corresponding semilinear equation on the induced structure map `v ≫ pB` of V. `σk g⁻¹` follows the existing scheme-action convention for the contravariant Spec functor |
| Union of markings preserved | `hmarkings`, equality of the image of the union of section ranges with that union, without requiring individual sections fixed |
| Closed G-stable boundary | `Z : Closeds V`, `hstable` gives invariance under every group element |
| Generic boundary contained in marked points | `hgeneric : (Z : Set V) ∩ v ⁻¹' {genericPoint B} ⊆ ⋃ i, {s i (genericPoint B)}`; the fibre's underlying space is canonically homeomorphic to the inverse image of eta, so this is exactly the set-theoretic generic-fibre assertion |

The item's final terminology paragraph defines notions for the surrounding alteration context.
It does not additionally assume that B is normal/projective, that the action is faithful, or
that any alteration is supplied. The theorem introduces none of those hypotheses. Likewise,
its reference to stable pointed curves does not assume the stability/genus inequalities here.
The recorded stable-pointed definition is imported and read, but not substituted for the
weaker marked nodal hypotheses of this lemma.

### Conclusions, clause by clause

| Node conclusion | Lean rendering |
| --- | --- |
| A closed exceptional D exists | `∃ D : Closeds B` |
| The specified choice, not an arbitrary enlargement | `(D : Set B) = markedNodalBoundary v (Z : Set V) G σB` |
| Image of nonsmooth locus | `v '' (v.smoothLocus : Set V)ᶜ` in the helper |
| Images of all components of Z not dominating B | The helper indexes `C : Set Z` with `C ∈ irreducibleComponents Z` and `¬ Dense (v '' (Subtype.val '' C))`; it takes their ambient images `v '' (Subtype.val '' C)` |
| All translates, including the original images | Outer `⋃ g : G, (σB g).hom '' (...)`; the identity element supplies the original set |
| Nowhere dense | `IsNowhereDense (D : Set B)` |
| G-stable | `∀ g, (σB g).hom '' (D : Set B) = (D : Set B)` |
| Smooth over B minus D | `Smooth (v ∣_ D.compl)` |
| Boundary containment | `(Z : Set V) ⊆ v ⁻¹' (D : Set B) ∪ ⋃ i, Set.range (s i)` |
| Every dominating boundary component lies in markings | The universal component clause with `Dense (v '' (Subtype.val '' C))` concludes `Subtype.val '' C ⊆ ⋃ i, Set.range (s i)` |
| Dimension-zero chosen boundary empty | `topologicalKrullDim B = 0 → (D : Set B) = ∅` |
| Every base change, without dominance/integrality restrictions | `∀ (B' : Scheme.{u}) (b : B' ⟶ B), ...` |
| Pulled-back H-projectivity and flatness | `IsHProjective (pullback.snd v b) ∧ Flat (pullback.snd v b)` |
| Pulled-back finite presentation | `QuasiCompact` and `QuasiSeparated`, followed by `∃ hfp' : LocallyOfFinitePresentation (pullback.snd v b)`; the witness provides the instance needed by the nodal and smooth-locus predicates |
| Nonempty connected reduced nodal pure-dimensional geometric fibres persist | `HasNodalGeometricFibres (pullback.snd v b)` and the universal algebraically closed fibre clause imposing reducedness and `IsPureDimension 1` |
| Quasi-split fibres persist | `HasQuasiSplitNodalFibres (pullback.snd v b)` |
| Actual pulled-back markings | `v.baseChangeSection (s i) (hs i) b`, the existing canonical pullback-lift construction |
| Both section equations pull back | Equalities after composing this section with `pullback.snd v b` and with `pullback.fst v b`, respectively `𝟙 B'` and `b ≫ s i` |
| New markings disjoint and in relative smooth locus | `Pairwise ... Disjoint ...` on the canonical new section ranges, and their containment in `(pullback.snd v b).smoothLocus` |
| Marking-image pullback used in boundary control | `(pullback.fst v b) ⁻¹' (⋃ i, Set.range (s i)) = ⋃ i, Set.range (v.baseChangeSection (s i) (hs i) b)`, the identity explicitly explained in node proof Step 8 |
| Boundary containment pulls back | Inverse image of Z under `pullback.fst` is contained in the inverse image of `b ⁻¹' D` under `pullback.snd`, union the canonical new section ranges |
| Smoothness over inverse image of B minus D | `Smooth ((pullback.snd v b) ∣_ (b ⁻¹ᵁ D.compl))` |
| No density or generic-fibre assertion after arbitrary base change | No `IsNowhereDense (b ⁻¹' D)`, no assumption on b being dominant, and no generic smoothness or geometric-integrality assertion about B' appears |

### Dependency declarations used

All statement-dependency interfaces were read in their source. The following table records
module and declaration (transitive public imports also expose their existing definitions).

| Dependency node(s) | Module / declaration |
| --- | --- |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` / `AlgebraicGeometry.IsHProjective` |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension` / `topologicalKrullDim` |
| def-pc-fibre-product, def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` / `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; scheme instances and residue-field fibres are supplied by the existing imports |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs` / `Algebra`; the generic residue-field and Spec field structures use the existing field-extension API |
| def-pc-field-tower | `Sheaf.FieldTheory.FieldTower` / `FieldExtension.degree`; contextual terminology, no added degree hypothesis |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral` / `AlgebraicGeometry.GeometricallyIntegral` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties` / `AlgebraicGeometry.IsIntegral` |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` / `AlgebraicGeometry.LocallyOfFinitePresentation` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth` / `AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus` |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField` / `Scheme.functionFieldOfComponents`; contextual terminology, generic fibre uses the existing generic point and residue field |
| def-sfb-quasi-split-nodal-fibres | `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres` / `AlgebraicGeometry.HasQuasiSplitNodalFibres` |
| def-sfb-stable-pointed-curve | `Sheaf.AlgebraicGeometry.StablePointedCurve` / `AlgebraicGeometry.IsStablePointedCurve`; contextual convention only, stability not assumed |
| def-trf-nodal-geometric-fibres | `Sheaf.AlgebraicGeometry.NodalGeometricFibres` / `AlgebraicGeometry.HasNodalGeometricFibres` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`; used inside the recorded H-projectivity construction and proof plan |
| def-weil-field | `Mathlib.Algebra.Field.Defs` / `Field` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite` / `AlgebraicGeometry.IsFinite`; contextual alteration terminology only |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `AlgebraicGeometry.LocallyOfFiniteType`, together with `QuasiCompact` |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat` / `AlgebraicGeometry.Flat` |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Basic` / `AdicCompletion`, used by the recorded nodal predicate |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic` / `MvPowerSeries`, used by the recorded nodal predicate |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `AlgebraicGeometry.IsProper`, supplied by H-projectivity |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension` / `AlgebraicGeometry.Scheme.IsPureDimension` |
| def-weil-surjective-morphism | `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` / `AlgebraicGeometry.Surjective`; contextual alteration terminology only |

Canonical markings use
`WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection` /
`AlgebraicGeometry.Scheme.Hom.baseChangeSection`; its complete construction and both
projection equations were read, and no second definition is introduced.

Recorded proof-dependency modules are imported non-publicly where they are not already public
statement imports: `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`
(`projective_base_change`), `Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres`
(`HasQuasiSplitNodalFibres.baseChange`), `Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange`
(`pointwise_flatness_base_change`), `Mathlib.AlgebraicGeometry.Noetherian` and
`Mathlib.Topology.NoetherianSpace`. Sobriety and separated sections' closed immersions are in
the already imported Properties and separated-morphism closure. Projective properness and
smooth base change are already in the public ProjectiveSpace/Proper/Smooth imports.
The proof-only node `lem-sfb-flat-space-smooth-locus` has no recorded Lean or Mathlib match;
there is no module of it to import at this stage. The theorem uses Mathlib's actual relative
`smoothLocus`; the missing proof-only statement is not used as data or an extra hypothesis.

### Edge cases and semantic checks

- `n = 0`: `Fin 0` is empty, all marking unions are empty, and pairwise/smooth-marking
  hypotheses are vacuous. `hgeneric` says the generic boundary is empty; all boundary
  components are vertical, giving exactly the required containment over D.
- `Z = ∅`: the component index set is empty. The helper is the finite union of translates of
  the nonsmooth image, as required; it does not incorrectly force D empty if singular fibres
  occur elsewhere.
- `dim B = 0`: integrality makes B nonempty, irreducible and T0; a distinct point would give a
  strict length-one irreducible chain. Thus the unique generic point is the whole space and
  the chosen set D, missing it, is empty. This includes the zero-marking case.
- Empty `B'`: no nonemptiness or integrality hypothesis is imposed on B'; geometric-point
  tests are vacuous, the unique new sections have empty ranges, and the smooth restriction
  over the empty open is allowed.
- A map b factoring through D: the new smooth open is empty. The theorem imposes no
  nowhere-density of `b ⁻¹' D` and no generic smoothness condition on the new family.
- Identity b: canonical pullback sections and both equations, image equality, and containment
  recover the original properties through the canonical pullback isomorphism.
- Trivial/nonfaithful finite G: no faithfulness is assumed. All translates are explicitly
  indexed by G, including its identity. Semilinear ground-field actions are permitted by
  the Spec equation and equivariance; perfectness is not assumed in any characteristic.
- Geometric test fields live in `Type u`, matching the recorded nodal definition and the
  scheme universe. There is no independently smaller field universe that could make tests
  vacuous. The group universe `w` is independent and unrestricted.
- The irreducible components in the helper and horizontal conclusion are components of the
  topological subspace Z itself, mapped to V. Components of V that merely meet Z would be
  incorrect here, and are not used.
- Domination is expressed by density of the actual component image. Properness makes the
  image closed, so nondominating images avoid the unique generic point, exactly as the node
  proof requires. No chosen component list or opaque closed set replaces this construction.

No STATEMENT-DISPUTED issue was found. The source's marked-boundary assertion agrees with
the node. The additional explicit smooth-locus construction and permanence clauses follow
the node's given expansion, with no target/unit statement changed.

### Searches

All remote searches used the prescribed `msearch.py Q102 lem-sfb-marked-nodal-boundary-control`.
The wrapper's exact search records are in the sandbox `searches.jsonl`.

- LeanFinder: `Invariant nowhere dense boundary for marked nodal curves and arbitrary base change`.
  Eight hits, mainly Weierstrass base-change nonsingularity and general immersion/unramified
  results; no marked-family invariant boundary theorem or its explicit construction.
- Loogle: `AlgebraicGeometry.Scheme.Hom.smoothLocus, AlgebraicGeometry.IsHProjective`.
  Zero hits; the public search index does not know the project's `IsHProjective`.
- Mathlib grep: `marked.*nodal.*boundary|nodal.*boundary.*control`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `Invariant boundary control for a marked nodal curve under arbitrary base change`.
  Eight hits, including `AlgebraicGeometry.isSmooth_isStableUnderBaseChange`,
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange` and Weierstrass results;
  these give individual permanence tools, not the node's statement.
- `rg` over both live source roots with `nodal.*[Bb]oundary|markedNodalBoundary|marked_nodal_boundary`:
  nearby trace-formula local nodal-boundary lemmas, no matching marked family theorem.
  `rg` for `lem-sfb-marked-nodal-boundary-control` in `lean/WeilConjectures`: no declaration.
  Broader source search found the already recorded single-curve reduction, marked
  plurinodal alteration, nodal and quasi-split predicates, and canonical base-changed
  sections, all read and reused where applicable rather than restated.

### Validation

Every compile uses `scompile.py`, never a local or global build. The first compiler run
identified one missing scheme-category annotation in a set's pullback carrier. It was
repaired with `(C := Scheme.{u})`; no hypothesis or conclusion changed. All binders and
universes are explicit and `autoImplicit` is disabled. The only postponed theorem is the
item's named theorem; the boundary helper has complete data. No theorem has been proved.

The corrected file passed `scompile.py` both as `Sheaf.Stage2.Sandbox0` and under its
actual library module name, with no errors or unexpected warnings. The helper and theorem
are compiled together in their owning single file. The wrappers retain the default per-file
limit; the library-run wall time includes server slot/dependency handling.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
