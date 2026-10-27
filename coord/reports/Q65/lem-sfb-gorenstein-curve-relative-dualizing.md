## Worker report

Q65 states `AlgebraicGeometry.exists_nodalRelativeDualizingSystem` in
`Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing`. Its only postponed theorem
is that declaration, with proof `by sorry`. Its docstring records the node's six-step
proof, including affine LCI descent, Koszul exactness, normalized polynomial duality,
determinant gluing, base-change transport and the injective-target Serre argument.
The node statement, proof and proof dependencies are unchanged.

The three auxiliary declarations belong to this node's conclusion: they package its
actual adjunction, compute its value on the structure module, and describe the full
relative dualizing system. They neither assume the result nor choose data using a
postponed existence proof. The only `def`, `NodalRelativeDualizingAdjunction.complex`,
is the literal application of the supplied right adjoint to O[0], followed by the
full-subcategory inclusion. All structure fields are explicit data or propositions.
Three existing-definition nodes attach the reused cartesian-square carrier and the
normalized adjunction/fundamental-class predicates; no declaration is copied or moved.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Schemes X and T, a morphism f | `{X T : Scheme.{u}} (f : X ⟶ T)` |
| Proper | `[IsProper f]` |
| Flat | `[Flat f]` |
| Finite presentation | `[LocallyOfFinitePresentation f]`; properness supplies quasi-compactness and separatedness, hence quasi-separatedness |
| Every geometric fibre | `hfibres : ∀ y : T, ...`, using the actual pullback along `Spec.map (algebraMap κ(y) (AlgebraicClosure κ(y))) ≫ T.fromSpecResidueField y` |
| Nonempty fibre | `Nonempty ↥(pullback ...)`; this asserts nonemptiness of the underlying space, not of a category or a collection of maps |
| Reduced fibre | `IsReduced (pullback ...)` |
| Pure dimension one | `(pullback ...).IsPureDimension 1`, the recorded componentwise Krull-dimension predicate |
| At worst nodal | At every `x ∉ (pullback.snd ...).smoothLocus`, `Nonempty (AdicCompletion (IsLocalRing.maximalIdeal ...) ... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))` |
| Existence of f^! on derived QCoh | For every `B : FlatLCIBaseChange f`, `adjoint B` has a preservation witness, a functor `D_QCoh(B.S') ⥤ D_QCoh(B.X')`, and an actual `Adjunction` with the restriction of the existing `schemeDerivedDirectImage B.p'` |
| Actual relative dualizing complex | `(adjoint B).complex` is exactly that right adjoint applied to the degree-zero structure module O, with its QCoh witness |
| omega = H^-1(f^! O) | `homologyIso B` identifies `omega B` with that cohomology sheaf in the shared sheaf-of-modules category |
| Invertible | `invertible B : (omega B).IsInvertible`; `quasicoherent B` makes explicit the node's QCoh clause |
| Canonical complex identification K = omega[1] | `complexIso B`, using a single object in degree zero and shift `(1 : ℤ)`; `complex_normalization B` requires its induced H^-1 map, after the standard shift and single-functor identifications, to equal `(homologyIso B).inv`. Thus an arbitrary scalar on the complex comparison is excluded |
| Every a:T' → T and its cartesian family | `FlatLCIBaseChange f` retains the two schemes, structure map, maps to X and T, and `IsPullback`; no LCI or Noetherian hypothesis is part of this record. It includes the identity square and every chosen pullback square |
| Canonical b*omega = omega' | `baseChange B D g b hc hg hb` is an actual module isomorphism for each cartesian arrow of base-changed families. `localIso` identifies this same omega with each chart determinant; `adjunction_normalization` fixes its transitions and base-change orientations; `fundamental_normalization` requires the cofactor/Jacobian class in those comparisons. `differential_normalization` then fixes the effect on `1 ⊗ da`; `baseChange_unique` states uniqueness |
| Compatibility with composition | `identity` equals the already recorded section-normalized `tensorPullbackSectionId`; `composition` uses precisely `tensorPullbackSectionComp h g` and the pullback of the first comparison |
| Compatibility with isomorphisms of families | The same `baseChange` quantifies over arbitrary cartesian source/base squares with commuting maps to the original family. Taking an identity base map and an isomorphism of sources gives every family isomorphism; the same identity and composition laws apply |
| Smooth-locus identification with relative differentials | `fundamental B : B.p'.relativeDifferentials ⟶ omega B` is an auxiliary way of specifying this canonical identification. `smooth B U` says its restriction is an isomorphism on every smooth open U, in particular on the relative smooth locus. `fundamental_normalization` requires the already-landed `IsCurveFundamentalClass` in this very system: the conormal-first wedge and augmented Jacobian are evaluated using `localIso`, with `flatLCICurveFundamentalSign c = 1`. This fixes the identification with differentials. Smooth invertibility alone is no longer used as a normalization |
| Restriction to a fibre is its Serre module | `serre` quantifies over every field k and every B with base isomorphic to Spec k, including every residue-field fibre. It gives `Hom(F,omega B) ≃ Hom_k(H^1(F),k)` for every QCoh F and explicitly states contravariant naturality for every module map. `scalarCohomology` is the recorded O-module cohomology with scalars restricted along the structural k-map |
| No Noetherian, generic smoothness, irreducibility, stability or genus hypothesis | None occurs. There is also no connectedness, marking, projectivity or pre-existing dualizing-line hypothesis |

The global `[∀ Y : Scheme.{u}, HasDerivedCategory.{w} ...]` chooses localizations only;
it does not identify u and w or impose a geometric finiteness condition. The shared
carrier is `SheafOfModules.{u} (moduleRings Y.toRingedSpace)`, not a second derived
category with the separately bundled `Y.Modules` category instance.

The fundamental differential is normalized relative to actual local comparisons of this
same omega with the conormal determinant. In `adjunction_normalization` and
`fundamental_normalization`, the structure literals use exactly this system's `omega`,
`invertible`, `localIso`, `baseChange`, `identity` and `composition` fields. They do not
quantify over an unrelated line or unrelated comparisons. The former requires the
kernel-first exact-cone transition formula (including its rank sign) and the actual
pullback orientation formula. The latter requires the conormal-first cofactor wedge and
its scalar augmented-Jacobian expression relative to those very local comparisons.
Thus rescaling the fundamental maps while fixing the chart identifications fails the
cofactor equation on the smooth open. A change of the line's trivialization must also
change its normalized chart identifications, and the resulting comparison is the
canonical one expressed in those trivializations. The previous report's claim that
smooth invertibility alone removed arbitrary rescalings was incorrect; this repair adds
the missing chart normalization explicitly. After that normalization, density of the
smooth open supplies the uniqueness of the displayed line comparisons.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections;
  both fibre-product definition nodes record this same universal construction.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion` and its ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (publicly available through the
  reused FlatLCI module): `tensorPullback`, `tensorPullbackSectionId`,
  `tensorPullbackSectionComp`; these are the dependency's recorded normalized interface.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- New existing-definition node `def-sfb-flat-lci-base-change`:
  `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, `FlatLCIBaseChange` and `.identity`.
  This replaces the inappropriate theorem-node citation.
- New existing-definition node `def-sfb-flat-lci-adjunction-system`:
  the same module, `FlatLCIPresentation`, its real conormal/differential/line constructions,
  the normalized refinement and pullback maps, `FlatLCIAdjunctionSystem` and `.IsNormalized`.
- New existing-definition node `def-sfb-lci-curve-fundamental-class`:
  `Sheaf.AlgebraicGeometry.LCICurveFundamentalClass`, `flatLCICurveFundamentalSign`,
  `IsCurveCofactorMap`, `IsCurveJacobianMap`, and `IsCurveFundamentalClass`.
  No Noetherian existence theorem is assumed or chosen from.
- Added already-landed node `def-a1-relative-differentials-pullback-map`:
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`,
  `Scheme.Hom.relativeDifferentialsPullbackGenerator`. This retains the actual tensor
  section, avoiding an arbitrary differential comparison.
- Added already-landed node `def-sc-field-linear-module-cohomology-operations`:
  `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`,
  `Scheme.Modules.scalarCohomology` and its underlying `RingedSpace.moduleCohomology`.

The added definition nodes depend only on foundational definitions; a source-only
dependency traversal checked they do not reach this item through either dependency kind
(108, 150 and 167 nodes in the respective closures).
All their existing declarations are reused, not copied. All recorded proof-dependency modules have
ordinary, non-public imports, apart from modules already publicly imported for the
statement. `lem-sfb-proper-flat-dualizing-polynomial-model` now has its landed declaration in
`Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel`. The final current-main
self-check found this change since the saved packet and added its ordinary proof import. No missing statement notion is left implicit.

### Edge cases checked before writing

- Empty base: fibre hypotheses are vacuous and every cartesian total space is empty;
  the zero structure module is invertible in the stated local definition. No excluded case.
- Nonempty base with an empty fibre fails exactly the `Nonempty` conjunct.
- A disjoint union of nodal curves is allowed. `HasNodalGeometricFibres` was deliberately
  not used because its connectedness clause would improperly strengthen the hypothesis.
- Smooth curves, including genus zero and one, satisfy the nodal implication vacuously;
  the smooth comparison has the correct Omega^1 and shift +1.
- Nodes, reducible fibres and self-nodes use two power-series variables and the ideal (uv),
  with no characteristic restriction, including characteristic two.
- Dimension-zero or mixed-dimensional fibres fail pure dimension one.
- Arbitrary, possibly nonflat and non-Noetherian, changes of base are quantified by the
  cartesian-square record. There is no smooth-generic-fibre or fixed-genus condition.
- Identity changes of base and arbitrary isomorphic cartesian families have explicit
  comparison laws, not merely existence of unrelated isomorphisms.
- Serre duality is tested over every field, not only algebraically closed ones. The zero
  QCoh module and all maps between QCoh modules are included in the naturality equation.
- Derived shifts use cohomological convention H^-1(omega[1])=omega. The normalization
  equation uses Mathlib's shiftIso with 1 + (-1) = 0 and its single-functor homology iso.

### Searches

The prescribed `msearch.py` searches were run for Q65 and this item; their exact
service responses are recorded in the sandbox `searches.jsonl`.

- LeanFinder: "A proper flat finitely presented nodal curve family has an invertible
  relative dualizing sheaf compatible with arbitrary base change": eight hits, principally
  Flat/Smooth base-change permanence, no relative dualizing theorem.
- LeanFinder: "Gorenstein relative curve dualizing invertible base change": eight hits,
  Weierstrass base change and smoothness permanence, no match.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsInvertible, CategoryTheory.Adjunction`:
  no hits; the service does not index the project-specific invertibility declaration.
- Loogle: `"Adjunction"`: twelve hits, including the existing `CategoryTheory.Adjunction`;
  reused for the actual right-adjoint data, not a relative-duality theorem.
- LeanSearch: "relative dualizing sheaf Gorenstein nodal curve": eight unrelated
  differentials-presheaf and Weierstrass declarations, no match.
- Mathlib grep: `dualizing|Gorenstein` in AlgebraicGeometry: zero hits.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf` for relative dualizing,
  nodal dualizing, Gorenstein curves and the item id: the NodalDualizingDatum gives
  an lci/Jacobian datum, the FlatLCI canonical-adjunction theorem assumes a Noetherian
  base, and connected nodal-family declarations impose connectedness. None states this
  arbitrary-base right-adjoint, base-change and Serre assertion. Existing ingredients
  were opened and reused. Exact new declaration-name searches found no collision.
- `tools/blueprint_refs.py search 'relative dualizing'`: three matches, all the
  pro-etale/etale six-functor dualizing complex with constant coefficient rings, not
  coherent O-module duality of a nodal family. No duplicate of this statement.

No STATEMENT-DISPUTED flag or source correction is needed.

### Validation

The saved packet first passed the required `deliver2.py --no-push` mechanical check.
The repaired module is checked with `scompile.py` in both sandbox and library module mode,
and the final packet with `deliver2.py --no-push`. Only the final theorem uses `sorry`. No `lake build`, global build, direct Git command or live-file edit
was run.

## Second reading by Q65

This is the worker's explicit self-check, not a claim of an independent second agent:
the dispatcher brief prohibits starting other agents and assigns independent review to
the maintainer after delivery. I reread the whole node and the generated module, matching
every hypothesis and clause in the table above. This caught the need to distinguish
`Nonempty ↥(pullback ...)` from nonemptiness of data, to reuse the shared module category,
to cover all smooth opens without assuming finite presentation as an extra supplied
field, and to normalize both the shifted-complex isomorphism and base-change comparisons.
Those issues were corrected before delivery. The proper-flat polynomial-model prerequisite is now a required ordinary proof import;
no hypothesis has been substituted for its conclusion.

## Repair of returned head 64d042017e88

H2: replaced `lem-trf-flat-lci-canonical-adjunction` in the delivery's statement dependencies
by `def-sfb-flat-lci-base-change`. It records the existing structure and its identity in
`Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, without relocating either. The two
additional definition nodes below similarly cite the normalized-system and cofactor
predicates as definitions, rather than using their owning theorem nodes. Current main
has no Lean attachment for the item. Its statement, proof, proof dependencies and other
fields are retained from current main; only `lean` and the permitted statement-dependency
additions differ.

H3: added `localIso`, `adjunction_normalization` and `fundamental_normalization`. This is
an actual change to the conclusion's data, not an unchanged re-push. The first supplies
every presentation's comparison to this same omega; the next two apply the existing
normalization predicates to the structure literal built from this same omega and its
base-change maps. The fixed comparison sends the specified dual-conormal tensor volume
orientation to the chart generator. Its fundamental map must give the conormal-first
cofactor wedge, equivalently the augmented Jacobian in that orientation. All previously
reviewed clauses are retained. For c=0 the empty conormal wedge gives the ordinary
relative differential, which immediately detects an attempted nontrivial unit rescaling
with fixed comparisons. For a node uv=0 the two generator images are the corresponding
cofactors; density of the smooth open fixes the line comparison. These checks include
characteristic two and disconnected fibres, without a Noetherian restriction.

## New nodes

`def-sfb-flat-lci-base-change` records the cartesian square carrier and its identity
as existing declarations. Source: Stacks duality Tag 0E2Y. It imposes no flat/lci
hypothesis despite the historical name. The generic cartesian-square definition alone
does not carry this chosen family together with its maps to the fixed original family.
The exact record was previously listed only under a theorem node, hence this definition
attachment is needed by H2. LeanSearch/LeanFinder/Loogle/Mathlib grep found no substitute;
source/DAG grep locates the exact existing definitions which this node now reuses.

`def-sfb-flat-lci-adjunction-system` records the supplied normalized conormal-determinant
system, including its local polynomial presentations, exact-cone determinant transition
normalization and pullback-orientation normalization. Sources: duality Tags 0B6V, 0BQZ,
0E2Y; determinant Tags 0FJX, 0FJY and 0FJM. Its statement spells out all data and the
kernel-first rank sign. It asserts no existence. Search finds these definitions in the
already-landed FlatLCI module, only attached to its existence theorem, so this node is
existing:true on those declarations. It adds no second implementation.

`def-sfb-lci-curve-fundamental-class` records the existing cofactor/Jacobian predicates
and `IsCurveFundamentalClass` of a supplied system. Source: duality Tags 0E9Y--0E9Z.
The definition has no Noetherian binder; that binder belongs only to the owning module's
existence theorem, which is not used here. The scalar trivialization is fixed by the
actual adjunction orientation. The node includes local restriction on differential
generators, the smooth-stalk criterion and arbitrary-base-change normalization. Searches
locate the exact existing definitions under the theorem node and no definition-node
attachment. All three new nodes record the prescribed search responses in mathlib_searches.

### Second reading of the repair by Q65

I reopened the item and all three definition nodes beside the repaired module. The two
structure literals are identical field by field and use the original `baseChange` maps,
so the chart normalization cannot accidentally constrain a separate system. I expanded
the reused predicate: it demands both the wedge and Jacobian formulas for every chart,
with its scalar trivialization taking the actual orientation image to one, and includes
cartesian arrows with identity base map. The normalized-system predicate also constrains
all transition and pullback comparisons. I checked the empty-open/rank-zero conventions,
the +1 sign under the rank-corrected convention, and the universal quantifiers on bases.
The original proper/flat/finite-presentation and fibre hypotheses, actual right adjoint,
H^-1 and shift normalization, smooth opens, base-change coherence/uniqueness and field
Serre naturality are unchanged. No data definition or extra theorem proof is postponed.

The repaired normalizations are witnesses in the conclusion, not extra hypotheses on
f: the theorem still accepts exactly f, properness, flatness, local finite presentation
and the original geometric-fibre condition. The local Koszul/determinant construction
in proof steps 3--5 supplies these normalized comparisons and cofactor maps over the
same arbitrary bases. No Noetherian existence theorem is invoked as an assumption.

The repaired packet passed preflight and compilation (dry-run commit 7a71d4d35cb).
After that check, the final proof-dependency source audit found the newly landed
`ProperFlatDualizingPolynomialModel` module and added its required non-public import.
The final dry run and delivery below validate that import as well. The preflight's
current new-node schema requires `import_flags: []`; all three new definition nodes
include it. No live source or launcher-tool file was edited.
