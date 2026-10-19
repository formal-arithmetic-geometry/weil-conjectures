## Worker report

Item: `lem-sp-varying-ring-graph-summand`. Module:
`Sheaf.Paper.VaryingRingGraphSummand`, namespace
`AlgebraicGeometry.ProEtale.VaryingRingGraph`. All theorem proofs are `sorry`;
definitions contain constructions, adjunctions, mates, composites, or choices
uniquely characterized by displayed equations. This is a statement delivery.
The item statement, proof, and proof_deps are unchanged. Its added statement dependency now names the definition owner of the reused operations.

Sources read: the item's statement and eight proof steps; Stacks
`etale-cohomology.tex`, 0F4L (`lemma-shriek-into-star-separated-etale`);
`more-etale.tex`, 0F4Y (`lemma-separated-etale-shriek`) and 0GKM
(`lemma-Rf-shriek-for-quasi-finite`); and main-20261015's
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels.
The source deliberately distinguishes presheaf summands from sheaf sections.
The module does too: generators are adjunction-unit sections; there is no
objectwise assertion that sheaf sections equal a direct sum.

Hypotheses and clauses, matched with the declarations:

| Node text | Lean rendering |
| --- | --- |
| Schemes U,T and separated etale finite-type e | `{U T : Scheme.{u}}`, `e : U ⟶ T`, `[Etale e]`, `[IsSeparated e]`, `[LocallyOfFiniteType e]`, `[QuasiCompact e]` in `graph_clopen`, graph construction, and evaluation statement. |
| Compactification e=pj; p proper, j open and qc | `c : Compactification e` supplies `c.Z`, `c.i`, `c.g`, `c.comm : e = c.i ≫ c.g`, and proper/open instances. `[QuasiCompact c.i]` is explicit in the main evaluation and finite clause. Helpers define the same map without needing this extra property. |
| Any inverse sequence of commutative rings | Section binders `C : ℕ → CommRingCat.{u+1}` and `τ : ∀ n, C (n+1) ⟶ C n`. Index n represents source level n+1. There is no flatness, torsion, finiteness, adic, or cartesian-system assumption here. |
| Small pro-etale sites, constant ring sheaves | `ProEt.topology`, `SemilinearProperOpen.coefficients`, `transition`, `ringSystem`; these are the dependency's actual constant sheaves and ring on the vertical sequence site. |
| Strict semilinear sections | `SemilinearProperOpen.Modules C τ X`, definitionally the recorded `SemilinearSections.Systems`; `Derived` is its ordinary unbounded derived category, not diagrams of derived objects. |
| Sheafified lift sums, including their transitions | `sumSite`, `levelCoefficientMap`, `sumCoefficientMap`, `sumRestriction`, `sum`, `sumAdjunction`, `generator`. Coefficient maps come from the sheafification units; their horizontal naturality is `coefficientMap_naturality`. |
| Exact degreewise derived sum extension | `sum_exact`, its three instance projections, and `(sum C τ e).mapDerivedCategory`. The analogous single-ring declarations are `levelSum`, `levelSum_exact`, and its instances. |
| Graph of every lift is clopen | `graph c V t ht` is literally `pullback.lift (𝟙 _) (t ≫ c.i)` with the equation obtained from `ht` and `c.comm`. `graph_clopen` asserts open and closed immersion for every V,t,ht. Fibre products use the published variable-first convention, so the actual product is V times_T c.Z. |
| Given value on graph and zero on complement | `graphMap_existsUnique` specifies both restrictions for every module M, index n, U-site object W and section m. `graphArrow c W` is the compactified graph. The first equation uses the open unit and the normalized restriction identification to read m in j!M; the second equation requires zero after every restriction landing in the complement. |
| Sum maps induce a natural module-system map | `graphMap` selects the unique natural transformation specified by those equations. Its type is `sum ⟶ extension j ⋙ push p` in the actual module-system categories. Thus linearity, site naturality and all semilinear transitions are part of its type. A lift t over an arbitrary T-site object is a U-site object: weakly-etale cancellation against e proves the required condition on t. Hence quantification over W covers every lift in the node. |
| Degreewise graph then derived direct-image comparison | `onHomotopy` is the explicit word: exact-sum localization comparison, degreewise graph map, homotopy-composition comparison, `push.rightDerivedFunctorUnit`, and exact-open localization comparison. `theta_existsUnique` specifies equality to this word at every homotopy representative. `theta` selects that uniquely specified natural transformation. |
| Evaluation is the analogous graph transformation | `levelGraphMap_existsUnique` and `levelTheta_existsUnique` repeat the graph and representative normalizations for one arbitrary ring. `varyingRingGraphSummand` equates the evaluated system theta with `levelTheta (C n)` after the specified `sumEvaluation`, `openEvaluation`, and `pushEvaluation`. The comparisons are invertible by `sumEvaluationInv_isIso`, `openEvaluationInv_isIso`, and `pushEvaluation_isIso`. |
| Finite ring R_n killed by an ell-power | In `finite_normalization`, take `A := C n`; `[CommRing A]`, `[Finite A]`, `[Fact ell.Prime]`, `_hA : ∃ q, ∀ x : A, (ell^q) • x = 0`. The discrete topology binders describe the canonical finite-ring presentation needed by the existing coefficient-realization API; every finite ring admits it. |
| Arbitrary field k of characteristic p>0, ell≠p | `k : Type u`, `[Field k]`, `[CharP k p]`, `_hp : 0 < p`, `_hne : ell ≠ p`. No finite-field hypothesis. |
| U,T,c.Z separated finite type over k; arrows over k | Each has an explicit `.Over (Spec (.of k))`, and separated/locally-finite-type/qc structure morphism instances. The arrows e,c.i,c.g have `.IsOver` instances. These are precisely the over-field conventions of `sk-def-sfb-dc-setting`. |
| Input nu_U*L, bounded constructible finite Tor | `L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat A))`, `_hL : AdjunctionTransfer.etaleProperty A U L.obj`. That predicate is the intersection of recorded bounded constructibility and finite Tor amplitude. `sitePull A U := StrictTower.H A U A (RingHom.id A)` is the actual site inverse image followed by identity-coefficient realization. Every bounded input admits the Plus presentation. |
| Specified sum/site comparison | `siteSumInv` is the inverse adjunction mate of the inverse canonical pullback square `StrictTower.hPullbackInv`, using the etale sum and intrinsic module-sum adjunctions. `siteSumInv_isIso` identifies this particular mate through the localized-site direct-image identity. `siteSumComparison` is its exact derived descent, with the orientation nu_T* sum_et ≅ sum_pro nu_U*. |
| Inverse finite etale normalization through specified support comparison | `finite_normalization` states `siteSumComparison.hom ≫ levelTheta = sitePull.map(normalizedSumComparison.inv) ≫ finiteSupportComparison`. `normalizedSumComparison A k N e c` uses the dependency's graph-normalized `EtaleCompactSupportNormalization`. `finiteSupportComparison` is the literal hR-then-hJ word, with canonical Plus-inclusion comparisons. `hR` derives the underived counit mate `hDirect`; `hJ` is the normalized open mate. Thus these are the proper/open maps specifying `compactSupportSiteComparison.inv`, expressed in intrinsic constant-ring module coordinates. N is the published normalization record with its graph and representative equations, not an unconstrained endpoint isomorphism. |
| No arbitrary-input isomorphism claim | Neither `theta` nor `levelTheta` is declared invertible. Only the evaluation and site comparisons are invertible. The finite equation is asserted precisely on the source input class. |

The localized sum presentation uses an adjunction universal property. Its data
are not selected from a bare existence of some map: `sum` is the standard chosen
left adjoint of the actual localization restriction. The unit is included in
`sumAdjunction` and `generator`. The existing
`SheafOfModules.localizedSystemExtension` is direct-sum extension followed by
module sheafification, with its summand-normalized adjunction. Under the
weakly-etale localization equivalence it has exactly this universal property.
Adjunction uniqueness supplies the unique unit-preserving identification, as
for Mathlib's chosen pullback. All downstream graph equations use this unit,
so the permitted universal-property presentation changes neither the map nor
its normalization. The same applies to `levelSum`. In contrast, `graphMap`,
`levelGraphMap`, `theta`, and `levelTheta` are selected only from explicit
exists-unique characterizations; their data are completely fixed by the
clopen restrictions or representative word.

Dependency declarations read and used (full signatures/docstrings, including
published source through `scompile.py --source` when absent locally):

| Module | Declarations / use |
| --- | --- |
| `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Scheme`, `Scheme.Hom`. |
| `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `IsProper`, `IsSeparated`, `UniversallyClosed`; compactification's proper factor and graph closedness. |
| `Mathlib.AlgebraicGeometry.OpenImmersion` | `IsOpenImmersion`. |
| `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | `LocallyOfFiniteType`; finite type is this and `QuasiCompact`. |
| `Mathlib.AlgebraicGeometry.Morphisms.Etale` | `Etale`; the unramified component is not a new independent hypothesis. |
| `Sheaf.AlgebraicGeometry.UnramifiedMorphism` | Recorded `IsUnramified` dependency imported; no private definition. |
| `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `pullback`, `pullback.lift`, projections and their equations. |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `ProEt.topology`. |
| `Mathlib.CategoryTheory.Sites.ConstantSheaf` | `constantSheaf`, its sheafification adjunction and unit. |
| `Sheaf.CategoryTheory.RingedSiteModules` | `CategoryTheory.ringedSiteModules`, actual `SheafOfModules` encoding. |
| `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` | `SheafOfModules.restrictScalars`; inherited semilinear-system and finite realization scalar actions. |
| `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf` | `SheafOfModules.extensionByZeroPresheaf`, the recorded lift-sum presheaf. |
| `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` | `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`, `localizedSystemAdjunction`; actual sheafified-sum universal property and exactness. |
| `Sheaf.Paper.SemilinearDerivedSections` | `Systems`, `DS`, `evaluation`, `semilinearDerivedSections`, `SemilinearDerivedSectionsData`; original system model and simultaneous derived comparisons. |
| `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral` | `SheafOfModules.localize_ringed_site_morphism_general`; localized direct-image identity underlying the sum/site normalization. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | `CoefficientCompatibility.normalizedSumComparison` and the specified compact-support proper/open mate conventions. |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | `Etale.etaleSupportMapCompatibility`, normalized inverse via `compactSupportComparisonOnHomotopy`. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | Recorded over-field setting/compactification interface; finite clause keeps all three schemes and arrows in that setting. |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | Existing arbitrary-ring `coefficients`, `transition`, `ringSystem`, `Modules`, `Derived`, `push`, `pull`, `extension`, `ordinaryAdj`, `ordinaryOpenAdj`, `J`, `R`, `P`, `adj`, `evalPullInv`, `evalPullInv_isIso`, `evalR_isIso`. The new existing-definition owner def-sp-semilinear-constant-ring-operations is added to stmt_deps; the theorem node is not cited for these definitions. |
| `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations` | `StrictTower.Modules`, `coefficients`, `constantRingIso`, `modulePullback`, `moduleDirectImage`, their exactness and adjunction. |
| `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension` | `StrictTower.moduleJ`, `moduleJAdj`, exactness. |
| `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` | `StrictTower.H`, `hDirect`, `hPullbackInv`, `hPullbackInv_isIso`, `HD`, `hR`, `hJ`; all have canonical section/unit normalizations. |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization` | `Etale.EtaleCompactSupportNormalization`; its sheaf and homotopy equations fix the comparison. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | `AdjunctionTransfer.etaleProperty`, existing bounded-constructible finite-Tor class. |

All recorded statement-dependency modules are public imports. Available recorded
proof-dependency modules are imported without `public` when not already statement
dependencies. No dependency module is replaced. The new definition node
`def-sp-semilinear-constant-ring-operations` registers the existing arbitrary-ring
operations and their normalized evaluation mates. It cites only definition nodes;
a read-only traversal of their statement/proof dependency closure found no path
back to this item. No import of the downstream coefficient-tower shriek
calculus is used.

Edge cases checked by reading the constructions and their types:

- Empty test schemes, empty source, and no lifts: the lift sum is zero; the
  graph/complement characterization is meaningful and yields zero when required.
- Zero ring, zero module, and exponent q=0: permitted; the latter forces the
  zero ring. Every map is its unique zero map in these cases.
- Identity maps and open immersions: the units fix the single-lift normalization;
  no hypothesis forces a nonempty scheme or nontrivial coefficient ring.
- Index n=0 is the first positive source level. No predecessor, inverse transition,
  flatness, or surjectivity is used. Arbitrary nonflat quotient transitions remain.
- Arbitrary unbounded complexes of strict systems are allowed by `onHomotopy`
  and `theta`; no evaluation-faithfulness assumption is used.
- Proper factors need not be finite; the graph is closed because proper implies
  separated, and open because it lies in the etale open part.
- In the finite clause k need not be finite; only positive characteristic and
  ell different from it occur. Boundedness comes from the existing input predicate.
- Site object universe is u+1, morphism universe u, module/ring universe u+1,
  and derived localization size u+2. No equality of site universes is imposed.

Searches actually run:

- `msearch.py ... leanfinder "graph sections etale sum extension to compact support varying ring semilinear module sections"`: eight unrelated smooth/section results; no exact statement.
- `msearch.py ... leansearch "etale sum extension graph section compactification derived comparison semilinear rings"`: eight generic etale-ring results; no exact statement.
- `msearch.py ... loogle "SheafOfModules.extensionByZeroPresheaf"`: tool returned zero hits and `unknown identifier`; this is a Loogle catalogue limitation, not evidence that the published project definition is absent. Read and used that declaration through `scompile.py --source`.
- `msearch.py ... grep "etale.*(graph|sum)|graph.*extension" AlgebraicGeometry`: zero Mathlib hits.
- `rg` of item id, graphSummand, varyingRing in upstream `WeilConjectures` and shared `lean/Sheaf`: no exact statement. The older `EtaleGraphSectionExtensionMap` and its linear variant are etale-site, finite-map statements; they do not give arbitrary-ring semilinear compactification maps. The downstream coefficient-tower calculus refers to this item and cannot be a prerequisite.
- `tools/lean_names_upstream.py show lem-sp-varying-ring-graph-summand`: printed catalogue metadata, no exact recorded declaration for this item. Upstream item-id grep likewise yielded no exact theorem.
- Read-only DAG search found the already-landed arbitrary-ring proper/open mate module, so its operations were reused rather than copied.

One new existing-definition node and no dependency modules. No `STATEMENT-DISPUTED` issue found.
The only item field delta beyond `lean` is the authorized addition of this
new definition node to `stmt_deps`.

Validation: `scompile.py` typechecked the sandbox and actual module paths; after
elaboration repairs, only a long-docstring warning remained and was wrapped.
The final dry run below recompiles the final file and performs server preflight.

## Second reading by NB

Performed a separate rereading of the node, the full Lean file, and the source
normalization definitions. The dispatch brief explicitly prohibits starting
another agent; this is a self-rereading, and the maintainer's independent review
remains independent. No independent second worker is claimed.

The rereading checked every row above, in particular the distinction between
lift-sum generators and sheaf sections, graph zero-extension versus arbitrary
maps between the same functors, ordinary derived systems versus diagrams in
separate derived categories, and the orientation of both finite comparisons.
An initial draft incorrectly attempted to use the proper inverse-image/direct-
image adjunction unit on a source-side module. This was removed: the delivered
ordinary map is uniquely characterized by the two clopen-gluing restrictions.
The single-ring map uses that same characterization, not an unrelated adjunction
choice. The rereading also found that an evaluation equation alone should not
leave the direct-image comparison without an invertibility assertion;
`pushEvaluation_isIso` now supplies that assertion for the specified mate.

The main theorem explicitly includes qc of the chosen open immersion. The finite
clause has the over-field structure on U,T,c.Z and on e,c.i,c.g, finite ring,
ell-power exponent, characteristic, and the exact existing input predicate.
The compact-support comparison was opened: `hR` is the derived underived counit
mate, `hJ` is the normalized open mate, and the Plus compatibility arrows in
`finiteSupportComparison` have the required orientations. Its final equation
uses `normalizedSumComparison.inv`. No inverse of the arbitrary-input theta is
asserted. All existential selections of graph or derived maps are exists-unique
with complete normalization equations, and every postponement is a named theorem
with a source and proof docstring. All 66 public declarations are recorded.

## New nodes

`def-sp-semilinear-constant-ring-operations` registers, with
`existing: true`, 42 published declarations in
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. Its main declaration is
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.Modules`. The node specifies
the constant ring sheaves and transitions, their ring on the vertical sequence
site, strict semilinear module systems, ordinary unbounded derived categories,
actual ringed-site direct image, its adjoint pullback, open extension, their
derived operations and adjunctions, and the section-normalized evaluation mates.
The source is main-20261015, `det-sp-tower-gluing`, Local pairs and Levels,
with the arbitrary-ring specialization from Zheng 4.1/4.10 and Stacks
03D7, 03DI, 03EK and 07A4. LeanSearch and LeanFinder each returned eight generic
module/etale results; Mathlib grep returned zero hits. The node stores the full
tool output. Upstream/project grep found the exact published definitions in
that module. DAG and blueprint searches found generic semilinear interfaces,
not this concrete constant-ring specialization: `def-coef-semilinear-system-models`
owns generic Systems/DS, while `def-coef-semilinear-geometry-base`,
`-derived` and `-ops` own abstract geometric interfaces. The new node
cites those actual generic system definitions and other definition owners,
including `def-cbc-strict-constant-tower-operations` for its evaluation targets.
It introduces no Lean definition, module, postponed proof, or arbitrary map.

## Returned H2 repaired

The immutable returned head was `4720c777bda7`. The prescribed initial dry
run of the saved packet passed preflight and compilation at `a7a03cfc56`;
it did not address the maintainer's mathematical ownership return. The retained
Lean module is unchanged. Replaced the saved packet's added theorem dependency
`lem-sf-semilinear-proper-open-mate-pasting` with
`def-sp-semilinear-constant-ring-operations` and supplied the new definition
node above. None of its operations is chosen from or depends on the pasting
theorem. The item's statement/proof/proof_deps and the base's 18 statement
dependencies are unchanged.

Self-check of the repair: read the published coefficient, system, ordinary
operation, derived-operation and evaluation definitions and their docstrings.
Every declaration in the new lean.declarations exists in that module; the
recorded Modules signature is copied verbatim. Every definition-node citation
in the new TeX is present exactly once in stmt_deps; all cited nodes exist and
are definitions. Their dependency closure has no path back to this item.
Rechecked the evaluation mate arrows with explicit scheme subscripts and
composition symbols, so both sides have the same source and target. The
ordinary evaluation/direct-image comparison is the identity on component
sections; evalPullInv is its adjunction transpose; evalP is its exact
localization inverse; evalR is the specified derived mate. The generic
Systems/DS definitions are reused, not duplicated. Arbitrary ring transitions,
the zero ring, n=0, empty schemes, and unbounded complexes remain allowed.
This self-check is by the author; no independent second worker is claimed,
as the dispatch brief prohibits starting another agent.
