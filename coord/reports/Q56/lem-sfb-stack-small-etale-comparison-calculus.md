## Worker report

The module `Sheaf.AlgebraicGeometry.StackSmallEtaleComparisonCalculus` states
`CategoryTheory.stack_smallEtale_comparison_calculus`. All theorem proofs are `sorry`.
The supporting definitions have real data or select a uniquely normalized universal
construction. The reviewed mathematical statement is unchanged. Two definition nodes
now own the ambient-universe operations and the canonical stack-space restrictions
and comparisons, as requested by the returned review.

The main theorem and its supporting canonical constructions jointly render the node:

| Informal hypothesis or clause | Lean rendering |
| --- | --- |
| Universe convention; base scheme S | Explicit `universe u v w m`, `S : Scheme.{u}`; independent `BasedCategory.{v,w}`; coefficient universe `max (u+1) v w` |
| Algebraic stack Z/S | `C : BasedCategory.{v,w} (Over S)`, `hC : IsAlgebraicModuliStack C`; its fibred-groupoid proof is `hC.1.1` |
| Big fppf site, structure sheaf, arbitrary module H | Existing `moduliFppfTopology`, `moduliModuleRings C hC.1.1`, and `ringedSiteModules.{max (u+1) v w}`; no quasi-coherence assumption in the general comparison construction or the first three conjuncts |
| Algebraic-space test z:V to Z | `V : AlgebraicSpace S`, `z : BasedFunctor (discreteModuli V.obj.obj) C` |
| H_z(T)=H(z restricted to T) | `stackSpaceEtaleLift` is the inclusion of scheme charts followed by z; `stackSpaceRestriction` is the existing continuous module pushforward along this inclusion, hence literal precomposition on carriers and restrictions. `stackSpaceTestSchemeIso` and `stackSpaceRingMap` identify regular-function scalars, using only the based-functor equality and sectionwise ULift |
| a:V to W and prescribed theta:z => t a | `a : V ⟶ W`, `theta : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t)` |
| Canonical c_(a,theta):a-star H_t to H_z | `stackSpaceComparison_existsUnique` specifies the unique natural transformation by its value on EVERY local tensor `b tensor m`; `stackSpaceComparison` selects that uniquely characterized transformation |
| Restriction induces c, including agreement on scheme charts | `stackSpaceComparisonArrow` is literally theta followed by the target test applied to the compatible scheme-chart arrow. The normalization sends `b tensor m` to `b` times `H.val.map` of precisely this arrow. This applies to arbitrary schemes, not just affine charts |
| Naturality in H | The comparison is a natural transformation `stackSpaceRestriction hC t ⋙ AmbientCoefficients.moduleTensorPullback a ⟶ stackSpaceRestriction hC z`, rather than an unrelated map for each module |
| Identity comparison | First conjunct, with theta's components explicitly prescribed as the canonical identity chart arrows; equality with `stackSpaceTensorId.hom.app` |
| Composition with pasted two-isomorphism | Second conjunct; gamma's components are theta, eta whiskered by a, and the canonical transport `CostructuredArrow.map_comp`. The equality is `tensorComp.hom ≫ c_(ab) = a-star(c_b) ≫ c_a` |
| Canonical pullback identity/composition identifications | `stackSpaceTensorId_existsUnique` and `stackSpaceTensorComp_existsUnique` normalize the unitor by multiplication and the compositor by `c tensor (d tensor m) -> c*a-sharp(d) tensor m`; their definitions choose these uniquely characterized isomorphisms |
| Etale a gives invertibility | Third conjunct, `IsChartwiseEtale a → IsIso ((stackSpaceComparison ...).app H)` |
| Every scheme-test restriction is associated to a quasi-coherent Zariski module | Fourth conjunct's premise quantifies over every `T : Over S` and every test from `schemeSpace T`; it uses Mathlib's exact `IsQuasicoherent` predicate on that small etale restriction. This is the equivalent local-presentation characterization of the associated-etale-sheaf condition, by the scheme Zariski/etale equivalence (Stacks 03DX, 03LC; 0GQC). It does not require big-site quasi-coherence |
| Then H_z is quasi-coherent for all algebraic-space tests | First conclusion of the fourth conjunct, using the SAME Mathlib `IsQuasicoherent` predicate for every V,z |
| Additional flat scheme-test comparison hypothesis | Second conclusion of the fourth conjunct is an implication: for every scheme arrow a, every pair of tests, and every specified theta, `Flat a.left` implies invertibility of its comparison. `stackSpaceSchemeMap` is the Yoneda image of that same scheme arrow |
| Then comparisons are isomorphisms for every flat space map | Consequent quantifies over all V,W,a,z,t,theta, with `MapIsFlat a` from the recorded chart-test definition; no representability by schemes is assumed |
| Canonical groupoid two-isomorphisms | All tests and prescribed two-isomorphisms are quantified; identity and pasted-component formulas apply to these canonical choices without requiring arbitrary presentation arrows to be flat |

Definitions/dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `etaleForget`, `etaleTopology`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the specialization
  to algebraic-space sites of Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`, publicly available through
  the preceding dependency: `BasedFunctor`, `IsFibredInGroupoids`, `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`. Mathlib's based-functor and comma signatures
  were read, including the orientation of `w_obj` and `CostructuredArrow.map_comp`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliFppfTopology`,
  `moduliStructurePresheaf`, `moduliModuleRings`; the section carriers are already
  canonically ULifted, and the new restriction uses exactly those modules.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes Mathlib
  `SheafOfModules.IsQuasicoherent` (only this quasi-coherence clause is used).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale`, used through the scheme/space etale comparison.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: existing `ModuleChart`,
  `moduleChartTarget`, `moduleChartPost`, the original u-sized operations; the new
  ambient node reuses these charts without changing their owning record.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`.
- `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`: the existing
  `CochainUniverseTransport.ring` and `ringFunctor`, used for actual ULift data.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, owned by
  `def-trf-scheme-algebraic-space`, and `IsChartwiseEtale`, owned by
  `def-sfb-space-chartwise-etale-morphism`. Both recorded signatures and docstrings
  were read in full, including the scheme Yoneda sheaf and the universal chart test.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`: `moduleCompositeChart`,
  owned by `def-sfb-space-module-tensor-composition`; its actual two scheme maps
  and their composite triangle are retained unchanged.

The theorem cites the precise definition owners of `schemeSpace`, `moduleCompositeChart`
and `IsChartwiseEtale`, rather than the enlarged-site and flat-base-change theorems.
The canonical coefficient-transport node and the two new definition nodes are also
statement dependencies. A read-only traversal found no path back to the theorem; the ambient node
has a complete 133-node local closure. The inherited CFG closure contains nine
records absent from this read clone; the server preflight checks the current DAG. The helper definition node uses the recorded generic CFG and
2-isomorphism vocabulary from `def-sfb-stable-pointed-moduli-groupoids`.

Proof-only imports are the recorded modules for the scheme Zariski/etale quasi-coherent
comparison, representable-etale scheme tests, etale-cover fibre products, and the etale
module-pushforward/restriction comparison. The proof node
`lem-sfb-fibred-fppf-space-module-comparisons` currently has no Lean record; it is
cited in the proof docstring, with no fictitious import. The delivered module supplies
the canonical restriction/comparison interface required by this item itself, so it
needs no wait on that proof node.

Edge cases checked: the empty space and empty scheme chart; the zero module; identity
arrows and canonical identity two-isomorphisms; nonrepresentable étale maps of spaces (the étale clause uses the existing chartwise
notion, without a scheme-representability assumption); nontrivial stack automorphisms (theta
is retained in the actual restriction arrow); arbitrary nonflat a (no iso claim);
flat a not representable by schemes; H locally quasi-coherent but not quasi-coherent
on the total big site; non-quasi-compact stacks; independent v,w; coefficients bigger
than u. No finite-presentation or finiteness condition was added. The scheme-test
hypotheses quantify over ALL scheme tests and arrows. The comparison formula uses
ALL compatible charts and tensors, not just their global or affine values.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Module sheaves on fibred fppf sites restriction to small
  etale sites and canonical comparison maps"`: eight hits, including
  `SheafOfModules.Presentation.map_π_eq`, `PresheafOfModules.restrictHomEquivOfIsLocallySurjective`,
  and `SheafOfModules.toSheafCompSheafToPresheafIso`; none states the stack comparison
  calculus or flat-space conclusion.
- `msearch.py ... loogle "SheafOfModules.pullback, AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback"`:
  zero hits, with the project-specific algebraic-space name unknown to Loogle. Its
  declaration was found and read directly in the project's source instead.
- `msearch.py ... grep "comparison|pullbackComp" Algebra/Category/ModuleCat/Sheaf`:
  six hits, chiefly Mathlib `SheafOfModules.pullbackComp` and its conjugacy and
  associativity lemmas. These are general ringed-site tensor comparisons, not the
  total-fppf/small-etale stack comparisons or their conditional invertibility.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id, moduli etale restrictions and space comparisons: no existing
  declaration of this item. `StackLqcCoherator` has related scheme-test restriction
  constructions, but is a DOWNSTREAM consumer of this item and cannot be imported;
  it also lacks algebraic-space tests and the theorem being stated. The existing
  scheme tensor identity/composition and `moduleCompositeChart` were reused where
  available. Searches for the new full declaration names found no collision.
- Read Stacks sources at 075D (comparison properties), 076R (algebraic-space module
  comparisons), 0GQC (local quasi-coherence on chart restrictions), and 0762 (flat
  scheme-test compatibility). Read the current blueprint direct-images proof (3)
  in `literature/blueprint/latest/`, not an archived snapshot.

## New nodes

`def-sfb-space-ambient-module-operations` owns
`Sheaf.AlgebraicGeometry.SpaceAmbientModuleOperations` and its 18 listed declarations
in `AlgebraicGeometry.AlgebraicSpace.AmbientCoefficients`. It introduces the independent
ambient coefficient universe via the existing canonical sectionwise ULift transport.
Its real chart data use Q24's `ModuleChart`, chart target and chart postcomposition.
The node explicitly states the chart restriction laws, the full compatible-section
limit model, projection naturality in both variables, existence and uniqueness up to
the unique projection-preserving natural isomorphism, the left-adjoint tensor pullback,
its unit/counit and its local tensor section. Each postponed theorem is a clause of
this definition node and retains its source and complete proof docstring. All definitions
have actual data or select a normalized universal property. No equality of independent
universes is assumed. The original Q24 record is not included in this delivery and
remains byte-identical to live. The former `AlgebraicSpaceAmbientModuleOperations.lean`
path is not delivered, avoiding the conflicting NL path mentioned in the return.

`def-sfb-stack-space-etale-comparisons` owns
`Sheaf.AlgebraicGeometry.StackSpaceEtaleComparisons` and its 17 listed declarations.
It contains the continuous chart lift, canonical underlying-scheme identification,
natural structural ring map, actual module restriction, comparison arrow, and uniquely
local-tensor-normalized comparison. It also owns the normalized identity and composition
isomorphisms, the actual Yoneda scheme map, and the two additive-sheafification slice
instances needed to use the local-presentation quasi-coherence predicate. Its statement
explicitly includes each supporting theorem's mathematical assertion. This follows the
review's advisory: the lqc-coherator consumer can cite the definitions independently of
the comparison-calculus theorem. No consumer node is edited.

Both new nodes are in the item's chapter and unit, carry `import_flags: []`, preserve
the item's blueprint ancestry with the item prepended to `via`, and have full Lean
records, sources and search evidence. There is no new statement correction.

For each new node, `mathlib_searches` records the full output of LeanSearch, LeanFinder,
Mathlib grep, project grep across `lean/WeilConjectures` and `lean/Sheaf`, DAG grep and
`tools/blueprint_refs.py search`. The tool queries distinguish the ambient-universe
small-etale chart-limit construction from generic module operations, and the actual
CFG/small-etale restriction from Zariski open restriction. No existing declaration
or definition node supplies these interfaces. The existing canonical transport,
continuous module pushforward, chart category and composite chart are reused.

## Returned-review repair

H13: Removed the dependency-node override entirely. The delivered ambient operations
have a new module path and a new definition-node owner. In particular, the live Q24
record's module, `ModuleDirectImageModel`, all 18 declarations including `ModuleChart`,
and every other byte remain untouched. No attempt is made to rebind the record to
`AmbientCoefficients`, and no conflicting contents are placed at NL's former path.

H2: Replaced `lem-trf-space-enlarged-etale-ringed-site-model` in the theorem's
`stmt_deps` by `def-trf-scheme-algebraic-space`; replaced
`lem-sfb-space-flat-direct-image-base-change` by
`def-sfb-space-module-tensor-composition`; added
`def-sfb-space-chartwise-etale-morphism`. The corresponding declarations remain the
exact existing `schemeSpace`, `moduleCompositeChart`, and `IsChartwiseEtale`.

Advisory: Moved `stackSpaceRestriction`, `stackSpaceComparison` and their supporting
constructions into the separately owned definition module above. The theorem imports
that module. The main theorem's signature and all previously reviewed formulas are
verbatim unchanged. Only owning imports, source blueprint tags and node records change.

Validation: the final `scompile.py` run passed for all three delivered files with no
errors or unexpected warnings. Server library compile times were 18.4s for
`SpaceAmbientModuleOperations`, 14.3s for `StackSpaceEtaleComparisons`, and 12.1s for
`StackSmallEtaleComparisonCalculus`, each below the unchanged 60s limit. The final
dry run performs per-file compilation and maintainer preflight again.

## Worker verification

The worker re-read the final node and module clause by clause using the table above.
The dispatcher explicitly forbids starting other agents. The maintainer's independent
review remains the delivery's second reading.

The audit found and repaired four interface issues before delivery: the total-site
coefficient universe could not be forced down to u, so a separately owned ambient interface was supplied;
the identity and composition formulas must retain the actual prescribed two-isomorphisms,
so their component equations and canonical transports were written explicitly; the
quasi-coherence predicate must use the existing local-presentation definition, so the
scheme-test condition is expressed through that equivalent condition rather than
requiring big-site quasi-coherence. The étale clause uses `IsChartwiseEtale`, the general algebraic-space notion, rather
than restricting it to representable étale maps. The tensor comparisons and compositors are normalized
on all local tensors, which rules out arbitrary-map or arbitrary-isomorphism substitutions.
The four main conjuncts and every hypothesis in them were read against the node's clauses.
All new supporting theorems have source and natural-language proof docstrings and are
listed in the owning `lean.declarations`; their proofs are `sorry`. No statement is disputed.

Repair audit: Re-read the unchanged theorem against the clause table above and the
independent review's mathematical PASS. Checked that all supporting declarations
have exactly one delivered owner, that the main theorem still includes both arbitrary
identity and pasted two-isomorphism cases, and that no downstream consumer is imported.
The two new definition nodes depend only on definitions and neither depends on this
theorem or the coherator. No statement is disputed.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
