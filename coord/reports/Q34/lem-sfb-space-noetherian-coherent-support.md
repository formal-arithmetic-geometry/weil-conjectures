## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceNoetherianCoherentSupport` states
`AlgebraicGeometry.AlgebraicSpace.noetherian_coherent_subquotients_closed_support`.
It contains one theorem with proof `sorry`, no definitions and no proved assertions.
The node's mathematical statement, accepted split and proof dependencies are unchanged.
The statement dependencies gain the already landed definition owners
`def-trf-space-module-scheme-restriction` and `def-sfb-space-module-support`, because
this signature names their canonical constructions. No new nodes or dependency repairs.

Hypotheses and clauses, read against the node:

- A scheme S and an algebraic space X over S are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. The arbitrary universe u is explicit.
- Local Noetherianity is exactly
  `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
  Objects T include every representable etale scheme map, with no surjectivity condition.
  The sentence defining Noetherian is a terminology convention; the theorem assumes
  only locally Noetherian, not quasi-compactness or quasi-separatedness.
- Modules are `X.Modules` on the recorded small etale ringed site. Site quasi-coherence
  is the existing `SheafOfModules.IsQuasicoherent` specialized to its structure sheaf.
- Coherence is rendered without a new predicate: site quasi-coherence together with
  `∀ T, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
  ((X.schemeRestriction T).obj F)`. The latter is the actual finite-type-kernel
  coherence predicate exposed by the recorded pqf-def-coherent module, not merely the
  conjunction IsQuasiCoherentFiniteType that used to be its primary interface.
- The structure module is `SheafOfModules.unit X.structureSheaf`. The first conjunction
  says it is quasi-coherent and has coherent restriction on every chart.
- `F N : X.Modules`, `i : N ⟶ F` and `Mono i` encode a submodule inclusion. These range
  over all monomorphisms in the ambient module-sheaf category, not only a chosen
  category of quasi-coherent modules. The hypotheses give exactly coherence of F
  and quasi-coherence of N.
- The next conclusion gives chartwise coherence of N; combined with its assumed
  quasi-coherence this is precisely coherence of N. `IsClosed (moduleSupport N)` is
  its geometric-stalk support closed in the point topology.
- `c : CokernelCofork i` and `IsColimit c` specify F/N by its full categorical
  cokernel universal property. There is no additional existence assumption: the
  conclusion applies to every cokernel representative. It states quasi-coherence,
  every chart's coherence, and `IsClosed (moduleSupport c.pt)` for this quotient.
  This formulation avoids selecting quotient data from an unproved existence.
- The final universally quantified clause specializes to
  `i : I ⟶ SheafOfModules.unit X.structureSheaf` with `Mono i` and
  `I.IsQuasicoherent`. A submodule of the structure module is exactly an ideal
  sheaf, so this quantifies over every quasi-coherent ideal. It states the
  quotient's quasi-coherence, chartwise coherence and closed support, exactly the
  node's last sentence.

Declaration reuse and source reading:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleForget`, `structureSheaf` and `Modules`. Read their full
  definitions and docstrings: representable diagonal, fppf sheaf, surjective etale
  scheme atlas, all etale scheme tests and the regular-functions structure sheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` is the full
  subcategory for Mathlib's `SheafOfModules.IsQuasicoherent`; its slice sheafification
  instances allow the existing predicate in section universe u.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`, lines 36–44 and
  73–75. `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, lines 56–60.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly imports
  `WeilConjectures.AlgebraicGeometry.Coherent`, whose `RingedSpace.IsCoherent`
  is finite type plus finite type kernels of every finite free map on every open.
  Its complete definition and docstring were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`
  is the canonical restriction to open subschemes with its regular-function scalar
  comparison. This is the chart module of the node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport` is the
  existing nonzero-geometric-germ locus, expressed through sections that no etale
  refinement above the point kills. The definition and germ interpretation were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  is the supremum of the coinduced topologies along all etale scheme-source maps.
  Hence `IsClosed` uses exactly the atlas topology of the statement.
- The recorded proof declarations are imported privately:
  `CategoryTheory.siteRestriction_exact` (WeilConjectures.AlgebraicGeometry.SiteRestrictionExact),
  `CategoryTheory.ringedSiteModules` (Sheaf.CategoryTheory.RingedSiteModules),
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`
  (Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence),
  `Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`
  (WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian),
  `Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`
  (WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian),
  `Scheme.Modules.finite_type_module_support_closed`
  (WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed), and
  `AlgebraicSpace.etale_chart_moduleSupport`
  (Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport).
  Their source statements/docstrings were read. The genuine proof-only prerequisite
  lem-sfb-scheme-etale-module-exact-finiteness-comparison has no Lean record yet;
  there is no module to import. It is named in the proof docstring and remains in
  proof_deps. None of its objects is needed to type this statement.

Source checked: `literature/stacks-project/spaces-cohomology.tex`,
lemma-coherent-Noetherian (07UB), lines 1877–1906, and
lemma-coherent-Noetherian-quasi-coherent-sub-quotient (07UD), lines 1935–1955;
`spaces-morphisms.tex`, lemma-support-finite-type (07TZ), lines 2835–2863.
They give precisely structure coherence, coherent quasi-coherent subquotients and
closed finite-type support. The theorem docstring carries all five accepted proof steps.

Edge cases checked before writing: empty X, zero F, N = 0, N = F, the zero ideal,
the unit ideal, and etale charts not surjective over X. Zero modules have empty
support; the zero ideal quotient is O_X and the unit ideal quotient is zero. No
nonemptiness, nonzero, affine, separation, global compactness, or finite-dimensionality
hypothesis was added. The same scheme universe and section universe as the recorded
algebraic-space interface are used, without equating independent site universes.
No false statement or unresolved statement dispute was found.

Searches actually run via msearch.py, group Q34 and this item:

- leanfinder, query "On a locally Noetherian algebraic space a quasi coherent
  submodule of a coherent module and its quotient are coherent and have closed
  support": eight hits, including Module.isClosed_support and the general module
  sheaf predicates; no algebraic-space theorem or one-line exact specialization.
- loogle, query `"IsCoherent", "support"`: zero hits.
- grep, query `[Cc]oherent.*[Ss]upport|[Ss]upport.*[Cc]oherent`: zero hits.
- leansearch, query "Coherent submodules quotients and support on a locally
  Noetherian algebraic space": eight algebraic-module results, no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for coherence and support, and the
  item id: found scheme-only closed-support theorems, algebraic-space support and
  restriction definitions, related ideal-power results and consumers of this item;
  no declaration of this assertion. The same-id search in WeilConjectures finds none.
- rg in dag/lean_names_upstream.json and both source trees for the proposed full
  declaration name found none. No duplicate declaration or definition is introduced.

Validation: scompile.py Q34 lem-sfb-space-noetherian-coherent-support compiled
both the sandbox and library-path forms cleanly (3.4 s and 10.7 s); no errors or
unexpected warnings. All variables are explicitly bound, with autoImplicit false.

## Second reading by Q34

The dispatcher explicitly prohibits starting other agents; this is a separate second
pass by the same worker, not a claim of independent review. The maintainer provides
independent delivery review. Reopened the node, source passages, dependency definitions
and final Lean signature and checked each clause above.

The potentially misleading primary pqf-def-coherent declaration was checked: its current
module publicly exposes RingedSpace.IsCoherent, and the signature uses that exact
predicate, so it does not conflate coherence with quasi-coherent finite type. The
submodule conclusion reuses its quasi-coherence hypothesis and therefore loses no
clause. The quotient conclusion explicitly supplies quasi-coherence, so chart coherence
is not asserted of an uncontrolled module. The final clause quantifies over all ideals
as monomorphisms into the structure module, and over every cokernel representative.
The support and chart restriction definition-owner nodes were added to stmt_deps;
no mathematical correction was required. There are no file-local notations, hidden
instances, let binders, extra hypotheses or auxiliary theorems.
