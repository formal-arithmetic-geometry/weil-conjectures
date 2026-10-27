## Worker report

Stage 2, Q84, 2026-10-23. The current node has no Lean record. The old stage-1
live-wins refusal is inapplicable: coord/brief-stage2.md §0 expressly permits this
stage-2 handoff after Q137's reviewed split. The accepted statement and proof are
preserved. No source statement correction or disputed statement is needed.

Read Stacks spaces-cohomology.tex, lemma-power-ideal-kills-sheaf (07UK), including
its affine-atlas proof, and lemma-coherent-Noetherian-quasi-coherent-sub-quotient
(07UD). The main module states coherent_support_ideal_power, with proof sorry.

Hypotheses and clauses, individually:
- S : Scheme.{u} is the base scheme and X : AlgebraicSpace S is the specified space.
- hln quantifies over EVERY object T of X.EtaleSite and asserts IsLocallyNoetherian
  of its underlying scheme: exactly locally Noetherian on etale scheme charts.
- hqc : CompactSpace (Point X.obj.obj) is quasi-compactness in the existing final
  atlas topology. hqs says every fibre product of two affine scheme tests mapping
  to X is quasi-compact. This is absolute quasi-separatedness, the usual affine-test
  criterion for the diagonal (and the established AlgebraicSpaceCoherentFilteredUnion
  interface); it does not impose quasi-separatedness relative to an arbitrary base S.
- F : X.Modules is a module on the specified small etale structure sheaf.
  hFqc is the recorded Mathlib IsQuasicoherent predicate. hFcoh asserts the recorded
  RingedSpace.IsCoherent on every schemeRestriction T, exactly the node's definition
  of coherence on a locally Noetherian space. No finite-presentation replacement.
- Z : AlgebraicSpace S and i : Z ⟶ X introduce the closed subspace. hi uses the
  recorded IsRepresentableWith and scheme IsClosedImmersion for EVERY scheme base
  change. No reducedness, irreducibility or nonemptiness hypothesis is introduced.
  The node's explanations of those unused notions are not extra assumptions.
- closedIdealSections i V is the intersection of kernels of the specified chart
  scalar maps. The canonical direct image is a limit with these projections, so
  this is precisely ker(O_X -> i_* O_Z), not an arbitrary ideal or arbitrary map.
- closedIdealPowerFamily starts at the full ambient submodule; the successor is
  the intersection of all subsheaves containing ideal-section products. Thus it is
  the LOCALLY generated product, rather than an incorrect sectionwise-image sheaf.
  closedIdealPowerModule packages that actual section data and its named sheaf proof.
- The first universally quantified conjunct says, for every natural n including zero,
  closedIdealPowerModule i F n is quasi-coherent and every chart restriction coherent.
- The second conjunct at each n says exactly the same of closedIdealPowerQuotient,
  the cokernel of the actual inclusion transported through smallModuleEquivalence.
- The left side of the iff says: for every chart T and ordinary point x with nonzero
  stalk of F restricted to T, schemePointMap T.obj.hom x lies in pointImage i.hom.hom.
  This is precisely Supp(F) contained in |i|(|Z|). For quasi-coherent modules, the
  geometric stalk is faithfully flat scalar extension of the ordinary chart stalk,
  hence has the same vanishing; every space point has an etale chart lift. Therefore
  quantifying over all charts is equivalent to the geometric-support condition,
  and neither requires surjectivity of an individual chart nor strengthens support.
- The right side is ∃ n : ℕ, IsZero (closedIdealPowerModule i F n), exactly an
  arbitrary nonnegative killing exponent, with no positivity restriction.

Dependencies read and used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  EtaleSite, etaleForget, structureSheaf and Modules, with their source docstrings.
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its slice
  instances; the actual predicate is SheafOfModules.IsQuasicoherent from Mathlib.
- pqf-def-coherent's primary record CoherentFiniteType defines the conjunction of
  quasi-coherence and finite type; its existing upstream audit also records the
  actual coherent predicate. We use WeilConjectures.AlgebraicGeometry.Coherent,
  RingedSpace.IsCoherent, whose full finite-type-and-finite-type-kernels definition
  was read. CoherentFiniteType is imported to retain the recorded dependency module.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointImage and final topology;
  AlgebraicSpacePointClasses: Point and schemePointMap.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion, specialized
  via the already recorded IsRepresentableWith, with no duplicate predicate.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: ModuleChart,
  moduleChartScalar, ModuleDirectImageModel, its projections and isLimit;
  moduleDirectImage and its canonical chart-limit construction.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: schemeRestriction, the
  actual open-restriction functor and canonical ring comparison. Added its existing
  definition node to stmt_deps to record its use.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: smallModuleRestriction and
  smallModuleEquivalence, preserving the original module-section universe u.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules; Mathlib SheafOfModules.

Available proof dependency modules are imported non-publicly:
SchemeZariskiEtaleQuasiCoherentEquivalence (scheme_zariski_etale_quasiCoherent_equivalence),
WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
(ideal_times_quasiCoherent_affine_sections),
WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
(coherent_support_power_ideal_kills), AlgebraicSpaceFibreProductsEtaleCovers
(fibreProduct_isAlgebraicSpace and the cover/base-change clauses), and Mathlib
Morphisms.QuasiSeparated for the affine quasi-separatedness instance. The unstated
space-ideal correspondence, exact-finiteness comparison, coherent-support subquotients,
affine-atlas existence and chart-support theorem have no module to import yet. They
are proof dependencies, not missing objects needed to type this statement.

Edge cases: at n=0 the submodule is F and the quotient is zero; no positive-exponent
binder excludes this case. Empty X or F=0 admits exponent zero. Empty Z has unit ideal,
so the equivalence reduces to F=0. For Z=X the ideal is zero and exponent one kills F.
A nonreduced closed immersion uses its full kernel, so no radical replaces its ideal.
Non-quasi-compact charts are allowed; no chart is required to be affine in hFcoh/hln.
All universes and binders are explicit; autoImplicit is disabled in both modules.

Searches actually run (recorded in searches.jsonl):
- LeanFinder: "Support of coherent sheaf on a Noetherian algebraic space contained in
  closed subspace if and only if ideal power kills the sheaf" returned 8 scheme ideal
  support/basic-open results, not this algebraic-space statement.
- Loogle: "support", "annihilator" returned Module.annihilator_le_of_mem_support,
  Module.mem_support_iff_exists_annihilator and Module.supportDim_eq_ringKrullDim_quotient_annihilator;
  these are affine-module facts only.
- msearch grep: closedIdealPower|AlgebraicSpace.*support|ideal.*[Pp]roduct under
  AlgebraicGeometry returned only Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean.
- LeanSearch: "Ideal power filtration of a sheaf of modules on an algebraic space as
  the subsheaf locally generated by products with a defining ideal" returned
  Ideal.Filtration, stableFiltration and related affine-module declarations (8 hits).
- rg on lean/WeilConjectures and lean/Sheaf for closedIdealPower, closedIdealProduct,
  closedIdealSections gave no existing algebraic-space construction. Source-id grep
  likewise found no upstream declaration of this node. Broad geometric-stalk searches
  found coefficient etale/Weil sheaf APIs, not this structure-module construction.
- DAG keyword searches found the consumer filtration lemmas, not a definition of this
  canonical algebraic-space ideal filtration. tools/blueprint_refs.py search 'ideal power'
  returned only sheaf Rees algebra, adic derived inverse limit and flat ideal pullback,
  none defining the construction at issue.

Validation: scompile.py compiled both modules separately in dependency order, against
its live published server build and private overlay. Both are clean. All theorems have
sorry proofs; definitions have real section/submodule/cokernel data. No direct build,
repository edit, git command, or launcher-tool edit was used.

## New nodes

Added def-sfb-space-closed-ideal-filtration, in the item's chapter. It defines the
actual kernel sections, subsheaf-generated products, iterated powers, inclusions and
canonical quotients, for arbitrary modules and morphisms, with no Noetherian assumption.
Sources are Stacks 03MB, 07UK and the existing small-model comparison 039Z. The node's
statement explicitly includes the sheaf condition of the intersections, matching the
sole auxiliary sorry theorem closedIdealPowerFamily_isSheaf. Its proof docstring gives
the intersection/gluing argument in full. All other declarations are definitions with
real data, and lean.declarations lists all seven declarations. The three search kinds
above are recorded from their actual logs. Neither the DAG nor Mathlib nor the project
has this algebraic-space ideal-filtration construction; the scheme ideal product is
not a private replacement and remains only a proof input. Its blueprint ancestry is
the item's existing null node and full via chain; no blueprint node states it.

## Second reading by Q84

A separate final reading in this worker session compared the current node, both full
modules and new node record (no other agent was started, as the dispatcher forbids it).
The base Noetherian conditions are all present: chartwise local Noetherianity, compact
point space and absolute affine-test quasi-separatedness. The coherent hypothesis and
each coherent conclusion expand to site quasi-coherence plus the actual chartwise
finite-type-kernel predicate; neither finite type alone nor an arbitrary coherent
predicate is substituted. The closed immersion uses the full scheme-test condition,
and the kernel is fixed by the direct-image chart projections. The generated product
uses sheaf submodules and therefore includes local gluing. The named intersection
sheaf theorem is matched by the definition node's statement, source and proof docstring.
The quotient uses a genuine cokernel, and the original module universe is preserved.
Both coherence clauses, n=0 and the two directions of the support iff are present.
Ordinary chart-stalk vanishing is equivalent to geometric-stalk vanishing specifically
because the hypothesis is quasi-coherence; no support assertion for arbitrary module
sheaves is claimed. No arbitrary atlas, exponent, ideal or comparison is supplied as
an extra hypothesis. The report and record explicitly explain this representation.
The existing schemeRestriction definition node was added to stmt_deps rather than
silently using an unrecorded notion. Diagnostic Probe.lean was removed from the delivery.
No mismatch requiring a change to the accepted natural-language statement was found.

Final preflight: first dry run reported the live schema requires import_flags on new
nodes; added import_flags: [] without changing mathematical content. The next dry run
printed OK at 27c64ac1740. Final source check corrected the chapter name of Tag 03MB
to Morphisms of Spaces (spaces-morphisms.tex, lemma-closed-immersion-ideals); its
statement and proof were read. The latest blueprint unit and direct-image proof were
read as the ancestry context; this helper does not alter their statements.
