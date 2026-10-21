## Worker report

The module `Sheaf.Paper.StratumCompletionUnitRestriction` states every clause of
`lem-weil-pbc-stratum-completion-unit-restriction`. Its primary declaration is
`AlgebraicGeometry.Scheme.stratum_completion_unit_restriction`; the other clauses
and the canonical constructions are listed in `lean.declarations`. All eleven
new theorems have proof `by sorry`. Definitions have actual data. There is no
statement correction, disputed statement, or dependency module. The return repair adds
one existing-declaration definition node for the canonical coefficient/pullback comparison.

I read the whole node and its eight proof steps, every statement dependency's
statement and record, the recorded interfaces and their docstrings, and the
proof-dependency interfaces available in the checkout. I read Bhatt--Scholze
Lemma 6.5.8 and Proposition 6.6.11 from the local PDF. The latter explicitly
uses stratum restriction and the pro-etale local property of completeness in
its reverse direction. The source text is unchanged in the delivered node.

Hypotheses and clauses correspond as follows. Declaration names below are in
`AlgebraicGeometry.Scheme` unless explicitly qualified.

| Node text | Lean rendering |
| --- | --- |
| X is locally Noetherian and quasi-compact | `[IsLocallyNoetherian X] [CompactSpace X]` in the unit, intrinsic preservation, and detection statements. No separation assumption. |
| A commutative Noetherian ring, finitely generated I, torsion A/I, finite perfect positive quotients | `{A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)`, retaining all the fields of `CompleteCoefficientDatum` and `quotientFinite`. |
| R_n=(A/I^n)_X and B_X=lim R_n | `d.finiteRing X n`, `d.completedRing X`, `d.projection X n`, using the recorded continuous-functions sheafification and its actual limit. Lean level n means positive exponent n+1. |
| K in the actual D(Mod(B_X)) | `K : d.derived X`, definitionally `reductionDerivedCategory X (d.completedRing X)`, using the standard unbounded localization. |
| Locally closed immersion, site-object restriction, or their composite | `IsAdicStratumRestriction f`, the disjunction of `IsImmersion f`, `WeaklyEtale f`, and both two-step factorizations. The intermediate scheme and both arrows are quantified, with their composite required to equal f. A weakly etale map with a scheme in the fixed universe is an object of Mathlib's small pro-etale site. |
| u^-1 B_X is B_Y, by quotient projections | The existing `d.integralRingIso f` is used throughout, and `stratumRestriction_limits` includes its projection equation for every n, with exactly `d.finiteRingIso f n`. `stratumFiniteCoefficient_naturality` includes every quotient transition. |
| Module pullback is exact | `stratumModulePull d f` abbreviates the published `proEtaleRingModulePullback` with this very coefficient iso. `stratumRestriction_limits` states additivity and preservation of finite limits and finite colimits. Its small-limit assertion is the intermediate claim of proof steps 1--2, needed to prove the completion claim. |
| Canonical isomorphism of finite derived reductions, retaining finite coefficients | The existing `(d.chi f n).app K` is exactly the displayed finite-coefficient isomorphism. `stratumReduction_evaluation` identifies evaluations of the entire strict tower comparison with this particular chi, using the published scalar-restriction/pullback comparison. It does not forget the finite quotient action in stating chi. |
| Commutes with quotient transitions | `stratumModuleReductionIso` is an iso of actual strict towers. `stratumReductionIso` is its universally normalized iso in the derived category of strict towers, not just a sequence of unrelated isos in the derived category. Exact evaluation naturality supplies every transition square. |
| Commutes with normalization maps | `stratumReduction_normalization b a h K` is an explicit equation between the two paths using `completedReductionDerivedNormalization`, chi, and the finite quotient/pullback chi. It quantifies all a <= b, including equal indices. |
| The specified strict quotient tower and its quotient unit | `completedReductionTower X d` and the existing `d.completionUnit X K` are reused. The unit is the derived constant/limit adjunction unit followed by Rlim of `completedReductionAugmentation`. |
| Inverse image of the unit is the restricted object's unit, including the map from u^-1 K | `stratumCompletionComparison_unit` asserts `IsIso (stratumCompletionComparison d f K)` and the equation `(d.pull f).map (d.completionUnit X K) ≫ stratumCompletionComparison d f K = d.completionUnit Y ((d.pull f).obj K)`. Both sides start at exactly `(d.pull f).obj K`. |
| Intrinsic derived completeness is preserved | `stratumIntrinsicComplete_preserved` uses the existing `IsDerivedCompleteIntrinsic` on arbitrary supplied source and target representatives. `r`, `a`, and `ha` specify the finite tuple generating d.ideal, including an empty tuple. The target scheme is not assumed Noetherian. |
| Any finite stratification and any chosen pro-etale cover of each stratum | `S : FiniteLocallyClosedStratification X` is precisely the dependency's finite locally closed partition with scheme realizations. `V : ∀ i : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain i)` quantifies every such family with arbitrary cover-index universe w. |
| Completeness iff all covering-member restrictions are complete | `stratum_completion_unit_restriction` is the biconditional with RHS quantified over every i, every j of `(V i).I₀`, and every representative and realization of the actual pullback along `(V i).f j ≫ S.immersion i`. The same intrinsic Koszul predicate and generators occur on both sides. |

Canonical choices are pinned down, rather than replaced by arbitrary maps:

* `stratumModuleReductionIso_exists` specifies a UNIQUE ordinary strict-tower iso by
  its quotient-unit equation. Quotient units are epimorphisms. This fixes the
  ordinary tensor/pullback comparison, natural in the module, on the full tower.
* `StratumReductionFormula` conjugates this ordinary comparison by the actual
  universal reduction counits and the exact pullback localization factors on
  every K-flat representative. `stratumReductionIso_exists` specifies the UNIQUE
  derived natural iso with this formula. Merely identifying evaluations would
  not determine a map in the derived tower category; this equation is stronger
  and is why that representative normalization is explicit.
* `stratumReduction_augmentation` preserves the actual strict quotient unit.
* `stratumRlimComparison` is defined as the derived constant/limit adjunction
  mate of the canonical constant-pullback iso. There is no choice in this map.
  `stratumRlimComparison_isIso` is for all strict derived towers under an allowed
  restriction. Exact countable products and the normalized strict-limit theorem
  identify this mate with the canonical Roos product comparison in the proof.
* `stratumCompletionComparison` is the composite of that mate and Rlim of the
  prescribed strict reduction iso. Its invertibility and unit equation are
  asserted for every K, without a completeness assumption on K.

The small pro-etale site has object universe u+1 and morphism universe u;
coefficient rings and module carriers have universe u+1. No site universe equality
is imposed. The generic equal-universe constant-completion interface is used only
as a proof dependency; the published actual-site coefficient transport and
Koszul/quotient comparison are reused for the statements.

Dependency declarations used:

* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology and
  `proetalePrecoverage`; immersion and weak-etaleness are their existing scheme
  morphism properties.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its Q.
* `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, `completedReductionModuleTowerFunctor`,
  `completedReductionTowerComplexCounit`, `completedReductionEvaluation`,
  `reductionCoefficientMap`, `completedReductionDerivedNormalization`, and the
  recorded module/derived/tower interfaces and arithmetic fields.
* `Sheaf.Paper.FourCorners`: `d.integralRingIso`, `d.finiteRingIso`,
  `d.projection_comm`, `d.pull`, `d.finitePull`, `d.chi`,
  `proEtaleReductionPullbackIso`. This landed node is added to stmt_deps.
* `Sheaf.Paper.CompletedPullback` (the published integral interface retained by
  public import in the completed-pullback node's current module):
  `d.completionUnit`, `d.constantRlimAdjunction`, `d.towerModulePull`,
  `d.towerPull`, `d.constantPullbackIso`, `d.derivedConstantPullbackIso`,
  `completedReductionModuleUnit`, and `completedReductionAugmentation`.
  This landed node is added to stmt_deps.
* `Sheaf.Paper.CompletedRlimFunctor`: `completedRlim`, cited through its existing
  definition owner `def-pur-completed-rlim-functor`. The properties theorem
  `prop-weil-pbc-rlim-functoriality` is not a statement dependency.
* `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, the recorded intrinsic predicate;
  `Sheaf.Paper.IntrinsicCompletion`: `IsDerivedCompleteIntrinsic`, its existing
  canonical transport through the completed-ring comparison to the actual
  function-coefficient presentation. This is the same published Koszul fiber
  and its (u,0) unit, not a second completion definition.
* `Sheaf.Paper.CompletedKoszulQuotientComparison`:
  `completedKoszulQuotientComparison`, the published unit-normalized bridge
  used only in the proof. Its node is absent from stmt_deps.
* `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictionDerivedPullback`, including its finite quotient action,
  and its ordinary scalar-restriction and comparison constructions. These are cited
  through `def-weil-pbc-ring-restriction-pullback-comparison`, an existing:true
  definition record. The adjunction theorem is not a statement dependency.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`, the recorded
  definition without an extra constructibility condition. Under the global
  Noetherian hypothesis its strata are constructible, as needed for the proof
  dependency `proEtale_derived_stratum_cover_detection`.

Proof-dependency modules with recorded statements are imported non-publicly:
ConstantCompletionEquivalence, ExactProductFunctorStrictLimit,
RingedSiteRestrictionKFlat, NoetherianStratumDetection,
ProEtaleImmersionLimitPreservation, ProEtaleInverseImageLimitsZariskiLocal,
ProEtaleCountableProductsExact, ProEtaleWeaklyEtaleLocalization,
ProEtaleConstantRingMap. IntrinsicCompletionCompleted and AdicCoefficientDatum are
already reached by the public imports. Two proof-only nodes,
`lem-weil-pbc-reduction-pullback-derived-tower` and
`lem-weil-pbc-module-sheaves-limits-sectionwise`, currently have no recorded Lean
module, so there is no module to import for them. No object required to state
this item is missing: its specialized canonical strict reduction comparison is
supplied here, and actual module limits are provided by the imported Mathlib
module-sheaf API. These two nodes remain proof dependencies; their proofs are
not prerequisites for a stage-2 sorry statement.

Edge cases checked before and after drafting:

* Empty scheme, empty stratification (n=0), and covering families of the empty
  stratum: no nonemptiness hypothesis is added; the derived category is zero
  and the vacuous local condition is correct.
* Empty generating tuple (r=0), zero ideal, unit ideal, and zero coefficient
  ring: every construction uses the published quotient and Koszul units; no
  `Nontrivial`, positive-rank, or proper-ideal assumption is added.
* Zero complexes and unbounded complexes: neither boundedness nor constructibility
  is assumed anywhere in the restriction or detection statements.
* First positive quotient n=0 (exponent 1), equal levels b=a, and arbitrary
  a<=b: the explicit quotient normalization equation includes them all.
* Identity restriction and both composite orders: the predicate includes these;
  all comparisons are built from canonical coefficient/projection and adjunction
  maps, including in these cases.
* Covering members and intermediate schemes need not be Noetherian or quasi-compact.
  The hypotheses are on the original X alone. Cover index universe w is independent
  of u; no small-cover or finite-cover condition is silently imposed.

Searches made (2026-10-21):

* `msearch.py ... leanfinder "Restriction to locally closed strata on the pro-etale
  site commutes with the adic completion unit and detects derived completeness"`:
  eight hits, concerning ordinary adic-completion lifts, evaluations, and transition
  maps. None concerns the pro-etale strict quotient completion unit or finite strata.
* `msearch.py ... loogle '"Sheaf", "completion"'`: zero hits.
* `msearch.py ... grep 'pro.?etale.*complet|complet.*strat'`: zero Mathlib hits.
* `msearch.py ... leansearch "Derived adic completeness is preserved and detected
  by restrictions to a finite stratification"`: eight hits (`IsAdicComplete.bot`,
  `IsAdicComplete`, `AdicCompletion`, `AdicCompletion.module`,
  `IsAdic.isPrecomplete_iff`, `WittVector.isAdicCompleteIdealSpanP`,
  `AdicCompletion.instCommRing`, `AdicCompletion.piEquivFin`), all ordinary
  algebra/topology; none is the present sheaf-derived statement.
* `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, stratum-completion combinations, and every proposed principal
  name: no existing declaration for this node. Broader completion/restriction
  search located the canonical FourCorners, CompletedPullback,
  IntrinsicCompletion and CompletedKoszulQuotientComparison interfaces, which are
  reused. The closest `adic_stratified_perfect` is a constructibility/local-perfect
  characterization, with different hypotheses and conclusion, not this node.

Validation: the whole delivered module passed scompile.py in sandbox and library
mode, 5.9 s and 5.5 s respectively on the second pass, with no errors or warnings.
There are no auto-bound variables, private definitions, file-local notation or
file-local instances, and no Lean line exceeds 100 characters.

## Second reading by NA

This is the worker's second pass; the dispatcher's independent maintainer review
will read the delivered packet. I reread the unchanged node, both source passages,
and the final Lean module. The checks specifically included the full projection
square in `stratumRestriction_limits`, the all-level normalization equation,
`stratumReduction_evaluation` retaining quotient-coefficient pullback before
scalar restriction, and `stratumReduction_augmentation` in the actual derived
strict-tower category. The strict comparison is normalized on K-flat representatives,
so it is not specified just by evaluation data. The completion comparison is a
fixed adjunction mate followed by the fixed tower iso; its source-unit equation
starts at `(d.pull f).obj K`. Both preservation and detection use the published
intrinsic Koszul predicate via its existing coefficient transport, rather than
defining completeness as quotient completeness. The arbitrary covering family
quantifiers and the absence of a Noetherian assumption on its members match the
node. No mismatch or statement correction was found. No independent second-reader
agent was started, in accordance with the explicit dispatcher instruction.


## Return repair (immutable head 624ffde843d6)

The retained packet was first checked with deliver2.py --no-push; it passed the
mechanical preflight and server compile as commit 20dacafed4b. The independent
return identifies semantic dependency ownership that those mechanical checks do
not detect. All three numbered points are repaired:

1. The only construction used from CompletedRlimFunctor is `completedRlim`.
   Replace the added theorem dependency `prop-weil-pbc-rlim-functoriality` with
   its already landed definition owner `def-pur-completed-rlim-functor`.
2. The finite-evaluation equation uses the plain definition
   `proEtaleRingRestrictionDerivedPullback`. Add the existing:true definition node
   `def-weil-pbc-ring-restriction-pullback-comparison`, recording this construction
   and `proEtaleRingRestrictScalars`, `proEtaleRingRestrictionPullbackApp` and
   `proEtaleRingRestrictionPullbackInv` in the published module
   `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. Replace the added
   theorem dependency `lem-weil-pbc-ring-sheaf-change-adjunction` by this node.
   The derived comparison is literally the descent of the inverse of `asIso` of
   the ordinary comparison; it is not chosen from the derived adjunction theorem.
3. Remove the added `lem-weil-pbc-completed-koszul-quotient-comparison` from
   stmt_deps: it supplies no object in any statement. Its proof use does not
   justify a statement dependency.

The main Lean file is unchanged. Against current main the mathematical statement,
proof, proof_deps, source, and all non-owned fields of the item remain unchanged;
only lean and the permitted added statement dependencies are delivered. The
current base has the original nine stmt_deps, so removing the three rejected
additions does not remove any base dependency. The delivery wrapper rebuilds the
packet on the current server base. The named CompletedPullback interface is
still obtained through the import chain of def-weil-pbc-completed-pullback, as
noted by the reviewer; no new interface or duplicate statement is introduced.

## New nodes

`def-weil-pbc-ring-restriction-pullback-comparison` owns the existing scalar
restriction and canonical ordinary/derived pullback comparisons. Its source is
Stacks Tag 03D3 (the module adjunction mate) and the exact termwise localization
used with Tag 0D6D. It introduces the compatible ring-sheaf square, defines
restriction through the ring maps, defines the ordinary comparison by its actual
unit/direct-image-identity/counit formula, and defines the derived comparison as
the descent of its inverse with the standard composition factors. The record is
existing:true on the published module; no module is copied. The primary signature
is verbatim from the server source read with scompile.py --source. Its four names
are the exact declarations requested in return point (2).

The source-to-Lean correspondence for this node is: `{U V : Scheme.{u}}` and
`f : U ⟶ V`; `RV SV` and `RU SU : Sheaf (ProEt.topology _) CommRingCat.{u+1}`;
`aV`, `aU`; `cR`, `cS`; and the explicit `comm` projection equation are the
published module's binders. `proEtaleRingRestrictScalars` is Mathlib scalar
restriction through the commutative-to-ring-sheaf forgetful functor.
`proEtaleRingRestrictionPullbackApp` is exactly the three-arrow mate formula;
`proEtaleRingRestrictionPullbackInv` gives its natural transformation; and
`proEtaleRingRestrictionDerivedPullback` composes the inverse ordinary iso's
termwise descent with the two exact derived composition isomorphisms. No
Noetherian, finiteness, flatness or separation assumption is added. The identity
map, identity coefficient square, zero ring sheaves, and empty scheme remain
allowed. No additional statement of invertibility or adjunction compatibility is
introduced by this ownership record.

Searches performed for the new node on 2026-10-21:

* LeanSearch, "Restriction of scalars of sheaves of modules commutes canonically
  with inverse image under compatible ring sheaf isomorphisms": eight ordinary
  scalar-restriction declarations, including SheafOfModules.restrictScalars.
* Loogle, `SheafOfModules.restrictScalars`: four hits, the generic functor,
  additivity, and its object/map values.
* Mathlib grep, `restrictScalars|pullback` in
  Algebra/Category/ModuleCat/Sheaf: 22 hits, ordinary restriction and continuous
  pullback/direct image APIs. The broader grep
  `restrictScalars|RestrictionDerivedPullback` had 25 hits, mostly ordinary
  algebraic scalar restriction. The exact query records are in mathlib_searches.
* Project/DAG/upstream rg on the four names finds their published definitions and
  consumers; parsing all definition-node lean records finds no owner of any of
  these four names. The recorded adjunction theorem owns the properties rather
  than this plain construction. No WeilConjectures or upstream-name record
  matches. Blueprint search `restriction.*scalar|change.*ring`: zero nodes;
  blueprint ancestor lookup gives thm-weil-pbc-finite-extension.

## Repair self-check by NA

I reread each of the three return points against the final node files and the
unchanged Lean file. The final added dependencies are the two previously
accepted FourCorners/CompletedPullback definition nodes, the existing Rlim
definition node, and the new existing:true coefficient/pullback definition node.
None of the three rejected theorem additions remains. I read all four recorded
comparison declarations and their full ambient binders from the current server
source, checked both comparison directions and the unit/counit formula, and
checked the new node fields and source. The ordinary and derived comparisons
are canonical constructions with actual data, not arbitrary endpoint isomorphisms.
The original hypothesis/clause table and edge-case analysis still apply because
the theorem module and the natural-language statement are unchanged. No separate
agent was started, as required by the dispatcher.


## Repair validation and tool blocker

The original saved packet passed the initial prescribed --no-push run (commit
20dacafed4b). After the three return repairs, local record checks confirm: only
lean and stmt_deps differ on the item; no base dependency is removed; all three
rejected theorem additions are absent; both recorded primary signatures match
their actual source verbatim; the new node has exactly the required field set,
matching bracket citations, existing:true with no copied module, and the required
JSON layout. The unchanged theorem module has eleven sorry proofs and maximum
line length 95.

The repaired packet cannot currently reach the server preflight: the prescribed
scompile.py compile and two repaired-packet deliver2.py --no-push attempts fail
in the compilation infrastructure before compiling the delivery. Each reports
unknown module prefix 'Mathlib' while compiling the overlay dependency
WeilConjectures.Mathlib.CategoryTheory.NatIso; its search path contains the live
project build path and Lean's toolchain but no Mathlib package. The wrapper's
server confirmation then reports exactly "Live published library is unavailable".
A standalone scompile.py retry and a later dry run after a 45-second pause give
the same diagnostics. This is not a Lean elaboration error in the delivery and
not exit code 124. No launcher/compiler tool was changed or bypassed, no global
build was run, and nothing was pushed. All repaired files are retained here for
the next attempt once the published library is available.


## Retained-packet retry (2026-10-21 04:09 UTC)

As requested by the retry brief, I read this saved report first and immediately
ran deliver2.py NA lem-weil-pbc-stratum-completion-unit-restriction --no-push.
It failed before delivery compilation: overlay
WeilConjectures.Mathlib.CategoryTheory.NatIso reported unknown module prefix
'Mathlib', and SERVER CONFIRMATION reported "Live published library is unavailable".
A subsequent standalone prescribed scompile.py attempt on the retained theorem
module also failed before delivery compilation, now with the more specific error
that the object file Mathlib/CategoryTheory/Functor/Category.olean does not exist
in the published Mathlib build. SERVER CONFIRMATION again reported "Live published
library is unavailable". These are exit-1 infrastructure failures, not busy-server
exit 124 or elaboration errors in the packet.

I compared the retained item JSON with the current shared read clone: the only
changed fields are lean and stmt_deps; no base statement dependency is removed.
The four added dependencies are def-weil-pbc-four-corners,
def-weil-pbc-completed-pullback, def-pur-completed-rlim-functor, and
 def-weil-pbc-ring-restriction-pullback-comparison. All three rejected theorem
additions are absent. The new existing:true record lists all four requested
coefficient-comparison declarations and writes no duplicate module. The Lean
module remains unchanged, consistent with the independent review's instruction
that Lean needs no change. The repaired packet is preserved; no tool or upstream
source was modified and nothing was pushed during this retry.


## Retained-packet retry (2026-10-21 04:15 UTC)

I read the retained report and ran the prescribed deliver2.py --no-push first.
Two dry runs initially failed before the packet compile with a missing published
Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic.olean artifact, followed
by the server confirmation "Live published library is unavailable". The subsequent
standalone scompile.py run is progressing through the published dependency overlay.

I rechecked all three ownership repairs: the Rlim definition owner is cited,
the four ring-restriction/pullback constructions are recorded on the new
existing:true definition node, and the Koszul comparison is absent from stmt_deps.
The existing comparison signature matches the published source exactly. The theorem
module is unchanged and its primary signature matches lean.statement verbatim.

The current shared base changed lean_audit from null to {}; I preserved its current
value in the packet. The item now differs from that base only in lean and stmt_deps,
with no original statement dependency removed. Both node files retain canonical
indent-one UTF-8 JSON with final newlines.

Final retry result (2026-10-21 04:18 UTC): the standalone scompile.py
run compiled its preceding overlays but stopped at the shared
WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic overlay with
"timeout after 60 s". A third prescribed deliver2.py --no-push attempt retried
that overlay and returned the same timeout. Both attempts explicitly report
SERVER CONFIRMATION: "Live published library is unavailable". This is not a
"no answer from the compile server" diagnostic. None reached compilation of
the retained item, and nothing was pushed. All three requested ownership repairs
and the current-main metadata refresh remain retained in this sandbox. No
launcher tool, shared source or published artifact was edited or bypassed.

## Retained-packet retry (2026-10-21, fourth dispatch)

I read the retained report and ran deliver2.py --no-push first as requested.
The first dry run and the subsequent standalone scompile.py failed in the
upstream SiteInverseImageTensor overlay before this packet was compiled: the
published WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings.olean
object was missing. After a pause, another standalone scompile.py advanced to
EtaleInverseImageModuleObject but reported a missing published
WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients.olean.
These were exit-1 missing-artifact errors, not busy-server exit 124.
A further prescribed dry run is retrying the current server source overlay.

The retained packet was compared again with the current shared read clone.
Only lean and stmt_deps differ on the item, with no original dependency removed.
All three rejected theorem dependencies are absent. The four additions are
FourCorners, CompletedPullback, the existing completed-Rlim definition owner,
and the new existing:true ring-restriction/pullback comparison definition owner.
The primary Lean signature matches lean.statement verbatim, both node files
have the exact indent-one UTF-8 JSON layout with final newlines, and the unchanged
Lean module's maximum line length is 95. No upstream files or launcher scripts
were edited and no compilation wrapper was bypassed.

Final result of this retry (2026-10-21 04:44 UTC): the prescribed dry run
completed its current-server confirmation and printed:
"OK (dry run): commit 4025f42dabd passes the preflight and compiles; nothing pushed".
Thus the earlier missing-overlay-artifact errors were resolved by the prescribed
wrapper/server retry. The repaired packet now passes both the per-file compiler
and the maintainer preflight. The self-check above covers all three numbered
return points; no further Lean or node change was necessary.


## Retained-packet self-check for return 7603bd08ea63

As explicitly requested in the retry brief, I read the saved report and ran the
prescribed deliver2.py --no-push before changing the retained packet. It printed
"OK (dry run): commit 05cce7de27d passes the preflight and compiles; nothing pushed".
The wrapper checked the retained statement module and the existing-declaration
probe on the server, then ran the current server preflight on its freshly based
commit. Neither reachability diagnostic from the immutable-head return recurred.

I retained the mathematical packet as instructed for a passing initial dry run.
The fixed-scalar-geometric-adjunction node is not a file in this delivery and is
absent from the current shared read clone. The ring-restriction/pullback definition
is explicitly cited in the item's stmt_deps, and its four existing declarations
are checked by the wrapper's server probe. No unrelated node is edited or assigned
a fabricated mathematical dependency to repair an obsolete-head reachability error.

The self-check reread the hypothesis/clause correspondence and the actual final
Lean declarations, including the fixed-source unit equation, strict-tower evaluation
comparison and arbitrary covering-member quantifiers. The primary signature is
verbatim in lean.statement, autoImplicit is explicitly false, all Lean lines have
at most 95 characters, and both JSON files have the required canonical layout.
The item differs from the current shared read clone only in lean and stmt_deps;
none of its base statement dependencies is removed. Earlier ownership repairs
remain intact. The successful prescribed dry run is the current server evidence;
no local DAG validator or global build was run.

## Retained-packet self-check for return ac665650e32a

Following the explicit retry instruction, I read the retained report and ran
`deliver2.py NA lem-weil-pbc-stratum-completion-unit-restriction --no-push`
before changing the packet. It printed "OK (dry run): commit f54d2b28370 passes
the preflight and compiles; nothing pushed". Both server-checked Lean files
(the statement module and the existing-declaration probe) passed. Neither
incremental DAG reachability diagnostic in the return recurred on the current
server base.

I retained the mathematical packet as instructed for a passing initial dry run.
The fixed-scalar-geometric-adjunction node is absent from this delivery and
from the current shared read clone. The ring-restriction/pullback comparison
node is explicitly cited by this item's stmt_deps. No unrelated node is changed
and no artificial dependency is added to address an obsolete-head diagnostic.

For the required self-check I opened the final theorem module, both delivered
node records, the hypothesis/clause table, and the published ordinary mate and
derived pullback comparison. The unit equation retains the fixed source
(d.pull f).obj K; finite evaluation retains the quotient-coefficient scalar
restriction; strict comparison is characterized on K-flat representatives; and
detection quantifies every covering member and representative. I confirmed
that the primary signature equals lean.statement verbatim, autoImplicit is
explicitly false, the maximum Lean line length is 95, and both JSON files use
the required canonical layout. Against the current shared base only lean and
stmt_deps change on the item, with no base dependency removed. The earlier
ownership repairs remain intact. No Lean or mathematical-node edit was needed.
Only this report entry was appended after the successful dry run. No local DAG
validator, direct git command, or global build was run.
