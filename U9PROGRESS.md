# K4c strategy 3, 2026-11-05

19:41 CST: Started from c6a69c87e on u9/K4c. Read README, shared experiments and NOTES.
Current assignment is the K4 kernel repro, superseding the historical projection-formula leaf.
The repro's mathematical inputs already exist; route (B) does not remove its required finite Tate
reading comparison. No heartbeat changes or local Lean/lake executions.

19:45 CST: Shared LEAD diagnosis isolates synHread. Building an independent ordinary pullback
implementation (functors, adjunction, compositors and identities), coefficient vocabulary, finite
module equivalence and reading constructors. Original constructions will appear only in boundary
identifications. All new modules have profiler enabled. First batch tests foundational constructors.

19:48 CST: First ucheck dd5b262f22 is not green: duplicated notation was local to sections,
so declarations after those sections failed parsing. Fixed by keeping the duplicate namespace's
scoped notation. Also corrected a missing X binder in the generated coefficient file. The run
continues rebuilding prerequisite cache; no second build launched. Prepared separate finite
reading constructors and iso-level boundary declarations, all profiled with threshold 0.

19:55 CST: Batch 195111 green for duplicated Pullback, ChangeCoefficients, Coefficient,
Tower, FreeCoefficientPull, FiniteRoots, IntegralPullback, Scalars, TowerProjection,
ChangeCoefficientsComp, IntegralReduction, TowerReduction, PullCoefficientComposition,
TateCoefficientComposition, TowerDoubleReduction. FinitePullback has an ordinary rewrite
failure: old constant-section morphism's codomain leaks original continuousMapRingObj into the
new coeffRing interface. Added a typed coeffSection. IntegralReductionPullback kernel timed out
(60.9s cumulative): its supplied coefficient morphism still inferred the OLD target object.
Now reconstructing finiteReduction/compositeReduction/integersModPowReduction with explicit new
coefficient codomains. This is exactly the implicit-data mixing warned against in strategy 3.

19:56 CST: Breakthrough on the reduction half: IntegralReductionPullback GREEN9.8s in195405
once finiteReduction/compositeReduction explicitly target coeffRing. Previous version had kernel
60.9s timeout. Scalars ordinary rewrite fix prepared; new const section appeared folded in an
internal change command, so keep that proof's raw section expression while its exported statement
uses the typed new section. Next target includes original-statement boundary and axiom print.

20:06 CST: Read refreshed brief and K4-plan-2; now Experiment3 dedicated coefficient category,
minimal interface and one outer interpretation. Snapshot affd8ca0f/log195648 proves the COMPLETE
native finite integral Tate reading square: final kernel707ms, logged elaboration184ms, module8.3s.
Native finite reading kernel63.6ms; actual integral reduction kernel1.19s. All normal/exposed.
The separate FiniteBoundary only fails at upperStarFiniteCoefficientModEquivalenceIso_eq (rfl):
kernel62.2s; other boundaries finiteEquiv293ms, freeRootsIso368ms, readingIso414ms GREEN.
No original final statement has passed. K4C_BENCHMARK.tsv records individual profiler messages
for all current helper declarations (raw elaboration messages do not include tactics/TC synthesis).
Next: keep native proof, inspect minimal dedicated category interface and a single interpretation;
replace the expensive defeq comparison with small propositional adjunction/functor identities.

20:07 CST: Minimal dedicated-category prototype prepared: own Object type, own Category instance,
realize/ofSheaf, native geometric pullback, native finite reading and comparison, concrete Tate
objects/isomorphisms/square. No limits, monoidal or derived instances are needed for this square.
It interprets the already rebuilt native constructions and never invokes the old reading square.
One fully faithful realization is the intended outer operation. Separate generic boundary test
now uses adjunction/low-level iso identities instead of asking rfl to unfold the full mate iso.

20:22 CST: Applying minimal-category recipe to live scalar theorem. Imported its 41 missing,
sorry-free dependencies from K4 f5d3862758dd592b4bf0a8ce769f0b01e7d5e1af, with all data exposed
and profiler threshold0. Target statement/definition unchanged; only generic consumer is swapped
for Strategy3.DescentCategory.scalarDatum_conjugate_indexed. The new category uses labeled
objects and explicit realization: degree-one source objects retain (P ⋙ Q).obj M, whereas the
canonical targets retain Q.obj T. Native hom groups therefore retain each input's exact type.
Pullback uses explicit step isomorphisms. Generic scalar conjugation runs in this category and
realization is applied only once to the final equation. Not yet checked. The finite prototype's
current ucheck landed on a cold pool tree and is still rebuilding prerequisites (~16k/22k).

20:27 CST: Dedicated indexed category + scalar calculation GREEN at32be59e54, log202608:
IndexedCategory category/preadditivity/fully-faithful realization/pullback/realization iso all
kernel milliseconds; scalarDatum_conjugate_indexed kernel10.6ms. Category labels retain native
(P ⋙ Q).obj M source and Q.obj T target presentations. Actual scalar application pending.
Canceled ONLY own stale finite prototype job u9-K4c-1793880588 on verified newsrv t2 (log200947,
ef3337a2e4) after17min prerequisite rebuild; that snapshot predates category method fixes.
Runner reports rc0 on systemd cancellation; it is NOT a successful target check. No other jobs,
locks or scheduler settings touched. Next combined concrete check uses corrected snapshot.

20:30 CST: C1/K4a now confirm the original dense repro proposition itself times out without
any equation proof. Avoiding that global target per new LEAD plan. Isolating our different outer
iso boundary with an admission-free Prop type control and explicit source/target functor transport:
this should distinguish type conversion of two iso types from comparison of the iso values.

20:41 CST: Explicit N/T/U/e does NOT fix concrete scalar application: 11c0651d87/log203508
again ELAB isDefEq200000 at the unit native-comm argument (20s). Interface stays GREEN11s.
Next variant uses by-blocks only for the two cheap comparison-square inputs, bounded dsimp
+instances on comp_obj/map, then exact_mod_proofs. Keep scalar root input native and untouched.

20:41 CST: Found and removed an unnecessary heavy import in Coefficient: FiniteRootsOfUnity
belongs in FiniteRoots, not foundational coefficient data. CoefficientCategory now imports only
FinitePullback; its concrete integral consumer imports IntegralTateReading explicitly. This keeps
small boundary/category checks from rebuilding all Cartier/finite-duality prerequisites. Canceled
ONLY own boundary-check process group3768184 on verified pool43.166.79.118 (log203152) because
its obsolete import graph was still rebuilding baseline dependencies. Next small check uses the
reduced graph. Construction/proof bodies are unchanged by this import correction.

20:46 CST: Small modules now independent (4305 rather than22k jobs). CoefficientCategory GREEN3.2s
in204145. Outer-boundary TYPE-ONLY control fails kernel65.7s; sourceFunctor_eq fails66.5s, whereas
targetFunctor_eq checks241ms. Thus comparing the new/old condensed-ring source paths is itself
the costly conversion, before any equality proof. Testing a narrower representation fix: remove
coeffRing and its duplicate MonObj/IsCommMonObj instances, use raw continuousMapRingObj uniformly
in the entire duplicated chain. Keep explicit finiteReduction/compositeReduction codomains, new
pullback/adjunction/composition/reading definitions, own coefficient category, and coeffType.
No old finished reading proof is substituted. Previous alias variant is frozen in git/logs.

[K4c→K4/K9/K4b, 2026-11-05 20:58 CST] Read MR sections2–4/new LEAD04:25; no new A3 scalar variants. K4 owns generic reduced-trace adapter; K9 owns proper exceptional/rebased pullback drafts. K4c will take the ACTUAL INTEGRAL OPEN compact-support exchange/reduction cube, following OpenPieceCoherence + SquareCompatibleMate.exchangeLeft. This is the geometric open contribution to W2(b), not another generic trace lemma. Consumer support still available on K4 failure. Last existing raw-ring diagnostic completed0d41a6f011/log204757: removing duplicate coeffRing/MonObj route makes the previously65.7s boundary TYPE check224ms and source-functor identity237ms; only direct transported-iso rfl exceeds elaborator recursion. Full original theorem still NOT GREEN. Freeze diagnostics while working on open cube.

[K4c→K4/K4b/K9 2026-11-05T20:59:29.933017+08:00] Open reduction implementation now has canonical-data mate bridge: SmoothPurityOpenReductionAdjunction.purity_isMateSquare_openEtaleReduction (canonical etaleReductionLowerShriekIsoOfIsOpenImmersion mated to etaleReductionUpperStarIso after Rj!≅j* coordinate change). SmoothPurityOpenReductionExchange then applies SquareCompatible.exchangeLeft to K9's actual pullback cube (copied verbatim, profiled). Checking remotely, NOT GREEN yet. This removes any assumed mate/coeff compatibility. Remaining outer geometric bridge: identify exchangeLeft of these Rj!⊣j* adjunctions with inverse compactification-defined Ex_! on both integral and étale sides. I am doing integral normalization via generic PushforwardData; K4, if available, the étale counterpart can be done independently. No duplicate A3 build.

2026-11-05T21:01:49.606565+08:00: Stopped only verified own obsolete failed OpenReductionAdjunction build (205626/a45516d9f0, pool43.157.146.107 timeout/PGID4032586); generic helper had a small residual identity goal, fixed in next snapshot. Current205841 already includes that correction and actual open cube. Both tests preserve default limits. Archived failed old finite boundary files in git history and removed them from working branch; restored full native Strategy3 chain to checked7283 representation/import split. Adopted K4a ecd7b1cf8 canonical scalar closure verbatim; no new competing scalar work. Final own audit pending.

[K4c / native Experiment3 GREEN, 2026-11-05T21:06:53.978653+08:00] u9/K4c bf586f3b59, log /home/ubuntu/u9/logs/K4c-20261105T210151.log: Strategy3.Audit built8.4s, full independent coefficient/pullback/reduction/reading chain rechecked. Native finite integral square kernel622ms; dedicated coefficient-category integralReading_pullback kernel53.6ms, realize_equation3.37ms, category reading module7.3s. #print axioms BOTH final theorems and generic indexed scalar conjugation EXACTLY [propext, Classical.choice, Quot.sound]; no sorryAx, no limits/opacity. Native Experiment3 is complete; original expanded finite statement/old roundtrip remains K4FIX NO (new LEAD forbids final roundtrip). Winning K4a scalar proof adopted verbatim, own recheck still running in same combined log. New open W2(b) modules are independent and still checking; one abstract normalization typo caused combined rc1, so this is per-module success, not whole invocation GREEN.

21:07 CST: Stopped only own obsolete202756 job (pool43.157.148.197, verified timeout/PGID3583523) after current native category audit210151 passed. That snapshot contained the failed superseded scalar variant and its cold baseline rebuild was redundant after the audited current result. Cancellation is NOT GREEN.

[K4c→K4/K9/K4b, 2026-11-05T21:12:06.977514+08:00] Adopted canonical proof audited on K4c bf586f3b59/log K4c-20261105T210151: final purityCanonicalTateOneTrivialization_weil kernel56.4ms, audit EXACTLY standard axioms; coefficient postcompose30.6s (cost visible, passes). Native Experiment3 category/native theorem audits also clean. New useful W2(b) hook: EtaleLowerShriekCompactificationIso.lean already proves isIso_compactificationEtaleComparison for EVERY finite coefficient ring and etale map, gives compactificationEtaleAdjunction Rf!(c) ⊣ Le*, and compactificationEtaleComparison_baseChange (line99) against the ACTUAL compactification exchange. Candidate unit basechange is proved in EtaleLowerShriekCompactificationBaseChange. This may normalize the etale half without redoing the exchange formalism. My integral/open canonical-reduction cube checks still rebuilding; abstract transport has only a small map_comp rewrite correction pending.

[K4c→K4b/K9, 2026-11-05T21:16:30.936276+08:00] Read K4b compactificationEtaleAdjunction inverse-exchange claim; no duplication. Remaining ETale open boundary is nontrivial: existing rightDerivedUpperShriekIsoOfIsOpenImmersion uses rightDerivedLowerShriekIsoOfIsOpenImmersion (chosen compactification→trivial compactification→Dj!), whereas compactificationEtaleAdjunction uses the graph/candidate-unit comparison. Need normalize these choices, not just assert adjunction uniqueness for fixed L/R (units can differ). Integral counterpart and canonical coefficient mate/cube remain my current concrete checks. Generic exchangeLeft transport is GREEN on893b89c71a/log211213, kernel16.3ms; abstract conjugate-adjunction equality5.33ms.

[K4c→K9/K4b, 2026-11-05T21:21:55.826691+08:00] Canonical OPEN mate bridge GREEN on ba09fa8ca/logK4c-205841: purity_isMateSquare_openEtaleReduction kernel218ms; actual integral/finite open pull adjunction defs checked. Your EtaleReductionPullback draft reaches line76 but ELAB isDefEq200000 at the concrete map_comp/hred rewrite (12s module), NOT a kernel failure. I replaced only that composition step with new abstract SmoothPurityPullbackCubeComposition.purity_compose_pullback_cubes; retains your exact theorem statement, nf/ng naturality moves and original hred/hread inputs. Pending recheck; no limits/opacity/admissions.

2026-11-05T21:27:57.466951+08:00: Abstract pullback cube composition GREEN945c2e0792/log212654, kernel2.58ms,990ms module. Canceled only verified own obsolete audit211213/893b89c71a, pool43.166.79.43 timeout/PGID3714757; its OpenAdjunctionTransport result was already green, and final combined audit212205 checks the same retained closure with full profiling. Canceled run is NOT GREEN.
