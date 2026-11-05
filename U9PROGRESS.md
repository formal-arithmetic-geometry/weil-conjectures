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

2026-11-05T21:38:36.900035+08:00: Retained native/category and adopted canonical audits remain clean (bf586/210151). All new declaration files have profiler true. Adopted scalar files now use profiler.threshold0 for final measurements. Added K4C_RESULTS.md with verified scope, failed controls, and recipe; benchmark TSV currently472 rows, to refresh from final logs. New canonical open mate GREENba09fa8ca/205841 (218ms), generic cube composition GREEN945c2e0792/212654 (2.58ms). Concrete K9 pullback-cube repair checking3428c05ea2/log212758; full audit snapshotb33caeacc8/log212205 is older than the tiny generic map_comp correction and will need recheck. Integral normalization checkinga7355a85bd/log210818; old abstract transport error there is already fixed/green893b89/211213, latest normalization also includes identity simplifications. Added actual-integral-exchange corollary SmoothPurityIntegralOpenReductionExchange, currently uncommitted/unverified. All current waiting is remote baseline work; ucheck is the only compiler used. No DONE yet.

[K4c→LEAD/K4, 2026-11-05T21:41:54.285844+08:00] Read K4a DONE620ed3b89 (checked061954d781/log204835): original-name finite wrapper and exposed original-data predicate transport are clean. Adopting that verified finite closure (10 new native finite/boundary/predicate files + audit + repro wrapper) on K4c as well as the already adopted scalar proof, so the original repro MODULE can be checked here. This is adoption, not a new competing experiment; Strategy3 native category/chain remains separate and audited. Predicate unfolding reproduces the original equation; no dense round-trip claimed, per LEAD00:50. Only profiler reporting threshold changes to0. Open W2(b) concrete checks still cold active.

[K4c→C9/K9/K4b/LEAD, 2026-11-05T21:49:05.546056+08:00] Read NEW LEAD08:10; taking cross-field STEP2. Reusing K9 GREEN fully-faithful core + OpenFieldBaseChange61af11959 against C9 799f6fa976. Constructing actual cross-field compact-support bc by ambient basechange + fully faithful bounded inclusion. General etale compactified comparison still under search; no new assumptions or limits. Earlier W2 open cube checks continue; will hand off green pieces to K9.

[K4c→C9/K4b/K4/LEAD, 2026-11-05T21:54:19.539655+08:00] Open exchange drafted in SmoothPurityOpenFieldExchange (654d3f38bf, checking215135): ambient extension-by-zero mapDerived BC → leftDerived pullbacks → bounded restriction → actual compactified open functors; all-object mate and unit use K9 shortcut. Requires WeaklyEtale πY, valid for our field change. General etale alternative under investigation: Zariski Main open+finite factorization is proved in AlgebraicGeometry/Morphisms/QuasiFiniteFactorization; closed+smooth-proper exceptional BC is already proved across arbitrary fields (Comp + SmoothProjection), though GenericPoint wrapper unnecessarily specializes target to point. Could use local projective embedding of finite factor instead of rebuilding compactified etale adjunction. Need canonical exchange pasting at outer boundary; not yet a proof/green claim.

[K4c→K4b/C9/LEAD, 2026-11-05T21:57:10.410037+08:00] Cheaper possible chart replacement (no general etale comparison): affine W has PROVED AlgebraicGeometry.affineSpaceEmbedding W (AlgebraicGeometry/AffineSpaceEmbedding.lean:190). Graph of W→Y embeds W CLOSED into A^n_Y because Y separated over k. Then W→A^n_Y→P^n_Y→Y is CLOSED + OPEN + SMOOTH PROPER. Library already proves all-object exceptional BC for closed immersions along weakly etale maps (DualizingFieldChange/WeaklyEtale:75). I drafted all-object coordinate transport to properLowerShriekBaseChange in SmoothPurityFieldProperMate. This can replace the missing etale Step2 with existing closed theorem; chart/global actual exchange pasting is still needed in either route. Geometry already green, so recording as optional cheaper completion rather than changing your files.

[K4c→C9/K4b/K4/LEAD, 2026-11-05T22:00:52.269728+08:00] Read binding LEAD08:20. Global candidate now SmoothPurityGeometricFiberExchange.purityGeometricFiberLowerShriekExchange, built uniformly from compactificationOverField f, its geometricFiber, ambient weakly-etale compactification BC, bounded inclusion, and target compactification independence. Global open mate/unit corollaries use K9 fully-faithful lemma; no piecewise-choice gluing claim. Generic cross-field compactification exchange checkingee541c202c/log215510; global specialization UNCHECKED. Composition compatibility and general etale mate remain substantive gaps. Closed-graph alternative could remove etale gap, not composition gap.

[K4c→K9/LEAD, 2026-11-05T22:02:49.796109+08:00] Older W2 actual-integral-open normalization FAILED in210818: purity_trivialOpenExchange_app ELAB isDefEq200000 at concrete ExchangeFormalism identity specialization (26s module); the old second lemma also had ext descending into .hom, now understood. Upstream rational analogue has a1M heartbeat scope for precisely this trivial-compactification identification; I will not raise limits. With LEAD08:10 assigning W2 exclusively to K9, retiring the three unverified integral-normalization/application files from retained Lean closure (preserved in commit history); keeping GREEN generic identity/adjunction-transport/mate helpers and the pending repaired canonical coefficient cube. New cross-field open proof uses K9 fully-faithful route and does NOT depend on this failed normalization.

[K4c→C9/K4/K4b/LEAD, 2026-11-05T22:16:10.576669+08:00] GREEN ambient cross-field formalism: u9/K4c77b9fcc67, SmoothPurityAmbientExchangeFormalism, logK4c-20261105T221529 rc0/4127jobs. Uses actual derived upper/lower-star, exact open extension, existing pullback coherence, indexed by ALL schemes. Kernel771ms/elab2.16s for whole module; no new limits/opacity. This supplies the index category needed for applying abstract compIso_shriekBaseChange to geometric-fiber squares. Bounded global Ex + open/closed mate checks still compiling prerequisites in215510/215135/220154; not yet green. Composition compatibility remains open. K4: global Ex retains the ambient rightDerivedLowerShriekOfCompactificationBaseChangeIso and chosen compactification independence explicitly; adding a carrier formula for your Weil bridge.

[K4c→K4/C9/K4b/LEAD, 2026-11-05T22:27:04.501581+08:00] GREEN982a23848/logK4c-20261105T222318 rc0: SmoothPurityAmbientExchangeComparison identifies actual pullbackSquareComparison and baseChangeMap with all-scheme formalism (kernel1.19s/972ms); SmoothPurityAmbientOpenExchange identifies openImmersionLowerShriekUpperStarBaseChangeIso.inv with exchangeLeft on exact modules (kernel29.9ms). All default limits/exposed data. The latter is the normalization of the SPECIFIED CondensedModelBaseChange open iso, useful to K4 bridge. Next deriving it with mapDerivedCategoryAdjunction_mate then total-pullback coordinates; composition/global bounded identification still not closed.

[K4c→K4/C9/LEAD 2026-11-05T22:47:32.374106+08:00] Derived open normalization GREEN in K4c-20261105T223729 (source755dc1fc8c): purityOpenImmersionLowerShriekMapDerivedCategoryBaseChangeIso_inv kernel209ms; exact level50.2ms. Invocation rc1 only from independent OpenExchangeCoordinates typo, now repaired/awaiting small check. This is the SPECIFIED CondensedModelBaseChange derived open iso and mapDerivedCategory adjunction, no assumption. Composition bridge limitation identified: all-scheme formalism cannot directly use CompactSupportFormalism.HasProperExchange since library only supplies rational proper interchange on bounded constructible objects. Working with generic square/mate transport to relate bounded compositors; no unbounded IsIso premise introduced. Adopted K4b GREEN two-line UnitBaseChangeComp repair b908c8deca.
