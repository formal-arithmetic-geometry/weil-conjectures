## What changed

Proved `AlgebraicGeometry.Etale.isIso_baseChange_of_smooth` in
`lean/Sheaf/Targets/EtaleSmooth.lean`, with its signature and visibility unchanged.
No other Lean module, definition, or statement changed.

The existing source-library `Etale.isIso_baseChange_app_of_smooth` already proves the
needed ambient bounded-below smooth-base-change conclusion for module coefficients.
The proved `DerivedForget` equivalence and exchange comparison transport this result to
abelian coefficients. The proof explicitly transports homology and geometric stalks,
uses `addOrderOf x` as annihilator, proves it positive using the ring map to the
geometric-point field, and proves its prime divisors invertible by divisibility of a unit.
This retains the bounded-below smooth-base-change route of the target and sk-rem-rest.
The unit record has no fixed realized steps. The node copy records the actual argument
and source declarations; its statement and Lean attachment are unchanged.

Replaced four proof-only imports with
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` and
`WeilConjectures.SixFunctors.BaseChange.DerivedForget`. All public imports are unchanged.

Validation: local single-file compilation passed without errors or warnings (4.4 seconds).
Both new imports passed `tools/import_direction.py may`.
`deliver3.py C1 Sheaf.Targets.EtaleSmooth --no-push` printed OK: the commit
compiles and passes preflight except for the second reading, which the second reader
writes; nothing was pushed. No new holes or new nodes were added.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.isIso_baseChange_of_smooth`
(node `nt-target-etale-smooth`), the only original hole (1 of 1).
Added holes: none. Remaining holes in delivered Lean modules: none.
No decomposition and no new statements. The imported source theory can still depend
on existing project holes; this delivery proves the target from that existing theory.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`

The source `SmoothBaseChange.Theorem` remains a transitive dependency of `Derived`;
its direct import was redundant. The three removed Sheaf modules are replaced by the
existing source realization of the needed theorem and coefficient predicates, not by
weaker target hypotheses. In particular, no unbounded/Plus exchange bridge is needed.
The extra output-membership clauses of `boundedBelow_derived_smooth_baseChange` are not
needed for this target.

The following 26 modules leave this target module's source-import closure (and the
attached node IDs are listed completely). This is pruning for this item: they remain
reachable from other project targets in the current `TargetsCheck` closure. No module
is withdrawn or claimed globally unnecessary.

- `Mathlib.Order.Bounds.OrderIso` (no attached node).
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`: `sbc-def-derived-categories-with-allowable-torsion`.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`: `sbc-def-base-change-square`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: `sbc-def-base-change-map`.
- `Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange`: `sbc-thm-bounded-allowable-torsion`.
- `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange`: `sbc-thm-bounded-below-derived-smooth-base-change`.
- `Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion`: `sbc-lem-bounded-below-truncation-criterion`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `def-weil-pbc-cartesian-square`.
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality`: `sbc-lem-bc-naturality`.
- `Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative`: `lem-weil-pbc-derived-stalk-conservative`.
- `Sheaf.AlgebraicGeometry.DerivedGlobalGerm`: `def-weil-pbc-derived-global-germ`.
- `Sheaf.AlgebraicGeometry.FiniteRangeComparison`: `sbc-lem-finite-range-comparison`.
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`: `lem-weil-pbc-geometric-point-pullback-stalk`.
- `Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk` (no attached node).
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`: `def-weil-pbc-hypercohomology-filtrations`.
- `Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion`: `lem-sbc-qcqs-higher-images-prime-torsion`.
- `Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`: `lemma-weil-pbc-exact-couple-abutment`.
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`: `def-weil-pbc-truncation-exact-couples`, `lem-weil-pbc-truncation-couple-morphism`.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`: `lem-sp-couple-morphism`.
- `Sheaf.CategoryTheory.ExactFunctorCouple`: `lem-sp-exact-functor-couple`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `def-weil-sheaf-of-modules-category`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `def-weil-pbc-sites-and-cohomology`.
- `Sheaf.CategoryTheory.SpectralSequencePageInduction`: `lem-sp-page-induction`.
- `Sheaf.CategoryTheory.TruncationCoupleExact`: `lem-sp-truncation-couple-exact`.
- `Sheaf.Paper.CohomologyInWeakSerreSubcategory`: `lem-sbc-cohomology-in-weak-serre-subcategory`.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded` (no attached node).

The original direct node dependencies `sbc-def-base-change-map` and
`sbc-thm-smooth-base-change` are no longer separate ingredients here. The latter is
already used by the source bounded-below theorem; the former's unbounded abelian arrow
is not constructed by this proof. The allowable-torsion and bounded-below node concepts
remain, realized via the source module-coefficient predicates and theorem.

## Where the brief, the DAG or earlier work was wrong

The plan overlooked an already available source theorem and the proved `DerivedForget`
comparison. The Sheaf bounded-below attachment has additional allowable-torsion output
claims, while the target needs only the exchange-isomorphism clause. Using the existing
source theorem avoids proving those extra claims or comparing two separately defined
unbounded exchange arrows. No mathematical statement was found false or changed.

A redundant explicit type annotation on the module base-change hypothesis caused Lean
to unfold the large unit-square-counit mate during unification and time out. Inferring
that hypothesis directly from the existing theorem, then rewriting it by the proved
map equality, compiles quickly. No definition or timeout limit was changed.

The zero-order argument also handles an empty base: a geometric point over X supplies
the ring map making Γ(Y,top) nontrivial. No global nonemptiness assumption is introduced.

## Second reading by C1

1. **Interface and accidental changes — pass.** I compared the delivered module and node
   with the repository versions. The target theorem's signature, universes, hypotheses,
   conclusion, and visibility are byte-for-byte unchanged. The only Lean changes are its
   proof and proof-only imports; the node changes record the actual proof route and
   dependencies. No definition or target statement was altered.

2. **Proof and soundness — pass.** The module compiles cleanly with `lcompile.py`, has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition.
   The proof transports the abelian object through the proved `forget₂` derived-category
   equivalence, transports homology stalks through explicit isomorphisms, and applies the
   source ULift-ℤ smooth base-change theorem. The positivity argument uses the ring map
   induced by a geometric point and the prime-divisor unit argument; no nonemptiness
   assumption is smuggled in. The comparison lemmas identify the canonical map in the
   target, so the final `IsIso` is for the stated morphism. No new theorem or node was
   added.

3. **Statements and edge cases — pass.** The module-stalk torsion condition is exactly
   the source theorem's `torsionHomologyOfPrimes` hypothesis after coefficient transport.
   `addOrderOf x = 0` is ruled out from the induced map to a nontrivial field, including
   the possible empty-base situation, and prime factors are handled by divisibility of a
   unit. Searches and repository declarations found no existing stronger or duplicate
   statement needed by this proof.

4. **Pruning and route — pass.** The bounded-below smooth-base-change route and the
   `sk-rem-rest` route are retained. The four direct proof-only imports replaced by the
   source `Derived` and `DerivedForget` modules are genuinely unused after the proof was
   rewritten; the report's no-longer-needed list records the resulting closure pruning.
   Public imports remain limited to declarations used by the target interface.

5. **DAG agreement — pass.** The node's proof steps, `proof_deps`, and `proof_origin`
   describe the code that is actually present, including the coefficient equivalence,
   stalkwise torsion reduction, and final source-theorem application. The unit's route is
   preserved, no split-off statements were introduced, and the node's target statement is
   unchanged.

I changed only this report section during second reading. No Lean proof, declaration,
statement, node, or import required repair.
