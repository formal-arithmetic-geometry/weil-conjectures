## Worker report

Item: lem-coef-dualizing-support-evaluation. Module:
`Sheaf.SixFunctors.DualizingSupportEvaluation`. Main declaration:
`WeilConjectures.DualizingSupportEvaluation.evaluatedSupport`.
All auxiliary declarations below belong to that namespace. The only postponed
proof in this delivery is the main named theorem; its docstring gives the full
nine-step natural-language argument and sources. Definitions contain real maps,
functors and isomorphisms. No new axiom, hypothetical comparison datum, arbitrary
isomorphism choice, inverse limit, or normalization assumption is introduced.

The source read is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`,
paragraph 2, together with all nine extracted proof steps in the DAG node. The
original source field also names the older master snapshot. This delivery keeps
the mathematical node statement, proof and proof dependencies unchanged. It adds
only already-landed statement interfaces to stmt_deps and records the Lean.

### Hypotheses and objects

- Global finite-field datum: section variable `D : FiniteFieldDatum.{u}` gives
  exactly the fixed algebraic closure `D.k` and characteristic `D.p`.
- Prime and extension: `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]`
  `[Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`, and main hypothesis
  `(hl : l ≠ D.p)`. The ring, its chosen uniformizer, and finite quotient are the
  dependency's `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionRing`. Index `n : ℕ` represents the positive exponent
  `n+1`. Thus no zero quotient level is silently included or positive level lost.
- Scheme: `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]`; separated and finite type
  are precisely `[IsSeparated (X ↘ Spec (.of D.k))]`,
  `[LocallyOfFiniteType ...]` and `[QuasiCompact ...]`.
- Fixed compactification: `(c : Compactification (X ↘ Spec (.of D.k)))`.
  Its actual open immersion is `c.i` and proper map is `c.g`.
- Ordinary finite-level compact support is the dependency's
  `sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n+1))`.
  `supportModel` merely identifies the two published constant-ring direct-image
  presentations using `reductionConstantPush_eq`.
- The sequence-site input is universally quantified as
  `Q : coefficientSequenceDerived l E X`, the ordinary unbounded derived category
  of the actual ringed sequence site. Every strict complex gives such an object;
  there is no normalized-subcategory, flatness or boundedness binder. The level
  objects are `(coefficientSequenceDerivedEvaluation l E X n).obj Q`.
- Actual restriction transitions are
  `sigma l E X h Q`: `coefficientSequenceDerivedTransition` composed with
  the canonical `quotientRestrictionModel` presentation isomorphism. The quotient map is
  `compactSupportLevelQuotient l E m n h`. `alpha` applies the inverse hom-equivalence
  of `proEtaleRingDerivedExtensionAdjunction` to that transition. Thus alpha is
  exactly its tensor/restriction adjunct, never an independently supplied arrow.

### Each construction and conclusion

- `support` is native `ProEtale.VaryingRing.J ... c.i ⋙ ...P ... c.g`:
  exact open extension followed by the actual system-derived proper pushforward.
- `B` composes this with `coefficientSequenceDerivedRestriction` and the derived
  tower functor `sectionsTowers`. The latter is the actual
  `pointIntegralSections l E D.k` applied levelwise. Proper image and point
  sections are derived separately. The intermediate completed sheaf is only a
  coefficient presentation: restriction along R to its section ring followed by
  the finite quotient is the actual constant map R to A_(n+1). No limit over
  levels is taken. `sections` is the corresponding finite-level functor.
- `comparison` is precisely the open/proper coefficient map c: it conjugates
  `reductionDirectImageComparison` by the named canonical `supportModel` isos.
  That dependency defines the proper coefficient mate followed by the exact open
  scalar comparison, rather than postulating a natural map of these types.
- `d` is the scalar unit at F_m(M_m), followed by scalar restriction applied to
  `comparison.app M_m ≫ F_n.map (alpha ... Q)`. The order is the displayed
  formula in the node (Lean uses diagrammatic `≫`).
- `ev` and `transition` are the exact derived evaluation and localization of the
  actual horizontal arrow of an ordinary R-module tower.
- `sectionsEvaluation` is the canonical derived square for levelwise point
  sections. `theta : B ... ⋙ ev ... ≅ target ...` is an actual natural
  isomorphism, assembled from that square, `coefficientRestrictedEvaluationIso`
  and `compactSupportSystemEvaluation`, with functor associators. Its target is
  exactly the R-restricted point sections of F_n(M_n). This states the derived
  isomorphism itself, including naturality in the entire derived input.
- Main conjunct 1 is
  `transition.app (B.obj Q) ≫ theta_n.hom.app Q =
   theta_m.hom.app Q ≫ sectionTransition ... Q`.
  `sectionTransition` is RΓ(d) with the actual composition of quotient and
  constant-R restrictions (`compactSupportRestrictionComp`).
- Main conjunct 2 is the alternative formula
  `d = F_m.map sigma ≫ sfCompactSupportRestriction.hom.app M_n`.
  Both arrows are the specified published canonical arrows.
- Main conjuncts 3 and 4 state identity and every composable quotient equation
  for `sectionTransition`. They include equal indices and arbitrary gaps.
- Main conjuncts 5 and 6 state the same coherence before point sections.
  `dNormalized` only changes the restriction presentation through the canonical
  `quotientRestrictionModel`. The identity equation uses `normalizedDVRResUnit`;
  the composition equation applies Res_(r,m) to d_(m,n) and then the canonical
  `normalizedDVRResComp`. No equality is inferred from conservativity or
  faithfulness of evaluating arbitrary derived morphisms.
- Main conjunct 7 is `DualizingSiteCompatibility` for every quotient pair.
  This is the explicit finite-dualizing coefficient/site square: the actual
  `CoefficientCompatibility.transportedRecordedReductionDirectImageComparison`
  is applied directly to the same `reductionDirectImageComparison`, and the other side uses
  `Etale.ExceptionalCoefficients.compactSupportMap` at
  `finiteDualizingEtaleTerm`. At the dependency's chosen compactification this
  is definitionally its `finiteDualizingCompactComparison`; the node's arbitrary
  fixed compactification is retained. Only bounded-below membership witnesses
  for the two already-specified finite-dualizing objects are existential. There
  is no choice of a map or object in this clause.
- Main conjunct 8 is the conditional dualizing formula under arbitrary level
  isomorphisms `iₘ` and `iₙ` to `integralDualizingFiniteTerm`. Its antecedent says
  sigma agrees with the transported
  `integralDualizingExceptionalTransition`. By the scalar hom-equivalence this
  says exactly alpha is the counit-defined u of `lem-coef-finite-dualizing`.
  The conclusion is F_m(iₘ), then eta and Res(c followed by F_n(u)), then
  Res(F_n(iₙ.inv)). This is exactly the stated formula after the supplied level
  identifications, not an extra hypothesis on arbitrary Q.
- Every construction is a defined expression in the actual input, its canonical
  transitions and the fixed c. Thus the final independence-of-extra-choices
  clause is embodied by the definitions, not an arbitrary existential witness.

### Dependency declarations read and used

The signatures/docstrings of the recorded statement dependencies were read.
The scheme-morphism-properties node is a convention; the tower-abelian node has
Mathlib matches, not a missing Lean record. Those matches are the ordinary
functor-category abelian instance, levelwise mono/epi characterizations and
limit/colimit preservation by evaluation.

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the recorded ring/integers.
- `Sheaf.Paper.QcqsCompactSupportRealization`: ordinary intrinsic compact-support
  presentation, ultimately `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.Paper.NormalizedDVRTower`: `normalizedDVRDerived`, `normalizedDVRRes`,
  `normalizedDVRResUnit`, `normalizedDVRResComp`.
- `Sheaf.SixFunctors.FiniteDualizing`: `finiteDualizingEtaleTerm`,
  `finiteDualizingQuotient`, `finiteDualizingCompactComparison`,
  `integralDualizingFiniteTerm`, `integralDualizingExceptionalTransition`,
  `finiteDualizingRestriction_eq`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceDerived`,
  `coefficientSequenceDerivedEvaluation`, `coefficientSequenceDerivedRestriction`,
  `coefficientConstantTowerEvaluation`, `coefficientRestrictedEvaluationIso`,
  `coefficientSequenceDerivedTransition` (the actual horizontal map).
- `Sheaf.Paper.SemilinearDerivedSections`: actual semilinear-system derived
  pushforward/evaluation framework; native system evaluation uses this framework.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: recorded finite
  exceptional coefficient adjunction, as used by the finite-dualizing dependency.
- `Sheaf.Paper.FiniteCoefficientPoint`: actual final-object point sections;
  `pointIntegralSections` is the completed constant-map presentation.
- `Sheaf.Paper.CompactSupportNativeSystemEvaluation`:
  `compactSupportSystemLevel`, `compactSupportSystemQuotient`,
  `compactSupportSystemEvaluation`.
- `Sheaf.Paper.CompactSupportReductionTowerData` (public through the preceding
  interfaces): `compactSupportLevelQuotient`, `compactSupportRestrictionComp`.
- `Sheaf.Paper.PointSectionsDerivedReductionData`: published exactness instances
  for `pointIntegralSections` over the algebraically closed point.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `reductionCompactSupport`, `reductionDirectImageComparison`.
- `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionConstantPush_eq`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`:
  `sfCompactSupportRestriction` (the existing intrinsic restriction comparison).
- `Sheaf.Paper.EtaleProEtaleCoefficientTransport`:
  `CoefficientCompatibility.liftedScalarExtension` and
  `CoefficientCompatibility.transportedRecordedReductionDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`; scalar site boundary `pbcComparisonReduction`
  is the existing canonical comparison.
- Existing scalar API: `proEtaleRingDerivedExtensionAdjunction`,
  `scalarExtensionFunctor`, `scalarRestriction`.

Already-landed nodes for these additional interfaces are added to stmt_deps.
They do not create a dependency cycle; reachability through statement and proof
edges was checked. No replacement dependency module or new definition node was
needed. The remaining plain imports are proof dependencies cited in the complete
proof docstring (proper/open mates, finite origin and finite-duality site transport).

### Edge cases and searches

The statement was checked against m=n, r=m or m=n in a composite, arbitrary
gaps, the zero input, zero horizontal arrows, empty X, identity compactification,
unbounded inputs and nonflat quotient maps. Index 0 always means A_1.
Tensor extension remains derived; no exactness of tensor or invertibility of
alpha is assumed. Point sections use the given algebraically closed field,
which justifies the published exactness instances used to form the derived square.
No unrestricted exceptional adjoint on arbitrary pro-etale complexes is assumed.

Searches (msearch.py Q119 lem-coef-dualizing-support-evaluation; raw results in
sandbox searches.jsonl):

- LeanSearch: `Evaluation of separately derived proper pushforward and global
  sections for quotient semilinear module towers respects scalar adjunction
  transitions`: 8 hits, ordinary pushforward/adjunction declarations only.
- LeanFinder: `Derived compact support of quotient coefficient systems commutes
  with evaluation and identifies scalar restriction transitions`: 8 unrelated
  continuous-support/other declarations; no exact result.
- Loogle: `SheafOfModules.pushforward, Functor.evaluation`: no result; tool reports
  unknown identifier `Functor.evaluation`, so this search supplied no evidence
  beyond a failed name guess.
- Mathlib grep: `compactSupport.*(transition|evaluation)|semilinear.*(support|counit)`:
  0 hits.
- Repository rg searches in lean/WeilConjectures, lean/Sheaf and dag/nodes found
  the recorded semilinear sequence-site, native compact-support evaluation,
  coefficient transition, and trace-formula support-evaluation interfaces. None
  states this whole point-sections/scalar-unit/finite-dualizing theorem. The
  trace-formula result concerns evaluation before point sections.
- Exact item-id search in lean/WeilConjectures has no declaration. Name search
  `dualizing.*[Ss]upport.*[Ee]val|DualizingSupportEvaluation|evaluatedSupport` found
  only an unrelated clopen support comment. Existing notions were reused instead
  of defining another sequence-site, tensor functor or dualizing object.

No STATEMENT-DISPUTED issue or mathematical node correction was found. The earlier
DAG-cycle refusal is preserved below as history; the resumed dry run now passes.

### Validation

The complete module was compiled with the prescribed scompile.py wrapper on the
server in both sandbox and actual library module names, with no errors or warnings.
Every variable/universe is explicitly bound; autoImplicit is disabled. There is
one sorry, exactly in the main theorem. The delivery dry run is recorded below.

## Second reading by Q119

The dispatcher explicitly forbids starting other agents; this section records a
second pass by the same worker, not a claimed independent agent review. The
maintainer's independent delivery review remains the specified independent check.
The second pass compared every paragraph of the node against the module. It
identified the need to state coefficient-level coherence in addition to
section-level coherence; explicit identity and composition conjuncts were added
using the existing normalized restriction unit/compositor and the canonical
presentation iso. All clauses above, including arbitrary unbounded Q, actual
constant-R restriction, separate derivation, natural derived Theta, the actual
proper/open coefficient mate, and the conditional finite-dualizing comparison,
were then checked again. No statement strengthening or weakening was introduced.

## Earlier delivery preflight diagnostic (historical)

The prescribed command
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q119 lem-coef-dualizing-support-evaluation --no-push`
completed with exit code 1. Its server compile succeeded with no warnings. Nothing
was pushed. The only two refusal findings were:

- `(b) incremental DAG validation: cycles: lem-coef-dualizing-support-evaluation -> lem-coef-dualizing-construction reaches lem-coef-dualizing-support-evaluation`
- `(b) incremental DAG validation: cycles: lem-coef-dualizing-support-evaluation -> lem-coef-finite-dualizing reaches lem-coef-dualizing-support-evaluation`

Both first edges are inherited unchanged from the base item's proof_deps and
stmt_deps respectively. The additional theorem-dependency messages are explicitly
review notes, not refusal findings (`tools/stage2_delivery.py`,
`theorem_stmt_dep_notes`). The gate deliberately rejects inherited cycles through
a touched node (`tools/nt_incremental2.py`, `local_findings`); no tool was modified,
patched, run directly, or bypassed.

The read-clone paths documenting the pre-existing problem are:

1. lem-coef-dualizing-support-evaluation -> lem-coef-dualizing-construction ->
   def-pur-exceptional-coefficient-tensor-maps -> def-pur-co-smoothness ->
   fix-prop-projection-formula -> def-zl-field-weil-shriek-shift-data ->
   lem-pod-semilinear-field-operation-lifts ->
   lem-pod-weil-frobenius-compact-support-exchange -> sk-def-sf-exchanges ->
   sk-def-sf-operations -> thm-sf-ctf-stability -> thm-coef-integral-verdier ->
   prop-coef-integral-dualizing -> lem-coef-tower-trace-rectification ->
   lem-coef-dualizing-support-evaluation.
2. lem-coef-dualizing-support-evaluation -> lem-coef-finite-dualizing ->
   lem-coef-dualizing-affine-space -> def-pur-exceptional-coefficient-tensor-maps ->
   the same return path as in 1.

The mathematical statement is well typed and was not found false or ambiguous,
so a fabricated statement correction to delete its original prerequisites would
not be authorized. A dependency lean-only repair preserves the graph and cannot
remove either cycle. Changing downstream nodes is outside this worker's scope.
The compiled module, exact signature record and full report remain in the
specified sandbox, ready for the same dry run after the inherited graph is fixed.


## Resumed validation, 2026-10-23

The first action after inspecting the retained report was the prescribed
`deliver2.py Q119 lem-coef-dualizing-support-evaluation --no-push`.
It returned `OK (dry run): commit f3b93462f5d passes the preflight and compiles;
nothing pushed`. The earlier inherited-cycle refusal is no longer reproduced.
No graph workaround, dependency deletion, or Lean change was needed.

I reopened the full 380-line module, the node statement and nine proof steps,
and the current blueprint paragraph 2. The saved clause-by-clause correspondence
above remains accurate: actual sequence-site compact support, separately derived
point sections, the natural derived theta, the scalar unit/adjunct formula,
restriction form, both levels of coherence, and the finite-dualizing site and
counit comparisons are all retained. The zero and equal-index cases introduce no
extra assumption. The dispatcher forbids delegation, so this is the same worker's
self-check, with independent review still left to the maintainer.

A direct packet self-check confirmed that `lean.statement` is exactly the theorem
signature in the source, every line has at most 100 characters, autoImplicit is
disabled, and the sole postponed proof is `evaluatedSupport`. Against the current
read clone, only `lean` and additions to `stmt_deps` differ. The additions are the
already-landed interfaces listed above. There is no released repair note for this
item in the current read clone. The saved Lean module is retained unchanged.


## Returned delivery repair, 2026-10-23

The returned immutable head was `0dfba0e075b8`. The retained packet was inspected
before editing; its first required dry run returned
`OK (dry run): commit 1bfc9e2bef0 passes the preflight and compiles; nothing pushed`.
That mechanical pass did not resolve the independent review's two H2 findings.
The repair makes the following concrete source and metadata changes:

1. Removed `lem-weil-compact-support-coefficient-transition` from the added
   `stmt_deps` and removed its public import. `sigma` now composes the actual
   `coefficientSequenceDerivedTransition`, owned by the already cited
   `def-coef-ringed-sequence-site`, with `quotientRestrictionModel.hom` at the
   target level. The existing canonical restriction-presentation helper was
   moved before `sigma`. `alpha`, the restriction-form conjunct, and the
   finite-dualizing antecedent now use this transported actual transition.
   This is the coordinate conversion requested by point (1); no theorem from
   the removed dependency is used. The already cited
   `def-weil-compact-support-reduction-tower-data` now has an explicit public
   import for its quotient map and restriction compositor.
2. Removed `lem-sp-et-proet-coefficient-compatibility` from the added `stmt_deps`
   and removed its public import. In `DualizingSiteCompatibility` the alias
   `proEtaleCoefficientMap` was expanded to
   `transportedRecordedReductionDirectImageComparison φ c
   (reductionDirectImageComparison φ c.i c.g)` verbatim. Both constructions
   belong to the existing cited definition nodes
   `def-sp-et-proet-coefficient-transport` and
   `def-sp-reduction-direct-image-comparison`. No theorem from the removed
   dependency is needed for this definition.

The accepted `det-sp-reduction-exceptional` dependency remains: its proved
`reductionConstantPush_eq` is needed by `supportModel`. The accepted definition
node `lem-pod-point-sections-derived-reduction-data` also remains for its exactness
instances. No mathematical statement, proof, proof dependency or source was
changed. No new node or dependency module is needed. The signature record and
helper declaration list were updated to the actual repaired source.

The same worker reopened the node and repaired module for a second reading.
All eight conjuncts and their hypotheses remain as mapped above: the only
transition change is the canonical presentation of the same sequence-site
horizontal arrow. Its identity and composite cases, the zero input and empty
scheme, arbitrary unbounded input and nonflat quotients retain the same meaning.
The site-square alias expansion is definitionally identical to the returned
version. Delegation remains forbidden by the dispatcher.

Repair validation: the prescribed `scompile.py Q119
lem-coef-dualizing-support-evaluation` compiled the repaired file in both sandbox
and actual library module modes, completing in 24.1 s and 21.4 s respectively,
with no errors or unexpected warnings. A packet self-check confirmed the exact
signature record, all 23 recorded declarations, explicit universes/binders through
`autoImplicit false`, module mode, 100-character line width and a sole postponed
proof in `evaluatedSupport`. Relative to the current read clone the only changed
item fields are `lean` and additions to `stmt_deps`; no original prerequisite was
deleted. Both returned H2 additions are absent, while the two explicitly accepted
dependencies remain.
