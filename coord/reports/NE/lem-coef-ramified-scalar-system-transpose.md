## Worker report

The module `Sheaf.Paper.RamifiedScalarSystemTranspose` states the ramified scalar-system comparison and its actual ordinary adjunction transpose. Definitions contain real data; every postponed claim is a named theorem with its source and natural-language proof. The item JSON changes `lean` and adds landed declaration owners to `stmt_deps`, as authorized by brief-stage2 §5 and the H2 return. There are no new nodes or dependency-node edits.

### Hypotheses and objects

* `l`, `Fact l.Prime`, `D : FiniteFieldDatum`, and `hl : l ≠ D.p` give the global finite-field setting and the invertible coefficient prime. `E`, `L`, their field/algebra/finite-dimensional instances, and `i : E →ₐ[Padic l] L` give the finite coefficient extension. A field embedding is injective. Schemes have universe `u`; coefficient fields have universe `u+1`, as in the shared finite-coefficient interfaces. Smaller fields can be lifted. The site object/morphism universes remain `u+1` and `u`, respectively.
* `ramification`, `_he`, and `_hram : Associated (i(pi)) (v^ramification)` express the stated positive ramification index and equality of principal ideals. The first conclusion explicitly identifies every upper ideal with the actual `Padic.coefficientExtensionIdeal l L (ramification * (n+1))`.
* The named `xb`, `yb`, `xft`, `yft`, `xqc`, `yqc`, `xs`, `ys`, `fb`, `fs`, `fft`, and `fqc` bind exactly the separated finite-type k-schemes and separated finite-type k-morphism. They are explicitly included in the main theorem. `c : Compactification f` supplies j open and p proper. The noetherian instances in the general helper interfaces are consequences of finite type over a field (`FiniteCoefficientAdjoints.finiteTypeNoetherian`), not additional geometric restrictions.
* `lowerRings/lowerMaps` and `upperRings/upperMaps` are the dependency's actual coefficient towers. Index n means positive exponent n+1. In particular the upper exponent is e(n+1), including n=0; it is not silently replaced by the L-uniformizer exponent n+1.
* `Derived C τ W` is the ordinary unbounded localization of sheaves of modules on the vertical sequence site. It is not a category of diagrams of derived objects. `domain` is the full subcategory defined by the existing `SemilinearSections.Normalized` and, for every n separately, the existing `FiniteCoefficientAdjoints.ctf` predicate. The latter is `ProEtale.DerivedCategory.constructibleFiniteTor`, preserving the recorded constructibility notion and quantification over degree-zero test modules. No uniform boundedness or Tor interval is added.
* `SystemAdjunction` presents the ordinary part of the stipulated simultaneous enriched realization: its left functor is definitionally the actual proper/open `support`, its right functor has an actual ordinary adjunction, and `finite`, `left`, `right`, `unit`, and `counit` retain the actual finite adjunction. The repaired `left_canonical` field additionally equates the underlying left comparison, on each input, with `canonicalSupportEvaluation`; the normalization is no longer free. Each `AdjointDatum` fixes the finite counit by the existing etale-origin normalization. `quotient`, `supportTransition`, `exceptionalTransition`, `projection_comp`, `quotient_comp`, and `quotient_id` retain the canonical finite coefficient maps and their coherence. This helper does not replace the right adjoint by a free map or a collection of finite lifts. The main conclusion supplies the two simultaneous realizations together, including the retained upper tower.

### Each conclusion

* `scalar_preserves` is preservation of normalization and each individual bounded constructible finite-Tor level. `T` is literally the full-subcategory restriction of `(scalarData ...).scalar.T` on the whole derived sequence site.
* `scalarEvaluation` is the specified level tensor comparison. It is built from the dependency's `scalarData.evaluation` and `scalarRealization`. The latter is uniquely specified by the actual tensor/restriction Hom adjunction and the exact localization of the identity-on-sections ordinary restriction square. Thus these comparisons have fixed normalization; they are not arbitrary isomorphisms. The source and target derived localizations have different Hom universes, which the explicit realization preserves.
* `fixedTransition` realizes the system's own strict derived transition. `red` is its actual tensor/restriction adjunct. `scalar_transition` is exactly t(TN)=T(tN) after the canonical tensor reassociation `reassociate`. `quotientMap`, `quotientMap_comp`, and `quotientMap_id` use actual composite maps, including equal indices.
* `comparison` is the full-subcategory restriction of the already defined canonical `FiniteFreeCompactComposition.coefficientComparison`; no finite evaluations enter its definition. `α.hom = comparison ...` pins down the natural isomorphism in the main theorem, including its action on every system morphism. The ambient map is the scalar mate of the canonical proper/open restriction square, hence the proper projection followed by open balancing.
* `FiniteCompatibility.change` uses the existing `FiniteCoefficientAdjoints.Change`, whose projection is normalized by `projectionAtWitness`, and whose mate satisfies both finite unit and counit equations. `canonical` equates its projection with `finiteComparison`, the fixed proper/open scalar-adjunction mate. `comparison_evaluation` spells out the system-to-finite equation with all scalar and support comparisons.
* `basisLeg` is the scalar unit followed by multiplication by the coefficient. `finite_sum` says that for EACH integral basis, reduced at EVERY level, each summand of the restricted finite comparison is compact support of that same summand inclusion followed by the canonical restriction comparison. These are exactly the inclusions characterizing finite-sum distributivity. Neither comparison nor transpose definition has a basis parameter, so the map is basis independent.
* `comparison_quotient` writes the full finite coefficient square using the actual quotient maps and tensor reassociation. It is stated on every finite constructible finite-Tor input, not just inputs arising by evaluation.
* `lambda` is precisely inverse α at E_R N followed by T_Y of the given system counit. `transpose` is `CategoryTheory.mateEquiv` on that inverse square. Thus b is a natural transformation in the actual ordinary derived-system category. `transpose_counit` and the final conjunct of the main theorem state F_S(b) followed by epsilon_S equals lambda as an entire-system equation.
* `evaluatedTranspose` writes the finite coordinate after the scalar and exceptional evaluation identifications. `transpose_evaluation` equates it with the finite `Change.mate`. The latter's `counit_equation` says exactly that it is the finite transpose of T_Y(epsilon_A) after inverse alpha; its `unit_equation` retains the same finite unit.
* `quotient_square` is the explicit square in step 7 of the node proof: Q_B(b_m), then c_B and G_B(T(t_N) after s_Y), equals s_X followed by T(c_A then G_A(t_N)) and b_n. All intermediate subcategory proofs come from the stated finite tensor preservation, and the upper quotient is the retained ramified one. The `SystemAdjunction` cocycle and identity fields retain the laws at three indices; `Change` retains both finite adjunction equations.
* The construction precedes any inverse limit and makes no claim of faithfulness of finite evaluations. In particular `comparison` and `transpose` exist before their evaluation equations are stated.

### Dependencies read and used

Read every item statement dependency and its recorded declaration/docstring. Public imports include the recorded statement modules; the two imports identified as proof-only in the return are plain imports. Conventions for morphism properties and sizes have no declaration. The following are the principal declarations actually used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded Padic integer-ring, uniformizer, quotient, and finiteness constructions.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `Sheaf.Paper.NormalizedDVRTower`, `Sheaf.Paper.FiniteTorAmplitudeSites`, and `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: the recorded ordinary-system/evaluation and finite-Tor constructibility conventions, used through their existing semilinear and fixed-module specializations.
* `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.semilinearDerivedSections`, `ScalarData`, `ScalarSystems`, `Normalized`, `derivedTransition`, `reduction`.
* `Sheaf.Paper.FiniteFreeCompactComposition`: `lowerRings`, `lowerMaps`, `upperStage`, `upperRings`, `upperMaps`, `inclusion`, `scalarData`, `support`, `coefficientComparison`.
* `Sheaf.Paper.FiniteFreeCoefficientExtension`: its shared finite-stage interfaces, re-exporting `FiniteCoefficientAdjoints.AdjointDatum`, `Change`, `ctf`, `tensor`, `lower`, `upper`; these records fix the actual finite projection and exceptional counit maps.
* `Sheaf.SixFunctors.FiniteExceptional`: quotient-comparison, identity, cocycle, and adjunction statements; `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` and `Sheaf.Paper.CartesianSectionAdjointMates`: simultaneous ordinary/enriched realization and retention of finite units/counits. The helper packages their ordinary part on the actual ramified ring tower rather than replacing it by a uniformizer-indexed tower.
* Plain proof import `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`, preserving the compactification convention; no completed limit is used in the new construction.
* `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`: `ConstantScalarRestriction.restriction`, `onDerived`, and exactness. The added transport is their coefficient-map square, uniquely identity on sections, not another constant-module definition.
* `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`: `ProEtale.compactSupportRestrictionIso`, fixing finiteComparison by the actual proper/open map.
* Proof imports: `Sheaf.Paper.QcqsCompactSupportRealization`, `Sheaf.Paper.FiniteFreeSystemRestriction`, `Sheaf.Paper.FiniteFreeDerivedScalarCalculus`, `Sheaf.Paper.EtaleCoefficientSystemAdjoint`. The last supplies the retained e(n+1) cofinality interpretation. The listed proof-only node `lem-coef-system-scalar-projection-identification` has no recorded Lean module in the read clone, so it is not imported; this item defines its comparison directly from the already recorded ambient canonical comparison and states the necessary normalization itself.
* Mathlib `CategoryTheory.mateEquiv` and its counit formula are used directly; no private mate construction.

### Sources and edge cases

The accepted node's extracted statement and all eight proof steps were read. The current blueprint is `literature/blueprint/latest` (main-20261024), not an older snapshot. The old extracted paragraph's path no longer exists there; the current corresponding sources read were `sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-compact-support.proof.md` and `det-prop-scalar-six-exceptional.proof.md` (definition/formal-properties paragraph). They specify the same proper/open order and exceptional counit transpose. No node correction was needed.

Checked n=0 corresponds to exponent 1, m=n uses actual identity quotient and normalized scalar unit, and three indices use the actual tensor-composition comparison. For e>1, B_1 remains S/v^e; no equality of uniformizer indices is imposed. E=L and i=id are allowed, including e=1. Zero systems and empty schemes are allowed; no nonempty or positive-dimensional scheme assumption occurs. Individual n-dependent cohomological/Tor bounds remain unrestricted. Rank-zero basis is not a source restriction: the quantified bijectivity premise is impossible for the nonzero DVR in rank zero, so that auxiliary summand clause is vacuous only in the mathematically impossible basis case.

### Searches made

* `msearch.py NE lem-coef-ramified-scalar-system-transpose leanfinder "Finite free scalar extension on normalized derived coefficient systems compact support exceptional adjunction transpose compatible with quotient reductions"`: eight general algebra/cotangent hits, no normalized coefficient-system match.
* `msearch.py ... loogle 'CategoryTheory.Adjunction, "mateEquiv"'`: twelve general mate results, including mateEquiv, mateEquiv_counit and mate pasting; used the existing mate API.
* `msearch.py ... grep 'semilinear.*system|mateEquiv' CategoryTheory`: twenty general mate-related hits, no system construction.
* `msearch.py ... leansearch "Finite free extension of coefficients commutes with compact support on normalized derived systems and its exceptional adjunction transpose"`: eight ordinary module/localization scalar-extension results, no exact statement.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for semilinear systems, coefficient comparisons, transpose, quotient maps, constant-scalar restrictions, and compact-support restriction: located and reused the declarations above. Exact item-id search in upstream found no existing declaration for this item. Additional source searches found the existing fixed compact-support restriction comparison used in finiteComparison.

Compilation: the complete module passed the prescribed scompile.py twice (sandbox and final library module), with no diagnostics other than allowed sorry notices. The final delivery preflight/compile is recorded by deliver2.py.

## Second reading by NE

This dispatcher assignment forbids starting another agent; the maintainer performs the independent delivery review. I re-read the source, node and full module for this audit, without representing it as an independent agent review. The audit found and repaired (1) a localization-size mismatch in the constant-scalar realization, fixed by explicit existing localizations; (2) an initially implicit basis-distributivity clause, now the explicit `finite_sum` summand equation; (3) absent explicit coefficient-quotient squares, now `comparison_quotient` and `quotient_square`; (4) absent ramified-ideal parameters, now `_he`, `_hram`, and the equality at every n; (5) geometric section variables that Lean could omit, now explicitly included. Every source hypothesis and conclusion is mapped above. No statement is marked disputed.

## Repair of returned immutable head e5a1c8520d2f

The current shared node and the retained delivered node agreed in every field other
than `lean` before this repair. No stale accepted DAG text is overwritten. The
wrapper rebases the delivery onto the current live branch. The mathematical statement,
proof, proof dependencies, and other metadata remain unchanged; the statement signature
is unchanged verbatim. This is a substantive interface repair, not an unchanged push.

### H3: canonical support evaluation

The independent maintainer review correctly exhibited the automorphism defect in the
old package. Fixing a support functor and finite adjunctions, while allowing its left
evaluation to vary together with the system adjunction, does not fix evaluation of the
scalar comparison. In particular the nontrivial minus-identity twist could change the
evaluated comparison's sign. The old unit/counit and transition fields alone did not
exclude it.

`SystemAdjunction.left_canonical` now requires, for every n and every normalized
finite-Tor input M, `((left n).hom.app M).hom =
(canonicalSupportEvaluation C τ c n).hom.app M.obj`. The right-hand side has no
SystemAdjunction parameter and cannot be changed by twisting that existential package.
Its construction is explicit:

* `compositorSupportEvaluation` is the published canonical composite of
  `SemilinearProperOpen.evalJ` and `evalR`, including their specified strict-tower
  evaluations. Its owning node is `def-pur-system-compatible-compositor-words`.
* `levelPresentation` removes the constant strict diagram by ordinary evaluation at
  zero followed by `Functor.mapDerivedCategoryCompIso`. Its underlying ordinary
  evaluation is definitionally the original level; there is no chosen level iso.
* `directOrdinary_existsUnique` fixes the constant-scalar direct-image comparison to
  the identity on every section. `directOrdinary` chooses this uniquely determined
  isomorphism. `pullOrdinary_existsUnique` pins inverse image by requiring its mate
  to equal that direct comparison. `openOrdinary_existsUnique` pins extension by zero
  by requiring its mate to equal the inverse of that inverse-image comparison.
  Consequently none of these uniquely pinned choices can absorb an automorphism.
* `directRealization` derives the same ordinary section identity, using the canonical
  right-derived composition comparisons. `openRealization` exactly localizes the
  same unit-normalized ordinary open comparison. `lowerRealization` composes these
  factors in the prescribed proper/open order. The two localization universes remain
  distinct; no equality or extra size hypothesis is imposed.
* `canonicalSupportEvaluation` pastes these three specified comparisons. Its source
  and target are precisely `support ⋙ level` and `level ⋙ lower`. The new field
  compares its underlying ambient hom with the existing restricted `left` hom.

Each added postponed assertion is named, has its complete normalization in its type,
and has a source and proof docstring matching this node's finite-evaluation proof
step. All added data definitions are real compositions or uniquely pinned choices.
No new mathematical hypothesis is added to the main statement. Once the left
comparison is fixed, the unit/counit equations identify the right evaluation with
the adjunction mate of that fixed left comparison, using the same finite adjunction.
The returned simultaneous left/adjunction twist is therefore excluded.

### H2: declaration ownership and import visibility

Added these landed owners to `stmt_deps` and read their statements, Lean records and
used declarations:

* `lem-sf-compact-support-restriction-of-scalars`: the fixed-coordinate
  `ProEtale.compactSupportRestrictionIso` in
  `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`; the current recorded
  owner module `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` is also
  imported publicly. `finiteComparison` uses the existing fixed-coordinate map.
* `lem-sfb-constant-scalar-restriction-tensor`:
  `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`, restriction, exactness,
  equivalence and `onDerived`. Both earlier scalar and new geometric realization
  helpers use this one definition of constant-scalar restriction.
* `def-weil-pbc-witness-compatibility`: `Sheaf.Paper.WitnessCompatibility`,
  `ProEtale.pbcFixedScalarExtensionComp`, the actual adjoint conjugate of coefficient
  restriction composition used by reassociation and the quotient cocycles.
* `def-weil-pbc-normalized-origin-scalar-comparisons`:
  `Sheaf.Paper.NormalizedOriginScalarComparisons`, `ProEtale.normalizedOriginScalarUnit`,
  the scalar-adjunction mate of identity restriction, used in `quotient_id`.
* `def-pur-system-compatible-compositor-words`:
  `Sheaf.Paper.SystemCompatibleCompositorNormalization`, `compositorLevel` and
  `compositorSupportEvaluation`, whose full signatures and constructions were read.
* `def-cbc-strict-constant-tower-operations`:
  `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`, modules, geometric
  pullback/direct image, their normalized adjunction, and exact tower evaluation.
* `def-cbc-strict-tower-open-extension`:
  `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`, `moduleJ` and `moduleJAdj`, the
  unit-preserving open extension used before and after exact localization.
* `def-sp-semilinear-constant-ring-operations`:
  `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`, `levelTower`, the actual
  evaluation followed by a constant strict diagram; canonical evalJ/evalR underlying
  the compositor comparison.
* `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its canonical derived
  direct-image specialization, the already supplied module geometric adjunction.

`FiniteFreeSystemRestriction` and `QcqsCompactSupportRealization` are now imported
without `public`, exactly as requested. Ownership additions only cite already landed
nodes; no dependency node or separate notion is redefined. A read-only traversal of
the added canonical-evaluation nodes' dependency closures found no path to this item.

Additional repair searches: `rg` for `compositorSupportEvaluation`, `evalJ`, `evalR`,
`levelTower`, `ConstantScalarRestriction`, `moduleJ`, `moduleDirectImage`, and derived
composition comparisons in the shared Sheaf/upstream sources. These found the reused
canonical comparison and localization APIs. No existing general direct/open transport
at these unequal realization sizes was found, so the explicitly normalized helper
comparisons above are supplied here, as the return requests.

### H11: provenance of the reading

The section headed “Second reading by NE” above is a worker self-audit, not an
independent review; it is not offered as one. L's returned independent review of
immutable head e5a1c8520d2f is the independent reading that found H3 and H2. This
repair addresses those findings and records its own further audit honestly. The
explicit dispatcher instruction prohibits starting other agents, and no other agent
was started. The maintainer's independent reading of the repaired delivery remains
the project's delivery review.

Rechecked the repaired construction for identity compactifications, empty open
immersions, zero systems, equal quotient indices, and E=L. Ordinary identities on
sections and both adjunction mates retain these cases; the new canonical field does
not impose nonempty schemes or nonzero input objects. There is still no uniform
cohomological or Tor interval. The new transport contains no independently chosen
isomorphism that could absorb the minus-identity counterexample.

## Repair of returned immutable head 0d335cc9f490

L's independent review accepted the repaired canonical-support interface and returned
H2 only. This delivery replaces exactly two statement dependencies:

* `lem-pur-system-compatible-compositor-normalization` is replaced by
  `def-pur-system-compatible-compositor-words`, the landed definition owner of
  `compositorLevel` and `compositorSupportEvaluation` in the same imported module
  `Sheaf.Paper.SystemCompatibleCompositorNormalization`.
* `lem-sf-semilinear-proper-open-mate-pasting` is replaced by
  `def-sp-semilinear-constant-ring-operations`, the landed definition owner of
  `levelTower`, `E`, and the normalized `evalR` used through the compositor, in the
  same imported module `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.

Read both definition-node statements and Lean records and reread the relevant full
signatures, docstrings and constructions in their unchanged owning modules. The
imports stay as reviewed. The theorem dependencies
`lem-sf-compact-support-restriction-of-scalars` and
`lem-sfb-constant-scalar-restriction-tensor` remain, exactly as requested, because the
used comparison objects are constructed using their conclusions. No new node or
additional Lean helper is needed. The source hypotheses, all conclusion clauses,
canonical normalization and checked edge cases remain those accepted in this review.
The node statement, proof and proof dependencies are unchanged. Outside `lean` and
`stmt_deps`, the sandbox node agrees with the current shared node. The wrapper rebases
the repaired metadata and report onto the live branch.

The Lean source is byte-identical to the retained returned delivery; SHA256:
9e77d3230c1e0bdacea9a8153dfb33ff4ed73462fffcf871703c2e0c7ac051da. The recorded statement remains verbatim its signature. This is a
substantive correction of the two ownership edges, with no change to the already
accepted Lean interface.

H11 remains explicitly advisory: NE's reading is a self-audit, not an independent
worker reading. L supplied the independent immutable-head review, including acceptance
of H3 and identification of the remaining H2 edges. No second agent is claimed or
started under the dispatcher's prohibition.
