## Worker report

Item: det-prop-diagonal-tower-limit, group NV, stage 2, 2026-10-18.
Source read: main-20261015/sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.md and its proof, all three clauses and all proof
paragraphs; the node's seven expanded proof steps. The statement is unchanged.
No statement dispute was found. The file is Sheaf/Paper/DiagonalTowerLimit.lean.
Its three statements are diagonalCompletedTwist_limits (clause 2),
diagonalTower_directImage (general assertion of clause 1), and
diagonalTower_limit (the endpoint assertions and clause 3).

Hypotheses and objects:

- ell is a prime: `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive quotient exponents are
  indexed by n+1, exactly as in DiagonalTowerSystem; every positive exponent
  appears, and exponent zero is not silently substituted for exponent one.
- The standing setting is `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] (hpℓ : p ≠ ℓ)`, with `[Y.Over (Spec (.of k))]` and finite-type
  (LocallyOfFiniteType and QuasiCompact) and IsSeparated instances for its
  structural morphism. These are the hypotheses of sk-def-sfb-dc-setting.
  The twist statement uses an arbitrary X in that setting. The direct-image
  statement uses X and Y in that same setting and a morphism f over k.
  `hY : IsUnit (ℓ : Γ(Y, ⊤))` supplies the existing
  diagonal-system API's invertibility proof; it follows from the field setting
  and introduces no mathematical restriction.
- W, Delta, the supported integral constant, and the positive boundary are
  exactly diagonalSurface, diagonalImmersion, diagonalIntegralSource and
  diagonalIntegralBoundary from the dependency; there is no new Cartier class.
- The HasDerivedCategory and HasExt instances choose the existing unbounded
  localization and Ext size conventions, at u+1, as in the dependency. They
  impose no boundedness condition. All universes and variables are explicit.
- D, hcompletion, hsystem are the simultaneous derived reduction, completion
  specification, and normalized strict-cycle specification supplied by
  exists_diagonalTowerSystem. The conclusion unpacks exactly the original
  H, roots, a, b, c and all their finite normalization witnesses before stating
  the completed class; no new witness structure or dependency repair is used.
- DiagonalCompleted is the category of modules over purTwistZlCompletion,
  not modules over the discrete constant ring. diagonalCompletedSource is the
  actual ringed direct image of the completed coefficient unit on the diagonal,
  restricted along diagonalCompletedCoefficientMap. That map is the real
  limit lift of the finite constant-section inverse-image comparisons; no
  equality of inverse-image and completed coefficient rings is assumed.
  diagonalCompletedCodomain is purTwistZlModule in degree zero shifted by two.
  diagonalCompletedRestriction restricts along purTwistZlCompletionMap, uses
  constantCommuteCompose, then the published constantRingModuleRestriction.
  It does not replace a completed-coefficient arrow by an arbitrary additive one.

Clause-by-clause rendering:

1. `DiagonalRightDerived` records the universal total right derived pair, its
   unit and K-injective computation. `DiagonalRlim` adds projections normalized
   by the actual ordinary-limit projections on complexes. Thus Rlim is the
   total derived limit on the strict tower category, not an unspecified functor
   or merely limits of objects of the derived category.
   In diagonalTower_limit, `s₀` identifies the underlying completed supported
   coefficient with the ordinary source-tower limit; its composites are
   normalized by diagonalCompletedGenerator and the ordinary quotient unit π_n.
   The retained DiagonalSourceNormalization witnesses identify this with
   cartierProIntegralGenerator at every finite level.
   The generator is uniquely determined by n mapping to n times one on every
   locally constant integral section. `t₀` identifies the completed root line
   with the ordinary root limit, normalized by `preservesLimitIso` and roots.
   `IsIso (diagonalSourceLimitMap ...)` and `IsIso (diagonalTargetLimitMap ...)`
   are the two claimed derived-limit identifications. These maps are constructed
   from the ordinary-limit comparison through the derived unit and the exact
   existing source and signed Kummer isomorphisms, including the canonical
   shift comparison. They are not freely chosen endpoint isomorphisms.
   In diagonalTower_directImage, Rt is the derived functor of ordinary
   levelwise lowerStar (whiskeringRight). The isomorphisms e give evaluation
   of Rt as Rf on the evaluation, and c gives Rf after Rlim as Rlim after Rt.
   c₀ is fixed by limit.post; the unit equation fixes c, the K-injective equation
   fixes e, and the last equation retains all projection compatibilities.

2. diagonalCompletedSheafTwist is the published siteSheafTensorRight with
   coefficientTwistLine and the completed root line; positive one uses the line,
   negative one its actual internal dual. diagonalCompletedTwist is derived
   tensor with that same line in degree zero, using
   siteDerivedTensorIndependentCoefficients. The hypothesis `d = 1 ∨ d = -1`
   selects the two stated twists. diagonalCompletedTwist_limits asserts
   additivity and preservation of finite limits and finite colimits on sheaves
   (ordinary exactness), and ClosedSupportLimitFunctorProperties on unbounded
   derived categories. That existing record explicitly includes product
   preservation, triangulated exactness, preservation of every Roos
   homotopy-limit triangle, and invertibility of its canonical comparison.

3. In diagonalTower_limit, `δ` has precisely the completed-coefficient source
   and target, in D(W_proet, completed Z_l). Both endpoints satisfy the
   intrinsic principal-ideal derived-completeness criterion: maps from every
   P on which ell is invertible form a subsingleton. This is the criterion
   retained by DiagonalCompletionSpec, and does not change the meaning of
   sk-def-pe-derived-completion to ordinary sectionwise completeness.
   The equation for `∃! δ` says its entire underlying constant-coefficient map
   is L.R applied to D.T applied to the positive integral boundary, under the
   two canonically normalized endpoint comparisons. The completion assertion
   is therefore precisely hcompletion for that boundary. The retained equation
   for c.hom identifies this with Rlim c_bullet. Uniqueness is with respect to this whole
   map, not uniqueness from separate finite reductions (which is not asserted).
   DiagonalCompletedReduction specifies the real simultaneous derived quotient
   by its left-derived counit and ordinary quotient units. The final universal
   assertion gives isomorphisms from the completed finite reductions to the
   evaluated strict reductions; their two equations fix them against the
   canonical quotient units and limit projections. Its final map equality
   identifies the reduction of δ with the evaluated boundary. By
   the retained equation for c.hom and the retained normalized finite source/root
   identifications and cycle-class equality, this is exactly
   cartierResidueReducedPro, the torsion cycle class; the full arrow and its positive Cartier/Kummer sign are retained.

Dependency declarations read and used:

- Sheaf.Paper.DiagonalTowerSystem:
  exists_diagonalTowerSystem, DiagonalCompletionSpec, DiagonalDerivedReduction,
  DiagonalCycleSystemSpec, diagonalDerivedSingleCounit, DiagonalSourceNormalization,
  diagonalIntegralBoundary, diagonalIntegralSource, diagonalSurface,
  diagonalImmersion, diagonalFiniteToPadic and diagonalForget (all in
  AlgebraicGeometry.ProEtale). The existing specification was read in full.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField supplies
  the recorded standing finite-type/separated field setting; the framework
  source is the shared clone, per coord/pefw-upstream-framework.md.
- Sheaf.Paper.ProEtaleTateTwistsOfUniverses:
  AlgebraicGeometry.ProEtale.spComplexTwistOfUniverses, with its imported
  ProEtaleTateTwists and completed coefficient declarations. The actual signed
  line is WeilConjectures.coefficientTwistLine from CoefficientTwistsDetailed.
- Sheaf.SixFunctors.ProEtale.DerivedCompletion:
  AlgebraicGeometry.ProEtale.IsDerivedComplete; the endpoint assertions use
  its intrinsic ell-complete meaning through the criterion in the already
  recorded DiagonalCompletionSpec, since its continuous coefficient module
  category is not definitionally the constant-scalar strict-system category.
- Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit:
  AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit, including the
  integral limit clause specialized to Q_l.
- Sheaf.CategoryTheory.ConstantRingModuleSheaves:
  CategoryTheory.constantRingModuleRestriction, owned by the existing definition
  node def-sfb-constant-ring-module-restriction. The equivalence theorem
  constant_ring_module_sheaves is not used in the statement.
- Sheaf.Paper.FormalClosedSupportIILimits:
  AlgebraicGeometry.ProEtale.CondensedRing.ClosedSupportLimitFunctorProperties.
  Its record was read through both sequential_limits and comparison_isIso.
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed:
  Scheme.proEtaleRingedDirectImage, proEtaleSheafInverseImage and proEtaleBaseChange.
- Proof dependencies with published modules are imported for stage 3:
  RingedTowerPushforwardLimitComparison,
  RingedStrictTowerHomotopyLimitIndependentCoefficients,
  ProEtaleMilnorEpimorphic, ConstantCompletionEquivalence,
  AdicCompletionReduction, and the upstream UpperLowerStar.ClosedImmersion.
  PurTwistSheafLocallyFree and RingedToposMorphism are also explicitly imported;
  their stated proof routes are retained in the docstrings.
  sk-lem-integral-models has no recorded Lean module to import; its role in
  uniqueness is stated in the complete natural-language proof.

Edge cases checked before writing: empty Y is allowed (all sheaves and maps
restrict to the unique empty-site data); no connectedness or global choice of
compatible primitive roots is imposed. ell=2 has the same positive roof and
signed Kummer convention; the shift is 2, and neither sign is suppressed.
The first level n=0 is quotient ell, never quotient one. No boundedness or
finite-generation assumption is imposed on strict towers or on complexes.
The direct-image comparison includes identity maps and arbitrary strict systems
in the standing setting.
The negative twist is the dual line; no global trivialization was assumed.
Uniqueness concerns the whole restricted arrow and permits no inference from
objectwise equality of finite reductions.

Searches: msearch.py NV det-prop-diagonal-tower-limit leanfinder
"derived inverse limit diagonal cycle class completed Tate twist" returned
unrelated BDeRham/adic-completion results, no matching theorem. Loogle
"DerivedCategory" returned the generic derived-category declarations.
Mathlib grep "TateTwist|diagonal.*cycle|derivedCompletion" in AlgebraicGeometry
returned no match. rg of the upstream WeilConjectures and shared lean/Sheaf
for "diagonal.*(TowerLimit|towerLimit|Completion)|det-prop-diagonal-tower-limit"
found only a source citation in IntegralRestrictionLine, no declaration of the
present statement. The full existing recorded dependency signatures and
source docstrings were opened. Searches for completed coefficient maps found
CompletedTowerPullback.completedCoefficientMap, which uses the distinct
pbcAdicCompletion presentation. The present helper uses that same canonical
finite-comparison/limit-lift construction for the existing purTwistZlCompletion,
with proEtaleConstantInverseImageMap rather than an arbitrary map.
Mathlib's existing derived-single comparisons,
exact-functor derived construction, and ordinary limit comparisons are reused.

## Return repair (H2)

Compared with returned immutable head f44b7fa314b1, this packet removes the four
unneeded dependency modules and their node copies: lem-coef-derived-system-evaluation-calculus,
lem-sp-cartier-reduction-site-comparison, def-coef-ringed-sequence-site, and
def-weil-derived-pullback-tensor-hom. It also removes the unused public import of
Sheaf.Paper.CoefficientRingedSequenceSite. No theorem signature or helper data changes.
The maintainer's independent tests established that the item compiles against base;
these timeout optimizations therefore do not belong to this statement delivery.

Against the current main DAG, stmt_deps is exactly its original five entries plus
def-sfb-constant-ring-module-restriction and def-sfb-cartier-reduction-data.
The first owns the literal constantRingModuleRestriction construction, and the
second owns cartierResidueReducedPro, cartierProRootMap, and cartierResidue_cast.
Both definition nodes already have existing:true records, and neither node nor
its module is copied or modified here. The unused equivalence and Cartier
site-comparison theorem nodes are not added. Statement, proof and proof_deps
are identical to the current base. No new nodes or dependency modules remain.

The canonical completed coefficients purTwistZl*, the existing
ClosedSupportLimitFunctorProperties and the finite geoCartier* objects are
reused from the imports already recorded above. Their mathematical roles were
checked in the self-reading; this repair adds no replacement definition.

## Second reading by NV

This section is the worker's own self-check; the maintainer supplies the
independent review. I reread the full saved DiagonalTowerLimit module, the
current DAG statement, and both blueprint statement and proof files. Clause 1
retains source and target comparisons fixed by units, ordinary limit maps and
root projections, plus the general direct-image comparison normalized by
limit.post and by the K-injective computation. Clause 2 uses the same derived
tensor formula as spComplexTwistOfUniverses, and retains exactness, products
and the canonical homotopy-limit comparisons for the line and its dual.
The CommShift witness is existential because the following properties are
relative to that shift compatibility. Clause 3 retains completed coefficients,
the Hom criterion for derived completeness, uniqueness of the whole underlying
arrow, and finite reductions fixed by quotient units and limit projections and
identified with cartierResidueReducedPro. No separate-reduction uniqueness is
claimed. The finite-type separated positive-characteristic field setting,
ell distinct from its characteristic, is unchanged. The empty scheme, ell=2,
identity direct image and first positive exponent remain covered.

The maintainer's substantive review of f44b7fa314b1 found these clauses sound,
including both HEq normalizations (each rfl-provable in the recorded probe).
The present repair only removes the unused import and dependency repair files,
and corrects dependency ownership. The recorded main signature is still verbatim,
autoImplicit is false, and the file retains explicit universe declarations.

## Validation

The required initial dry run was started on the saved five-module packet before
editing. The corrected packet contains one Lean file and one item node only;
validation uses scompile.py and deliver2.py --no-push against the current base.
Exact outcomes are recorded below after those tools complete.

The corrected single module compiled cleanly through scompile.py: sandbox check
45.7 seconds and library-module check 44.5 seconds, against the base dependencies
without any of the removed dependency modules. No errors or warnings were emitted.

Resumed-packet self-check (2026-10-18 UTC): the initial required dry run passed
preflight and per-file compilation against the current base, producing dry-run
commit 1c01892aab. I checked the saved module against the current node and the
blueprint statement and proof again. The only node-field deltas remain lean and
stmt_deps; the latter is exactly the live five plus the two definition owners
requested in H2. The saved main signature matches lean.statement verbatim.
The single remaining module has no CoefficientRingedSequenceSite import, and
there are no dependency node/module copies in the packet. The standing setting,
canonical limit comparisons, signed tensor functors, completed-coefficient
endpoints, whole-arrow uniqueness and normalized finite reductions agree with
the earlier substantive review. No further Lean edit was needed. The existing
repair note is resolved stage 1 and requires preserving this statement and plan;
both are unchanged. This is a worker self-check, not a second independent review.
