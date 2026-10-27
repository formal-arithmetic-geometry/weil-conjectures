## Worker report

Q13, 2026-10-22. Item: lem-weil-pbc-quotient-pullback-compositor-normalization.
Module: Sheaf.Paper.QuotientPullbackCompositorNormalization.
Namespace: AlgebraicGeometry.Scheme.QuotientPullbackNormalization.

The module states the ordinary and canonical derived quotient-composition equations,
both naturality assertions, and the Cartesian-square equation. Every theorem has
`by sorry`; the definitions contain actual canonical data. No node statement or
statement dependencies were changed. No mathematical dispute was found.

### Hypotheses and clauses

* The coefficient datum is `{A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)`. Its existing structure supplies the ideal and
  finiteness of every positive quotient. `Scheme.{u}` retains the small pro-etale
  site's object universe u+1 and morphism universe u. There is no universe
  identification between these sizes.
* `PerfectProjection.ring d T` is the existing inverse limit of constant quotient
  ring sheaves. `CompletedConstantReduction.residue T d.ideal n` is its quotient
  module with the projection action; `PerfectProjection.quotient d T n` is that
  module in degree zero in the ordinary derived category. The API indexes
  positive exponents by `n : ℕ`, with exponent n+1; hence Lean n=0 is the node's
  n=1. All positive exponents are covered.
* `PerfectProjection.coefficients d f` is the existing projection-normalized
  completed coefficient comparison of profinite inverse image, made an isomorphism
  using its established invertibility. The pullback and module adjunctions used
  throughout are `proEtaleRingModulePullback`, `proEtaleRingModuleAdjunction`, and
  `proEtaleRingDerivedPullback`, at these precise coefficient identifications.
* The node's a is exactly the existing `PerfectProjection.quotientPullback d f n`.
  Its defining unique-existence theorem `quotientPullback_existsUnique` specifies
  every section of its adjunct as the constant-sheaf adjunction unit followed by
  direct image of the canonical constant comparison. In particular every constant
  p is sent to the same constant p after base change. This is not a freely chosen
  isomorphism. Its scalar action is the completed quotient projection.
* `ordinary_composition` binds arbitrary `h : Z ⟶ W`, `k : W ⟶ V`, and `D` of
  precisely the ordinary direct-image-compositor type. The hypothesis `hD` fixes
  its section map as `N.val.map ((MorphismProperty.Over.pullbackComp ... h k).
  hom.app U).op`. This is exactly restriction along fibre-product pasting, not
  an extra mathematical hypothesis on the schemes. The inverse left-adjoint
  conjugate b is `(Adjunction.leftAdjointCompIso adjk adjh adjcomp D).inv`.
  The equality is b followed by pullback of a_k and then a_h equals a_kh.
  Lean composition is left-to-right, so this is the node's displayed equality
  with its two sides reversed.
* The node's q is exactly `PerfectProjection.quotientDerivedPullback d f n`,
  defined as the canonical exact pullback/single-complex comparison followed by
  the degree-zero image of a. It is an isomorphism in the ordinary derived
  category over the completed ring, not just a cohomology-level comparison.
* `derived_composition` includes `hc`, the equality of the composite completed
  coefficient identification with `coefficients d (h ≫ k)`. The equality lives
  in a proposition, so its existential packaging does not choose extra data.
  `eqToIso (congrArg ... hc.symm)` supplies precisely the coefficient transport
  at the source of `proEtaleCanonicalDerivedPullbackComparison`. That comparison
  retains the actual adjunction-unit, sectionwise direct-image, termwise and
  flat K-flat representative characterizations. The stated composite is c,
  followed by Lh*(q_k), followed by q_h, and equals q_kh, for every positive level.
* `transition_naturality` binds `n m : ℕ` and `hnm : n ≤ m`. Its two conjuncts
  use the existing `quotientModuleMap` and `quotientMap`; they assert the ordinary
  and derived commuting squares for every transition from level m+1 to n+1.
* `system_naturality` binds another datum `e : AdicCoefficientDatum B` and an
  arbitrary natural transformation `φ : d.ringTower ⟶ e.ringTower`. These are
  the morphisms of the finite coefficient systems in the node. No map A→B
  inducing φ is assumed. `systemRingMap` takes its actual limit of constant-sheaf
  level maps using `limMap`. `systemModuleMap_existsUnique` fixes the quotient
  map on every section to be exactly the constant-sheaf map of φ_n; the
  definition selects that uniquely determined map. `systemRestriction` restricts
  along the actual completed map; its limit/colimit instances reuse the existing
  exactness results. `systemDerivedMap` applies degree zero and the canonical
  exact-restriction/single-complex comparison. The first and second conjuncts
  express ordinary and derived naturality with the canonical scalar-restriction
  pullback comparison. `systemRingMap_square` supplies its required completed
  coefficient square. These are helpers of this node's naturality clause.
* `cartesian_square` binds four arbitrary schemes, all four arrows, and
  `sq : ChosenCartesianSquare g' f' f g`. It uses the same d at all corners.
  `PerfectProjection.coefficients_square d f sq` is the existing canonical
  equality of completed coefficient routes. The formula uses
  `proEtaleAmbientRingedPullbackComparison ... .inv.app (quotient d Y n)`:
  this is exactly theta = theta_square inverse, in the direction from
  L(g')*Lf* to L(f')*Lg*. Both q-composites have the required common target.
  There is no properness hypothesis and no assumption that an exchange map is
  invertible; only the pullback compositor is inverted.

### Dependencies and published declarations

The six statement-dependency records and their declarations/docstrings were read.

* `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, its `ringTower`
  and `positiveQuotient_finite`, and the completed coefficient interface
  (recorded main declaration `completedReductionTower`). The chosen constant
  presentation is the already published `CompletedConstantReduction.residue`
  and `adicLisseCompletedRing`, reexported through PerfectProjectionFormula.
* `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image`, `proEtaleConstantComparison`,
  `proEtaleProfiniteComparison`, and the inverse-image composition comparison.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: its publicly retained
  general `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedPullback`. These are the
  arbitrary ring-sheaf operations, not only the constant-ring specialization.
* `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, the recorded alias
  of `proEtaleCanonicalPullbackComposition`. The module is imported for the
  proof's normalized-compositor characterization. The actual expression uses
  `proEtaleCanonicalDerivedPullbackComparison`, publicly retained by the next
  recorded dependency, whose ordinary and K-flat characterization is the same.
  The two canonical selections are determined by that characterization; no
  arbitrary comparison is substituted. This proof import is not reexported:
  making this broad module public perturbed imported derived-category universe
  instance search; plain import and the existing public general interface compile.
* `Sheaf.Paper.CondensedAmbientExchange`: publicly retains
  `proEtaleAmbientRingedPullbackComparison` and
  `proEtaleCanonicalDerivedPullbackComparison` from the general ringed interface.
  The statement uses that actual ring-sheaf interface, not condensed module objects.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`,
  including its commutative square and chosen fibre-product identification.

Additional existing definitions reused from `Sheaf.Paper.PerfectProjectionFormula`
are `PerfectProjection.ring`, `modules`, `derived`, `quotient`, `coefficients`,
`pullback`, `quotientPullback`, `quotientPullback_existsUnique`,
`quotientDerivedPullback`, `quotientModuleMap`, `quotientMap`, and
`coefficients_square`. This reuses the parent module's published constructions
rather than introducing a duplicate notion. The parent currently contains private
composition lemmas; those private statements do not provide a public declaration
for this node. If the parent's proof is later refactored to import this node,
its shared quotient constructions will need to remain below both modules to
avoid an import cycle. This delivery introduces no current import cycle.

`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` supplies the canonical
scalar-restriction comparison used by system naturality. Mathlib supplies
`Adjunction.leftAdjointCompIso`, `limMap`, `NatTrans.ofOpSequence`,
`DerivedCategory.singleFunctor`, and `Functor.mapDerivedCategorySingleFunctor`.
Proof imports retain composite-adjunction/mates, constant-sheaf/sheafification,
localization and the existing K-flat-resolution module from the node's proof plan.
No proof-only import is omitted.

The source text was checked at Stacks `sites-cohomology.tex`,
`lemma-derived-pullback-composition` (0D6D), and the current blueprint
`main-20261015/.../lemma-weil-pbc-perfect-projection-formula.proof.md`, third
paragraph. The eight-step DAG proof is rendered in the individual theorem
proof docstrings: constant adjunct uniqueness, ordinary conjugation,
K-flat normalization and localization, exact-single compatibility, naturality,
and cancellation of the two pullback compositors for the square.

### Edge cases

Read against identity morphisms, identity Cartesian squares, the first quotient
(Lean n=0), identical transition levels, the zero ring, unit ideal (zero quotient),
and empty schemes. No `Nonempty`, nonzero-ring, flat-quotient, properness or
exchange-invertibility hypothesis is introduced. Arbitrary finite-system maps
include identities; the canonical restriction comparison handles differing
completed rings. Derived composition does not assume the quotient itself K-flat:
the proof plan compares compositors on K-flat resolutions before specializing to
its degree-zero object. The site's object and morphism universe sizes remain
u+1 and u; the coefficients are Type (u+1), as required by the existing datum.

### Searches

Prescribed `msearch.py Q13 <item>` calls:

* LeanFinder: `Section normalized quotient coefficient module pullback
  isomorphisms commute with ordinary and derived pullback composition`.
  Eight hits, including `Scheme.Modules.pullbackComp`,
  `PresheafOfModules.pullback_assoc`, `Scheme.Modules.pseudofunctor_associativity`,
  and `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`.
  These are general ordinary comparisons, not the completed quotient statement.
* Loogle: `SheafOfModules.pullbackComp, CategoryTheory.Adjunction.leftAdjointCompIso`.
  Zero hits. The relevant generic `leftAdjointCompIso` source was read directly.
* Mathlib grep: `leftAdjointCompIso|mapDerivedCategoryNatIso_comp`.
  Fourteen hits in the sheaf/presheaf pullback and adjunction-composition sources.
  None states the normalized quotient and derived-square assertion.
* LeanSearch: `Canonical normalized quotient module pullback comparisons commute
  with ordinary and derived composition and Cartesian square comparison`.
  Eight hits: `Limits.pullbackComparison`, the `MorphismProperty.Over.pullbackComp`
  family, `SheafOfModules.pullbackComp`, `Scheme.Modules.pullbackComp`.
  No whole-node match.
* `rg` searched both `lean/WeilConjectures` and `lean/Sheaf` for quotient/compositor
  and canonical derived-comparison names; the required literal item-id search in
  WeilConjectures returned no match. The parent module's private quotient
  composition calculations and public quotient definitions were read in full.
  General canonical-composition and ambient-square definitions and their
  normalization characterizations were also read. No public existing declaration
  states all clauses, so this is not an existing-declaration delivery.

### Validation

The completed module compiled through the prescribed `scompile.py` in both the
private sandbox and live-library configurations, with no errors or unexpected
warnings. Diagnostic probe files are not delivered. Dry-run and delivery results
are appended below after the wrapper checks.

## Second reading by Q13

The dispatcher expressly forbids starting other agents and assigns independent
review to the maintainer. This is a fresh self-reading of the actual node and
module, not a claim of an independent second worker review.

I checked the node's ordinary equation against `ordinary_composition`: b is the
inverse conjugate, hD is the exact section-restriction normalization, and all
three a maps are the existing uniquely normalized maps. I checked the derived
equation against `derived_composition`: the coefficient equality transport is
included before the canonical comparison, and both quotient endpoints use the
ordinary derived categories. I checked both parts of naturality: arbitrary
quotient transitions appear in both degrees, and arbitrary natural transformations
of the two quotient systems use restriction along their actual limit map. I
checked the square direction separately: the node asks for the inverse ambient
comparison, and the statement uses `.inv.app`, not `.hom.app`. All four schemes
and all arrows are arbitrary apart from the chosen Cartesian-square datum.
No properness or invertibility of exchange entered. Positive exponent indexing
is uniformly shifted by one and includes the first level. No mismatch requiring
a node correction was found. Explicit standard derived-category instances in the
single-complex helpers and a non-reexported composition proof import repaired
elaboration issues without changing any mathematical hypothesis or conclusion.

Validation result: `deliver2.py Q13
lem-weil-pbc-quotient-pullback-compositor-normalization --no-push` printed
`OK (dry run): commit 5b1cca7f0ad passes the preflight and compiles; nothing pushed`.
The packet contains exactly this report, the item's lean-only node record, and
the single statement module.
