## Worker report

Module: `Sheaf.Paper.CompletedPullbackUnitTower`.
Main theorem:
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.completedPullbackUnitTower`.
This repair addresses F1 and F2 of the return on immutable head 276b455111f3.
The saved packet's initial dry run passed at 430c629df4; that mechanical pass did
not resolve the mathematical findings. The previous claims that a seed from bare
Nonempty data was canonical, and that clause (iii) already stated the recorded
completed-ring arrow, were incorrect. They are removed from this report and the
Lean record. No new nodes or dependency modules are needed.

Hypotheses and objects, matched to the corrected node:

- `A : Type (t + 1)` and `[CommRing A]` give the commutative coefficient ring.
  `d : CompleteCoefficientDatum A` supplies Noetherianity, its finitely generated
  ideal `d.ideal`, additive torsion of A/I, and perfect positive-power quotients.
  Their module finiteness is automatic because the quotient is cyclic. No finite
  underlying set is assumed.
- `{T' T : Scheme.{t}} (g : T' ⟶ T)` is an arbitrary scheme morphism.
  `site T` uses `proEtaleSiteModel T = AsSmall.{t+1} T.ProEt` and
  `proEtaleModelTopology T`. This transports the pro-etale topology and enlarges
  only its Hom universe; the original site has object universe t+1 and Hom t.
- `inverse`, `direct`, and `adjunction` are the actual sheaf inverse image,
  continuous direct image and adjunction of `proEtaleModelBaseChange g`.
  `inverse_finiteLimits` postpones only the proof of geometric left exactness.
- `transportedRingInverseImage` and `transportedRingDirectImage` are the actual
  CommRingCat sheaf functors on these same models. `transportedRingUnit` is their
  adjunction unit after forgetting commutativity. `transportedModuleInverseImage`
  is Mathlib's `SheafOfModules.pullback` along that unit, exactly the small-model
  construction used in the recorded `proEtaleModuleInverseImage`.
- `ringUnderlyingMap` is the set-adjoint of the ring adjunction unit;
  the module underlying comparison is pinned by requiring its set-adjoint to
  equal the underlying actual module pullback adjunction unit. Thus both
  comparisons refer to actual units, not unspecified isomorphisms.
  `constantInverseImageMap` is the ring-adjoint of the constant-section map from
  the sheafification unit, the formula of `proEtaleConstantInverseImageMap` on
  these models and in the full coefficient universe t+1.
- `canonicalInverseImageData_existsUnique` pins EVERY nonproof field: ring
  functor equality, the hom of every ring underlying isomorphism, the module
  functor for every ring, the inverse components of its underlying natural
  isomorphism, and each constant comparison hom. The remaining operation graph,
  naturality and inverse-law fields are proofs. HEq handles dependent codomains
  until the preceding ring/module equalities are substituted. This determines
  the whole data up to equality. `canonicalInverseImageData` selects only from
  this unique predicate. `algebraicLiftSeed` and the old unprovable claim about
  the rings of an arbitrary witness have been deleted. All these declarations
  now have Source/blueprint docstrings. The existence theorem has a complete
  construction/uniqueness proof plan in its docstring.
- `morphism g` uses precisely these data. Its `.pull A` is the exact module
  inverse image, localized to the ordinary unbounded derived category. Its
  `.towerPull A` first acts on strict towers, then localizes.
- `(site W).derived A` uses the standard Mathlib derived category of modules
  over the constant ring. `.towerDerived A` derives the strict functor category
  `ℕᵒᵖ ⥤ (site W).modules A`, not a diagram of derived objects. Level n is
  positive exponent n+1.
- `.reduction A d.ideal` is the dependency's universal derived quotient
  presentation, with its comparison on flat-term K-flat complexes. Its strict
  representative is the tower Q tensor P_n with the actual quotient transitions.
  `.completion` and `.unit` use that presentation and the fixed total right
  derived strict limit; no replacement completion unit is introduced.

Clause (i) is the witness `b : C ⋙ R ≅ R`. Its first conjunct is
`b.inv.app N = R.map (eta.app N)` for EVERY derived N. Its second conjunct
identifies evaluation of `b.hom.app N`, via `finiteEvaluationIso`, with restriction
of `finiteInverse`. The latter is the scalar-extension adjunct of
`finiteProjection`. That projection is evaluation of the fixed delta/derived-limit
adjunction counit, followed by the finite quotient coefficient comparison. Thus it
retains the quotient action and the specified projection normalization.

Clause (ii) is the witness q of natural isomorphisms of derived strict towers.
Its component is `b.hom.app ((morphism g).pull A |>.obj K)` followed by the inverse
of `reductionPullIso`. The latter is the dependency's canonical comparison, with
its tensor-insertion and K-flat representative normalization, so its inverse is
the required tau, independent of Q. K is arbitrary. Naturality and quotient
transitions belong to these strict-diagram morphisms before evaluation.

Corrected clause (iii) retains completeness only in the last conjunct:
`(site T).IsComplete A d.ideal K`. It compares evaluation of q, through
`targetEvaluation` and `finiteEvaluationIso`, with scalar restriction of
`finitePullbackProjection`. This definition is EXACTLY the finite scalar-extension
adjunct of R lim(tau), then the actual limit projection, then the finite target
comparison. It is the constant-coefficient alpha specified in the corrected node.
It does not identify it with `completedPullbackReductionArrow`. Its finite
coefficient invertibility follows from q and conservativity of scalar restriction;
this is explained in proof step 6 and the corrected DAG proof. The projection
normalization itself holds for arbitrary K by (i)/(ii); retaining the complete-K
form of (iii) matches the source's completed inverse-image formulation.

Dependency declarations used (module: name):

- `Sheaf.Paper.CompleteCoefficientDatum`: `Scheme.CompleteCoefficientDatum`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  `CategoryTheory.sheafificationAdjunction`, `CategoryTheory.toSheafify`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `ConstantCompletion.completedPullbackAdjunction`.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `InverseImageData`, `underlying`,
  `quotientPresentation`, `completion`, `completionUnit`, scalar adjunctions and
  derived finite comparisons. Its bare `inverseImageData_exists` is NOT used.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSiteModel`,
  `proEtaleModelTopology`, `proEtaleModelBaseChange` and continuity. Its
  `proEtaleModuleInverseImage`, `proEtaleModelRingUnit` and constant map formulas
  were read and are applied in their small-model coordinates here, so arbitrary
  model ring sheaves and arbitrary coefficient rings of universe t+1 are retained.
- `Sheaf.Paper.ProEtaleConstantReductionTower`, publicly importing
  `Sheaf.Paper.CompletionMateComparison`: `AdicSites.Site`, `Morphism`,
  `Site.deltaAdjunction`, `finiteAdjunction`, `finiteEvaluationIso`,
  `Morphism.reductionPullIso`, `evaluatePullIso`, `finiteRestrictionPullIso`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullback`, `pullbackPushforwardAdjunction`.

Proof-only imports retain the DAG plan: independent-coefficient K-flat resolutions
and change of rings, site tensor descent, ringed tensor comparison construction,
K-flat preservation, the strict K-injective limit and adic-completion reduction.
The completed-ring coefficient pullback/reduction imports were removed because
corrected (iii) uses the constant-coefficient construction.

Edge cases checked: zero ring and zero objects, I=0 and I=A, empty scheme/site,
identity g, arbitrary noncomplete N and K in (i)/(ii), and unbounded complexes.
The units pin the same constructions in identity and empty-site cases. The unique
predicate does not demand equality to an arbitrary chosen presentation. Positive
exponents start at one. For I=0 the quotient tower is constant, and for I=A its
levels vanish. A=F_p(t), I=0 is permitted: the quotients are perfect rank-one
modules with additive p-torsion and infinite underlying sets. No boundedness,
constructibility, smoothness, properness, or quotient-set finiteness is added.

Searches retained from the saved packet:

- `msearch.py` LeanFinder: "Derived completion unit is inverted by the strict
  reduction tower functor; its inverse under pullback is normalized by finite
  quotient projections": eight ordinary adic algebra completion results,
  including `AdicCompletion.factorₐ_evalₐ_one`; no derived strict-tower match.
- `msearch.py` Loogle: `"completion", "tensor"`: twelve ordinary module completion
  tensor results, no matching theorem.
- `msearch.py` grep in Mathlib/CategoryTheory:
  `completion.*unit|strict.*tower`: no hits.
- `msearch.py` LeanSearch: "Derived completion unit becomes an isomorphism after
  applying the strict derived quotient tower functor": generic derived-category
  localization results, no match.
- `rg` in WeilConjectures, the upstream names index and lean/Sheaf for this node,
  `completedPullbackUnitTower`, and `CompletedPullbackUnitTower`: no existing
  theorem at the original investigation.
- Repair search: `rg` for ringUnderlying, moduleUnderlying, proEtaleModuleInverseImage,
  proEtaleCoefficientInverseImageMap and proEtaleModelRingUnit found the recorded
  algebraic data structure and canonical small-model constructions. Mathlib's
  PullbackContinuous was read in full, including the exact adjunction signature.
  No existing unit-normalized InverseImageData specialization was found.

Sources read for the repair: the returned module and node; the current shared
node, its sole citer, and the dependency interfaces above; current main-20261015
fix-lem-exchanges proof; Stacks proetale.tex lemma-naive-completion (099M) and
lemma-pushforward-Noetherian-case (099N), especially (2),(5).

## Statement corrected

The old clause (iii) was:

> If K is derived I-complete, then under the constant/completed coefficient
> equivalence and its finite-reduction comparisons
> [lem-weil-pbc-constant-completion-equivalence], which identify C(Lg*K) with the
> completed pullback of [def-weil-pbc-completed-pullback], the level-n component
> of q is the projection-induced isomorphism alpha_n of
> [lemma-weil-pbc-completed-pullback-reduction].

The full old statement is saved verbatim in `statement_change.old_statement`.
Its completed-ring declarations require AdicCoefficientDatum and cannot be applied
under this node's weaker coefficient datum (the infinite F_p(t) example above).
The previous Lean RHS was a different, constant-coefficient adjunct. The correction
now says exactly which constant-coefficient projection-induced alpha is meant,
following Stacks 099N(2),(5), and records its adjunct formula. It preserves every
hypothesis and (i)/(ii). It removes the two inapplicable completed-ring statement
and proof dependencies, saves all changed fields verbatim, and rewrites only the
last proof step accordingly. This is a refinement lemma, not a blueprint unit's
own statement.

Every direct statement/proof citer was found by the node-id search and parsed
membership check (one):

- `lem-sf-cbc-compact-support-composition-limit`: holds FALSE for its recorded
  proof use. Its stated constant-coefficient q and concatenation comparisons
  survive: its inverse-image letter is explicitly C_U u* and its single-letter
  q is exactly (i)/(ii). However, the proof's completed-inverse-image step also
  invokes old (iii) to identify q_n with the completed-ring reduction alpha.
  Corrected (iii) no longer supplies that extra inference. The citer owner must
  repair or remove that proof sentence; the citer is named here and not edited.

## Second reading by Q70

I reread the final node and file after making the repair. This is the worker's
self-check; the maintainer supplies the independent review. F1 is repaired by
removing the seed and pinning all five types of data components to independently
constructed ring/module pullbacks and unit/constant maps. The HEq predicates compare
actual maps and functors; they no longer compare F to a bare chosen witness.
Source/blueprint docstrings are present for every new helper and chosen datum.
The only postponed proofs are inverse_finiteLimits,
canonicalInverseImageData_existsUnique and completedPullbackUnitTower, each a
named theorem with proof plan in this node/module. All definition data are real.

For the theorem: the original coefficient hypotheses and site universes match;
(i) quantifies all N and fixes b.inv to R(eta), and its finite inverse is the
adjunct of the actual projection; (ii) quantifies all K, fixes q=b followed by tau,
and keeps the strict diagrams; (iii) alone assumes completeness and now matches
the newly explicit constant-coefficient adjunct in the corrected node. F2 is
repaired with the source-based statement_change and sole-citer audit above.
The final audit also read the citer's proof, not only its statement, and found
its explicit invocation of the old completed-ring identification. That use is
marked holds:false even though its stated constant-coefficient construction
survives. The Lean statement field is extracted verbatim through its final
signature token.

Validation of the repaired packet: scompile.py compiled both sandbox and library
modes with exit 0, no errors and no warnings (12.5 s and 18.2 s). No global build
was run. The module has no line over 100 characters and autoImplicit is false.
The changed JSON fields are exactly statement, stmt_deps, proof, proof_deps,
statement_change and lean; proof_deps equals the union of uses in the proof.
