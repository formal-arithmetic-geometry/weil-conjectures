## Worker report

The module Sheaf.Paper.ConstantTowerDirectImageNormalization states all four clauses
of lem-sf-cbc-constant-tower-direct-image-normalization, with sorry proofs only.
Its namespace is AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.
The canonical maps mentioned in the statement are constructed in this module;
all choices retain a universal property or a unique representative formula.
No mathematical statement correction is made.

Hypotheses and objects:

- `A : Type (u+1)` and `[CommRing A]` give the coefficient ring in the chosen
  sheaf universe. `d : CompleteCoefficientDatum A` contains the Noetherian,
  finitely generated ideal, additive-torsion quotient and perfect positive-power
  quotient hypotheses, exactly as recorded by that dependency. There is no
  completeness, finite quotient set, flat quotient or constructibility assumption.
- `X Y : Scheme.{u}` and `f : X ⟶ Y` allow every scheme morphism. The existing
  `coefficients A X`, `Modules A X` and `Towers A X` retain the small pro-etale
  site's object universe u+1 and morphism universe u, with coefficients/modules
  in u+1. The chosen ambient universe may always contain a given ring and scheme.
  No equality of the two site universes is imposed.
- `DerivedCategory (Modules A X)` is the ordinary unbounded localization;
  `Derived A X` localizes the strict functor category `ℕᵒᵖ ⥤ Modules A X`.
  Index n denotes the paper's positive index n+1. `delta` is exact diagonal,
  `ev` is exact derived evaluation, `L` is the existing K-injective right-derived
  strict inverse limit, `push` and `R` are K-injective derived module and strict
  termwise direct image, respectively.
- `quotient` and `quotientStep` are the actual sheafified ring quotient maps.
  `level` uses the existing ordinary scalar extension and restriction. The uniquely
  pure-tensor-normalized `step_existsUnique` makes `reductionModule` one strict
  diagram. `ReductionModel` packages the universal derived pair and its K-flat computation.
  `reduction` is its universal left derived functor, retaining its counit. This is delta M tensor the whole coefficient
  tower, as explained in the reduction existence and main theorem docstrings.
- `augmentation` is the specified i, constructed using `Functor.leftDerivedLift`
  and the retained universal property. Its homotopy factorization is the strict
  quotient unit x maps to 1 tensor x. Its ordinary predecessor is uniquely
  normalized on all sections at every index, so no arbitrary map is selected.
- `limitPush` is the adjunction conjugate of the identity-component diagonal
  pullback square, fixing the common-direct-image comparison a with its ordinary
  units; `evalR` is the published normalized evaluation mate.

Clauses of the conclusion:

1. `chi A f : push A f ⋙ delta A Y ≅ delta A X ⋙ R A f` is a natural
   isomorphism constructed from canonical universal derived composition maps and
   the ordinary identity-component `Functor.compConstIso`. The first conjunct of
   `constantTowerDirectImageNormalization` gives its explicit K-injective formula:
   `IsDirectImageNormalizedOnKInjectives` spells out this equation for arbitrary abelian
   categories, then the main statement instantiates it with the published module
   and tower operations. After the exact diagonal localization factor and
   K-injective direct-image comparison, chi is the localized ordinary
   identity-component square. The predicate quantifies over every K-injective
   complex J, hence every chosen representative
   of every M. `delta_preservesKInjective` supplies the exact-terminal-evaluation
   argument needed to make the formula well typed.
2. The second conjunct applies `ev A Y n` to chi and then the existing `evalR`,
   followed by direct image of `deltaEval`. It equals `deltaEval` of Rf M.
   Thus, under precisely the evaluation identifications, the map is identity.
3. `deltaLimit` is the inverse of the canonical diagonal/derived-limit adjunction
   unit; `deltaUnit_isIso` states its invertibility for every unbounded object.
   The third conjunct starts with Rf of deltaLimit inverse, applies a=limitPush,
   L of chi inverse, and deltaLimit on Y, and asserts that this endomorphism of
   Rf M is `𝟙 _`. This writes both source and target transports explicitly.
4. `ordinaryReductionPull` is uniquely fixed on all inverse-image pure-tensor
   generators and is a strict-tower natural isomorphism. `reductionPull` retains
   its equation on K-flat representatives using both reduction counits.
   `IsReductionPullAt` spells out the canonical homotopy-category equation
   abstractly, then specializes to these module categories and counits.
   `projection` is its actual counit adjunction mate under the existing normalized
   module/tower adjunctions. This is the diagram-site projection-formula map h
   with its source identified by chi: the comparison transposed is exactly the
   quotient-tensor/pullback comparison (07A4). The fourth conjunct is
   `i_(Rf M) ≫ h = chi ≫ R(i_M)`, equality in the derived category of strict
   towers before evaluation or inverse limit. The main proof docstring explicitly
   identifies this mate with the counit-tensor construction and its unit
   normalization of ringedProjectionMateExact (0B56).

Dependency declarations read and used:

- Sheaf.Paper.CompleteCoefficientDatum: Scheme.CompleteCoefficientDatum,
  together with its named ideal and coefficient hypotheses.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory and the standard localization.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective:
  CochainComplex.IsKInjective, with QuasiIso for representatives.
- Mathlib.CategoryTheory.Functor.OfSequence: Functor.ofOpSequence.
- Mathlib.CategoryTheory.Products.Basic: Functor.constCompEvaluationObj.
- Sheaf.CategoryTheory.DiagramSiteRealization: exists_diagramSite_realization,
  used for the diagram-site interpretation; no second sheaf category is defined.
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses:
  ringedStrictTowerHomotopyLimitOfUniverses, original-site K-injective Rlim.
- Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison:
  ringedTowerPushforwardLimitComparison. Its equal-site-universe signature is
  imported as proof infrastructure; the main maps are constructed directly on
  the original site by the canonical adjunction conjugate, without specializing
  that signature at incorrectly equal universes.
- Sheaf.Paper.ProjectionMateExact: SheafOfModules.ringedProjectionMateExact,
  supplying the natural counit-tensor construction and tensor-unit normalization.
- Sheaf.AlgebraicGeometry.StrictConstantTowerOperations:
  AlgebraicGeometry.ProEtale.StrictTower.coefficients, Modules, Towers, Derived,
  modulePullback, moduleDirectImage, towerPullback, towerDirectImage, G, R, adj,
  ev, evalR and constantRingIso. Its already-landed node
  def-cbc-strict-constant-tower-operations is added to stmt_deps as permitted by
  the standing brief's STMT_DEPS MAY GAIN LANDED NODES rule.
- Sheaf.Paper.CompletedRlimFunctor: completedRlim and completedTowerLimit.
- Sheaf.Paper.AdicCoefficientDatum, reexported by CompletedRlimFunctor:
  reductionChange, reductionRestrict, reductionTensorSection.
  These helpers take arbitrary coefficient sheaf maps; no AdicCoefficientDatum
  with finite quotients is supplied or assumed.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations and the public module
  operations: proEtaleRingModuleAdjunction and proEtaleRingDerivedAdjunction.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp and
  MapDerivedCategory: normalized rightDerivedFunctorNatIso, composition
  comparisons and the comparison of exact functors with their right derivatives.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
  Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
  Sheaf.CategoryTheory.KInjectiveTotalDerived and
  Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses supply the
  recorded proof plan and independent-universe representative interfaces.
  The proof dependency lem-pe-constant-left-module-inverse-image has no published
  declaration in its record; the exact arbitrary-constant-ring operation is
  already provided by StrictConstantTowerOperations and its imported canonical
  ring-sheaf operations. No finite-ring restriction is substituted.

Edge cases: zero derived object; zero coefficient ring; unit ideal, whose positive
quotients and reductions are zero; zero ideal, giving constant quotient diagrams
whenever the datum's torsion condition holds; level n=0 (positive exponent one);
identity morphism; empty schemes; arbitrary unbounded complexes and arbitrary
nonproper morphisms. Neither proof nor signature assumes countable products exact,
a uniform bound, coefficient-set finiteness, separatedness or Noetherian schemes.
Both sides of the augmentation equation are strict derived tower maps, so equality
of evaluations alone is never used as a replacement for the requested equality.

Searches for existing declarations (2026-10-17):

- msearch.py leanfinder, query "derived direct image constant strict tower normalized
  inverse limit projection formula augmentation": eight unrelated LightProfinite,
  InverseSystem and eventually-constant-limit hits; no matching theorem.
- msearch.py leansearch, query "derived direct image commutes with constant inverse
  systems and quotient augmentation": eight unrelated constant-sheaf/forgetful,
  direct-limit and exact-functor shift-comparison hits; no matching theorem.
- msearch.py loogle, query "CategoryTheory.Functor.rightDerivedFunctor,
  CategoryTheory.Functor.const": zero hits, service rejected the upstream identifier.
  This is recorded as unavailable, not evidence of absence.
- msearch.py grep, query "constant.*tower|direct.*image.*constant" in CategoryTheory:
  zero Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for constant towers, constant direct image,
  and this exact node id: found generic constant-completion/derived-comparison
  infrastructure and the published strict operations, but no four-clause theorem.
  Read ConstantCompletionEquivalence, CompletionMateComparison and
  ProEtaleConstantReductionTower: the first two use an equal-universe small site;
  the last's quotient interface requires finite quotient sets. The present helpers
  specialize the existing scalar constructions directly on the original small
  site for precisely the datum here, without either extra assumption.

No STATEMENT-DISPUTED flag. The source's missing blueprint paragraphs are already
accurately documented in proof_origin/split_report. The implementation follows the
agent-supplied Stacks-based proof there; it does not claim those paragraphs exist.

## Second reading by Q16

The dispatcher explicitly prohibits starting other agents. This section records
an in-thread second pass against the node and source, not an invented independent
worker review. The maintainer performs the independent review of this delivery.
The pass checked each datum field, the two site universes, the positive-index
reindexing, the direction of chi and both transports in clause (3), and all four
normalizations. It also checked that projection is a specified adjunction mate
rather than an arbitrary map, and that reduction needs no finite quotient sets.
The second pass found Mathlib's exact `Functor.constCompEvaluationObj` for
constant-tower evaluation. The final module uses that declaration directly,
instead of constructing a second ordinary evaluation isomorphism.

The generic normalization predicates contain the full equations; they do not add
assumptions to the item. Abstracting their category variables prevents repeated
kernel expansion of the large concrete sheaf-module categories. The quotient
augmentation itself uses the universal `leftDerivedLift`, without a postponed
existence theorem for an arbitrary map.

## Validation

The prescribed scompile.py wrapper compiled both the sandbox and actual module
under the 60-second per-file limit with no errors or warnings (29.0 and 10.6
seconds for the final source check). All diagnostic heartbeat settings and
`#exit` commands were removed. Final declaration names follow the predicate
naming convention; all variables and all universes are explicitly bound.
