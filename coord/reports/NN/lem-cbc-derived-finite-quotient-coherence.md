## Worker report

Delivered `Sheaf.Paper.DerivedFiniteQuotientCoherence`, with the theorem
`AlgebraicGeometry.Scheme.derived_finite_quotient_coherence`. Nothing is proved:
the sole theorem has `sorry`. The two auxiliary declarations are an abbreviation
for an existing ordinary finite-target composite and the actual scalar-adjunction
mate of the already defined ordinary quotient transition. Neither selects data
from an unconstrained existence statement.

Hypotheses and objects, matched individually:

- The morphism g:T′→T is `{X Y : Scheme.{u}} (g : X ⟶ Y)`.
- The commutative Noetherian ring A and ideal I are `{A : Type (u+1)} [CommRing A]`
  and `(d : AdicCoefficientDatum A)`. The inherited `noetherian`,
  `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and `quotientFinite`
  fields retain every arithmetic assumption of the dependency node. No generators,
  completeness condition, boundedness, or invertibility of the completed coefficient
  structure map are added.
- A_T and A_T′ are `pbcAdicCompletion Y d` and `pbcAdicCompletion X d`;
  the finite ring is `reductionCoefficient _ d n`, where n encodes exponent n+1.
  Thus zero Lean index is the paper's level one, not a missing edge case.
- The universal strict reduction and pulled tower are `completedReductionTower Y d`
  and `completedTowerPullback g d`. These retain their published universal counits.
- B_n is `completedReductionFiniteTarget g d n`, followed by
  `pbcDerivedRestrict (completedReductionProjection X d n)`.
- F_0,n is exactly `completedReductionFiniteEvaluation g d n`, whose existing
  specification `HasCompletedReductionFiniteEvaluationNormalization` fixes it on
  all K-flat computations using the ordinary generator-normalized comparison.
  The theorem never quantifies over a freely chosen levelwise isomorphism.

Conclusion clauses, in the order they occur in Lean:

1. For every unrestricted derived K and every a≤b, the first conjunct is
   F_b ≫ d_B = d_0 ≫ F_a. The target arrow is the published
   `completedReductionTargetTransition` under completed scalar restriction,
   followed by `pbcDerivedRestrictComp` with the actual projection identity.
   The source arrow is `pbcTowerTransition` on the actual pulled reduction tower.
   Composition is written in Lean's left-to-right order.
2. The normalization is an identification: `IsIso
   (completedReductionTargetNormalization g d K a b h)` for every K and a≤b.
3. The prescribed formula `(x tensor r) tensor s ↦ x tensor q(r)s` is stated
   on every local inverse-image generator using `pbcTensorSection` and
   `completedReductionFiniteGenerator`. Mathlib uses scalar-first tensors:
   the resulting outer scalar is `q(r) * s`. The source reduction coefficient z
   is also reduced by its actual quotient homomorphism. Quantifying over V,U,f,z,x
   covers the generators of both inverse image and sheafified tensor; these are
   constructions, not assumptions that arbitrary sections lift globally.
4. The next conjunct identifies that ordinary balanced map with the actual derived
   target normalization, through `completedReductionFiniteModelMap` at both levels
   and `pbcComplexCounit` for the intervening coefficient extension. It holds on
   every K-flat representative. This prevents the ordinary formula and the derived
   normalization from being unrelated assertions. Flat-term K-flat models are
   included; the equation is also valid for any K-flat model.
5. The three-index clause compares the two normalizations through the canonical
   `completedReductionQuotientAssoc`, with the actual quotient cocycle proof.
6. The equal-index clause is equality to `completedReductionUnit`, the specified
   scalar unitor, for every derived K and every index, including index zero.

Dependency declarations used (signatures and docstrings read in their source files):

- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`,
  `reductionCoefficient`, `reductionCoefficientMap`,
  `completedReductionProjection`, `completedReductionProjection_comp`,
  `reductionDerivedChange`. Its arithmetic structure is defined in the public
  dependency `Sheaf.Paper.CompletedAdicCoefficientDatum`, extending
  `CompleteCoefficientDatum` from `Sheaf.Paper.CompleteCoefficientDatum`.
- `def-weil-pbc-completed-pullback` is recorded at
  `Sheaf.Paper.PbcQbarCompletedPullback.pbcQbarCompletedPull`; that module was read.
  The general strict tower construction required by this node remains published in
  its public import closure: `Sheaf.Paper.CompletedTowerPullback.completedTowerPullback`.
  The Qbar specialization is not imposed on this general adic statement.
- `Sheaf.Paper.ConstantCompletionEquivalence`: its recorded main declaration
  `CategoryTheory.ConstantCompletion.equivalence`, and the normalized finite
  interfaces `ordinaryFinitePull_existsUnique`, `finitePull_existsUnique`,
  `completedFinitePull_existsUnique`, `pullbackTowerComparison_existsUnique`.
  These are the constant/completed comparison used to construct the already
  published canonical finite evaluation map, not an identification of ambient
  constant and completed coefficient categories.
- `Sheaf.Paper.CompletedPullbackReduction`: `completedReductionFiniteTarget`,
  `completedReductionFiniteEvaluation`, `completedReductionTargetTransition`,
  `completedReductionTargetNormalization`, `completedReductionFiniteGenerator`,
  `completedReductionFiniteModelMap`, `completedReductionOrdinaryTransition`,
  `completedReductionQuotientAssoc`, `completedReductionUnit`.
  These definitions are now recorded by the new existing-definition node
  `def-cbc-completed-reduction-finite-interfaces`, cited in stmt_deps. The main
  theorem `completedPullback_reduction` is not used by this statement or its proof
  plan and is not a statement or proof dependency of this item.
- `Sheaf.Paper.BoundedConstructibleTower` in the same public import closure:
  `pbcTowerTransition`, `pbcDerivedRestrictComp`, `pbcScalarAdjunction`,
  `pbcComplexCounit`, and `pbcTensorSection`.

All already recorded proof dependencies with Lean modules are imported. The three
proof-only nodes without a recorded module (`lem-weil-pbc-flat-scalar-restriction-kflat`,
`lem-cbc-finite-constant-map-naturality`, and
`lem-cbc-derived-tower-evaluation-normalization`) are retained by name in the proof
plan; they are not needed to type this statement and are not restated here.

Edge cases checked mathematically: K=0; the empty target or source scheme;
the zero ring and I=A whenever the datum permits them; I=0; a=b; a=b=c;
repeated adjacent indices; level one (Lean index zero); arbitrary unbounded K;
and finite quotients that are not flat over the completed coefficient ring.
The constructions do not require a nonempty scheme, nonzero module, independent
choices of tower transitions, or K-flatness of quotient levels over the completion.
The site sizes remain object universe u+1 and morphism universe u, with coefficients
in u+1, following the supplied dependency interface.

Searches made:

- `msearch.py ... leanfinder "Canonical finite evaluation of derived tower pullback
  commutes with every quotient transition"`: eight ordinary adic-completion hits,
  including `AdicCompletion.transitionMap_comp_eval`; none is a theorem about
  derived module-sheaf tower evaluation.
- `msearch.py ... loogle "CategoryTheory.Functor.leftDerived_ext"`: one generic
  uniqueness theorem; it does not state the finite comparison and quotient cocycle.
- `msearch.py ... grep "finite.*[Tt]ransition|[Tt]ower.*[Ee]valuation" CategoryTheory`:
  zero Mathlib hits. A second Mathlib grep for `derived_finite_quotient_coherence|
  completedReductionFiniteEvaluation|completedReductionTargetNormalization` also
  returned zero hits.
- `rg` in `lean/WeilConjectures` for finite-transition and derived-quotient-coherence
  patterns found different ordinary algebra or unrelated finite-stage transitions.
  Searching the item id there found no occurrence.
- `rg` in `lean/Sheaf/Paper` found the canonical maps in
  `CompletedPullbackReduction`, and `adicPresentationFiniteIso_transition` in
  `AdicPullbackPresentationTransport`. The latter concerns a general presentation
  and only gives the quotient square; it does not state the complete conjunction
  of section normalization, derived computation, unit, and cocycle here.
- Read the current blueprint parent proof at
  `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`.
  The node is the finite-reduction compatibility assertion of that proof,
  with its nine-step simultaneous-resolution refinement retained in the docstring.

No statement correction, dependency module, or STATEMENT-DISPUTED flag.
Relative to current main, only `lean` and the addition of the new definition node
in `stmt_deps` change in the item copy. The Lean module is unchanged from the
returned delivery e76276c9418d.

Validation: scompile.py compiled the delivered file separately as both the sandbox
module and its actual library module, cleanly (9.5 s and 6.0 s). All universes and
variables are explicitly bound; no local notation, private declaration, or local
instance is introduced. Every line is at most 100 characters.

## Second reading by NN

A separate second pass in this worker session re-read the item and final module;
the maintainer provides the independent delivery review. The first conjunct uses
exactly the published F_0 maps, on the same strict pulled tower, and explicitly
retains the restriction-composition identification. The six conjuncts cover each
clause of the node: arbitrary K and every quotient, normalization as an isomorphism,
its tensor formula, its localization on models, the three-index cocycle, and the
equal-index identity. In particular the K-flat hypothesis occurs only in the
representative-computation clause, not on K in the square or cocycle. Re-reading
the tensor order confirmed q(r)*s and the additional reduction of z. No mathematical
mismatch was found. The compile caught two unqualified whiskering names; both were
qualified with `Functor` and the resulting module compiled cleanly. No proof was
filled and no source statement was changed.


## New nodes

`def-cbc-completed-reduction-finite-interfaces` records the ten existing general
adic constructions in `Sheaf.Paper.CompletedPullbackReduction`: finite target,
ordinary finite pullback, finite evaluation, local generator, model computation
map, ordinary and derived quotient transitions, target normalization, quotient
associativity, and unit. Its source is the finite-reduction step of the current
CBC blueprint proof, realized by the definitions preceding the module's main
theorem. The statement describes their construction, including the unique
section and K-flat normalizations, for arbitrary adic data and arbitrary K.
The record is `existing: true`: it adds no definitions, choices, theorem, or Lean
file. It depends exactly on the adic datum, completed pullback, and
constant-completion comparison nodes requested in the return.

Searches on 2026-10-21: LeanSearch and LeanFinder for "Canonical finite target and
evaluation comparison for pullback of derived adic reduction towers" returned
8 hits each, all generic pullback/ordinary completion material; Mathlib grep for
`completedReductionFiniteTarget|completedReductionFiniteEvaluation|
completedReductionTargetNormalization` returned zero hits. Their exact wrapper
records, including all returned names and digests, are copied in mathlib_searches.
DAG grep finds the theorem node and the O_E-only
`def-a1-integral-completed-pullback-interfaces`, which names only four of the finite
maps and records a different main module. Blueprint searches for "completed
reduction" and "finite evaluation" find no definition of this general interface.
Upstream WeilConjectures grep finds no names; Sheaf grep locates the definitions in
CompletedPullbackReduction and their uses in AdicPullbackPresentationTransport and
IntegralPullbackCompletedComparison. Therefore the existing module is reused and
its general definitions receive the missing DAG definition node.

## Repair of return L H2

Removed `lemma-weil-pbc-completed-pullback-reduction` from the saved packet's
stmt_deps and replaced it by the new existing-definition node above. The theorem
is not used, so proof_deps stays exactly as on main. All ten requested definitions
are listed in the new node's lean.declarations; the main signature is verbatim
from the existing source. No O_E specialization or completeness assumption is
introduced. No existing dependency node or Lean file was changed.

## Repair self-check by NN

Re-read the saved theorem's six conjuncts and the new definition node against the
full existing definitions and their normalization predicates. The general
AdicCoefficientDatum binders match; finite evaluation is the specified unique
K-flat comparison; transitions use the actual quotient maps; target normalization
is their scalar adjunct; associativity uses actual quotient composition; the unit
uses the sectionwise-identity restriction comparison. At equal indices and at
Lean index zero these are the same published constructions used by the theorem.
The new node makes no transition-coherence assertion. The earlier self-reading of
the six conclusions remains valid because the Lean file is unchanged. This is an
in-session self-check; independent review is the maintainer's. Initial saved-packet
dry run passed as 0bc701673b0, but did not detect the semantic H2 graph fault;
the repair above addresses that fault before the final compile and dry run.

Repair validation: scompile.py passed both the sandbox and library-module checks
(9.5 s and 6.0 s), without diagnostics. The current server source of
CompletedPullbackReduction matches the local source exactly. The retained Lean
file has SHA256 60b1e9617c10cb0933f6111725e2fe0cb668dafa70f589c85fe7024c469d9d6e.
