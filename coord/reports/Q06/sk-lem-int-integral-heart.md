## Worker report

The module `Sheaf.Paper.IntegralConstructibleHeart` states
`AlgebraicGeometry.ProEtale.integral_constructible_heart`, with `sorry` as its whole
proof. It introduces no definitions or auxiliary theorems. The saved module and node
record were retained after the interrupted attempt; the missing report is completed here.
The node copy differs from the current shared node only in `lean`, whose `statement`
is the signature verbatim. The UTC date is 2026-10-18.

Source read: blueprint main-20261015, sec-six-functors-basics,
`sk-lem-int-integral-heart/_section.md` (all three assertions) and
`sk-lem-int-integral-heart.proof.md` (all five paragraphs and torsion example).
The current node supplies the standing finite-type integral-model hypotheses.
Its four proof steps are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The characteristic is
  `(k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)`;
  `(_hℓ : ℓ ≠ p)` gives the required distinct characteristics. These are actual
  hypotheses, not implicit prime-to-characteristic assumptions on an unrelated ring.
- A finite extension of Q_ell is `(E : Type v) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E]`. The coefficient universe v is independent of u.
  The recorded `integralHeartCoefficientRingObj ℓ E` uses the small presentation of
  E, its canonical spectral-norm valuation ring, and continuous functions; it is
  the completed coefficient ring, rather than the constant discrete coefficient ring.
  No choice of uniformizer occurs in any conclusion, so the coefficient construction
  needs no uniformizer binder. The source's uniformizer is only used to prove the
  assertions by the adic and length-one-resolution arguments.
- The scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with separatedness,
  local finite type, and quasi-compactness of its structure map. These give precisely
  separated finite type over k and imply the source's Noetherianity; an additional
  independent `[IsNoetherian X]` is not imposed.
- Clause (1), full triangulated subcategory: the existing
  `constantModelBoundedConstructible` is an object property defining a full
  subcategory. The first two conjuncts are its closure under isomorphisms and
  `ObjectProperty.IsTriangulated`. Boundedness is
  `DerivedCategory.TStructure.t.bounded K`; stability under both standard
  truncations is quantified over every `n : ℤ`, using `truncLE n` and `truncGE n`.
- Clause (1), identification with degree zero: the inclusion of
  `IsConstantModelConstructible` followed by `DerivedCategory.singleFunctor _ 0`
  is Full and Faithful. Its essential image is exactly bounded constructible
  objects satisfying both `t.le 0 K` and `t.ge 0 K`. Thus the identification
  concerns all degree-zero objects, not just a one-way implication for singletons.
- Clause (1), abelian subcategory: `Nonempty (Abelian (ConstantModelConstructible ...))`
  supplies the abelian structure; `IsClosedUnderKernels` and
  `IsClosedUnderCokernels` refer to the ambient module category. Extension closure
  is `ObjectProperty.IsClosedUnderExtensions`, and smallness is
  `EssentiallySmall.{u + 1}` for that same full subcategory.
- Clause (2): for every constructible `C : SmallAdicCompletion.Modules ℓ E X`,
  the final conjunct supplies one `s : Scheme.FiniteLocallyClosedStratification X`
  and explicitly says its strata are constructible subsets. For each stratum a,
  there is a `Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a)` and for
  each chart a scalar module `N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)`
  satisfying `Module.Finite`. The displayed isomorphism restricts C along the
  composite chart-to-stratum-to-X and compares it with the existing canonical
  completed scalar extension `integralHeartRealization`. There is no free,
  projective, torsion-free, or flat hypothesis on N. N may depend on the chart.
- Clause (3): inside the same quantifier over `a : Fin s.n`, after its local-model
  assertion, an object `D : integralHeartDerivedCategory ... (s.domain a)` has
  `Nonempty (ExactPairing D C_restricted_in_degree_zero)`. Mathlib ExactPairing
  contains evaluation, coevaluation, and both triangle identities. In the symmetric
  derived tensor category this is a dual of the restricted C. This conclusion
  holds over the entire stratum, not merely over its covering charts. The next
  conjuncts are `DerivedCategory.torAmplitudeIn _ (-1) 0` for the restricted C and
  `DerivedCategory.torAmplitudeIn _ 0 1 D` for that same dual. The existing Tor
  predicate tests tensor against every ambient module sheaf placed in degree zero.
  The node asks for the existence of a dual, so no particular chosen internal-Hom
  realization is imposed. In a closed symmetric category these duals are canonically
  isomorphic to RHom(C, unit).

Dependency declarations and their source signatures/docstrings were read:

- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `ConstantModelConstructible`, and
  `constantModelBoundedConstructible`. The recorded scalar-model definition is
  used throughout, rather than upstream arbitrary local finite-presentation models.
- `sk-lem-integral-models`: `Sheaf.Paper.IntegralModels`, `integral_models`,
  including its hypotheses, coefficient categories, completeness equivalence,
  constructibility criterion, operation preservation, and generators. Imported
  without `public` for the proof route; its specialized embedded-coefficient
  theorem is not used as the definition of the more general coefficient field.
- Stated proof dependency `det-lem-int-integral-heart-triangulated`:
  `Sheaf.Paper.IntegralConstantModelHeart`, `integralHeartCoefficientRingObj` and
  `integralConstantModelHeart`. The first portion of the statement uses its exact
  coefficient construction and heart interface.
- Stated proof dependency `det-lem-int-integral-heart-local-model`:
  `Sheaf.Paper.IntegralHeartLocalModel`, `integralHeartScalars`,
  `integralHeartRealization`, `integralHeartDerivedCategory`, and
  `integralHeartLocalModel`. The current server source was also read with
  `scompile.py --source Sheaf.Paper.IntegralHeartLocalModel`; it agrees with the
  recorded local source. Its small coefficient ring abbreviates the same valuation
  ring construction as `integralHeartCoefficientRingObj`.
- `det-lem-int-integral-heart-dualizable` has no Lean record yet and contributes
  only a future proof, not a notion needed to type this statement. Its statement
  was read; no import for an unrecorded module is invented.
- Mathlib `CategoryTheory.ExactPairing` in `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`
  is the existing evaluation/coevaluation interface. Upstream
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` defines the exact
  all-module Tor-amplitude predicate used here.

Edge cases checked: the empty scheme permits a stratification with no strata, so
all stratum conditions are vacuous without requiring a nonempty index. The zero
sheaf is admitted, with the zero finite module as model and zero derived dual.
Torsion is admitted: the DVR quotient by a uniformizer has a length-one free
resolution in degrees [-1,0], and its derived dual is the quotient shifted by [-1],
with Tor amplitude [0,1]. No underived module dual is substituted. Arbitrary
integer truncation degrees, arbitrary coefficient-field universes, and varying
finite modules across different covering charts are retained.

Searches retained from `searches.jsonl`:

- LeanFinder: "Bounded constructible integral adic complexes form a triangulated
  category with an essentially small abelian heart and dualizable stratified finite
  module local models". Eight generic derived-category results, including
  `DerivedCategory.instIsTriangulated` and `DerivedCategory.TStructure.t`; no exact match.
- Loogle: `"ExactPairing"`. Twelve hits including `CategoryTheory.ExactPairing`,
  its evaluation/coevaluation, and congruence constructions. This existing interface
  is used; it does not state the integral constructible theorem.
- Mathlib grep: `integralHeart|[Cc]onstructible.*[Dd]ualiz|[Cc]onstructible.*[Aa]belian`.
  Zero hits.
- LeanSearch: "Integral constructible sheaves have an essentially small abelian
  heart and finite stratifications with dualizable restrictions of Tor amplitude
  minus one to zero". Eight ambient sheaf/derived-category results, including
  `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`; no exact match.
- Source `rg` searches for `integral_constructible_heart`,
  `sk-lem-int-integral-heart`, and integral-heart/constructible-dualizability names
  in the upstream WeilConjectures tree found no exact theorem. Project `lean/Sheaf`
  searches found the recorded partial heart and local-model modules, and consumers;
  the combined theorem is absent. These existing partial notions are imported.

Self-check: the file has `autoImplicit false`, explicit universes u and v, one
named sorry theorem, source and proof docstrings, and no lines above 100 columns.
The saved lean.statement was compared literally with the source signature and matches.
No mathematical statement fault or STATEMENT-DISPUTED condition was found.

Compilation status: the first required scompile invocation exited 75 before
elaboration, reporting `INFRASTRUCTURE RETRY (stale live olean)` for
`Sheaf.Paper.IntegralHeartLocalModel`: its published live object file does not exist.
The source is available through the prescribed --source interface. No launcher
script, live source, artifact, or shared-repository file was modified.

The subsequent `deliver2.py Q06 sk-lem-int-integral-heart --no-push` retried the
required compile and failed with the same missing published live olean diagnostic
in 1.2 seconds. It explicitly printed `COMPILE FAILED on the server, nothing pushed`.
Thus no delivery commit or push has completed, and the packet is retained for a
retry after the dependency's compiled artifact is published. Repairing this requires
library publication or a compiler-overlay correction outside the worker's authority;
restating or modifying the dependency would not repair a published-build failure.

## Dependency modules

The live build had no published object files for three already-recorded dependency modules,
so their declarations were unusable to the stage-2 compiler even though the exact source
was available. The delivery includes each source unchanged and changes only the dependency
node's `lean.note` to record this infrastructure defect and the supplied exact interface:

- `def-sfb-small-coefficient-derived-completion` —
  `Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion`, declaration
  `AlgebraicGeometry.ProEtale.SmallAdicCompletion.IsDerivedComplete` (with its recorded
  coefficient, reduction, and completion helpers). This is the module imported by
  `IntegralHeartLocalModel` whose published object was missing.
- `sk-lem-integral-models` — `Sheaf.Paper.IntegralModels`, declaration
  `AlgebraicGeometry.ProEtale.integral_models` (and its recorded helper declarations).
  The item imports this module directly and the published object was missing.
- `det-lem-int-integral-heart-local-model` — `Sheaf.Paper.IntegralHeartLocalModel`,
  declaration `AlgebraicGeometry.ProEtale.integralHeartLocalModel` (and all recorded
  scalar, realization, derived-category, and local-model helpers). Its published object
  was the first missing artifact reported by the dry run.

Each dependency module states exactly the notion in its DAG node; no declaration body or
statement was changed. Compiling these three sources in dependency order followed by
`IntegralConstructibleHeart.lean` is clean, with only the expected `sorry` declaration
warning suppressed by the project options.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
