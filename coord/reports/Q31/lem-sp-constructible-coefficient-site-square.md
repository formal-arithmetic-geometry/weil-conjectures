## Worker report

Delivered module: `Sheaf.Paper.ConstructibleCoefficientSiteSquare`.
Primary declaration: `AlgebraicGeometry.constructibleCoefficientSiteSquare`.
The module also records the two sheaf-level clauses as
`AlgebraicGeometry.constructibleCoefficientSheaf` and
`AlgebraicGeometry.constructibleSiteComparison`. All three theorem proofs are `sorry`.
Their docstrings carry the relevant steps of the seven-step DAG proof, including
constant finite presentations, tensor sheafification, restriction to the original
strata/covers, kernel/cokernel closure, and exact comparison of cohomology.
`constructibleCoefficientComplex` has actual data and applies the published ordinary
scalar functor termwise. Its additive structure comes from the published scalar
adjunction. It chooses no object or map from a postponed existence statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with the finite
  affine cover by spectra of Noetherian rings specified in the node.
- Finite commutative rings and a unital coefficient map: `(A B : Type (u + 1))`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`, `(φ : A →+* B)`.
  Coefficients and module values use the established common larger universe;
  site objects have universe u+1, site morphisms u. No equality of those universes
  or additional finiteness/flatness assumption is imposed.
- Interval: `(a b : ℤ) (_hab : a ≤ b)`.
- Complex: `C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ`.
  This is the recorded fixed-module presentation of ordinary constant-ring module
  sheaves, not condensed coefficients, an adic completion, or module objects over
  a different coefficient ring.
- Zero terms off the interval: `_hzero`, with `q < a ∨ b < q → IsZero (C.X q)`.
- Every term globally constructible: `_hcons`, using the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf`. Its actual definition existentially
  quantifies over a finite global scheme stratification and finite module models
  on an étale cover of each stratum. Constructibility of the locally closed strata
  is a field of that definition's `Scheme.Stratification`.
- Ordinary C_B with its B-action: `constructibleCoefficientComplex X φ C` uses
  `ProEtale.etaleSheafExtendScalars φ X`, which is literally
  `Sheaf.composeAndSheafify _ (ModuleCat.extendScalars φ)`.
  `ModuleCat.extendScalars` gives B tensor_A M with B acting on its B factor;
  symmetry identifies this with the source's M tensor_A B with B acting on the
  second factor. Both represent the same ordinary scalar extension. There is no
  flat model, resolution, arbitrary comparison functor, or derived tensor here.
- Every term of C_B constructible: the first conjunct of the main theorem.
  The following conjunct also gives its termwise vanishing outside [a,b].
- The original strata and covers, with value M tensor_A B: the second clause of
  `constructibleCoefficientSheaf` quantifies over the recorded
  `Scheme.FiniteLocallyClosedStratification X` and explicit constructibility of
  its strata. For every stratum k, every étale object U on it, and every finite
  original model M, a trivialization implies a B-linear trivialization on that
  same U with model `(ModuleCat.extendScalars φ).obj M`, which is also finite.
  In particular this applies simultaneously to every member of any witnessing
  cover, without replacing a stratum or refining that cover.
- N_R is the exact comparison: all occurrences are the recorded
  `ProEtale.comparisonUpperStar (ModuleCat R) X`, or its
  `mapHomologicalComplex (.up ℤ)` on complexes. `constructibleSiteComparison`
  is parameterized by an arbitrary finite commutative R, so it applies to both
  A and B. Its first conjunct is the exact intrinsic predicate
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf X R` on N_R F.
- Every witnessing nonempty partition and every original étale trivializing
  cover: the second conjunct of `constructibleSiteComparison` quantifies over
  the recorded finite locally closed partition, constructible strata, positive
  number of strata, and `Scheme.LocallyConstantDatum` on each stratum.
  `Presieve.ofArrows ... ∈ (Scheme.ProEt.precoverage ...).coverings ...`
  explicitly asserts that this same family, included by `Scheme.toProEt`, is a
  pro-étale cover. For each original constant finite model M, the following
  `Nonempty` isomorphism identifies the restriction of N_R F on precisely that
  pro-étale object with the constant sheaf on precisely M. Thus the unchanged
  stratum schemes, immersions, and subset partition witness constructibility.
- Zero-stratum input: the last clause of `constructibleSiteComparison` takes any
  recorded finite locally closed partition with `S.n = 0`, concludes `IsEmpty X`,
  and supplies `S' : Scheme.Stratification X` with `S'.n = 1`, empty domain, and
  constant zero restriction. `ModuleCat.of R (ULift PUnit)` is the explicit zero
  module. This full-stratum constant isomorphism supplies the identity
  trivialization cover, and S' includes constructibility of its single empty
  stratum. No nonempty-scheme hypothesis excludes this case.
- Q(C) and Q(C_B) bounded constructible: the two
  `Etale.DerivedCategory.isBoundedConstructible` clauses applied to
  `_root_.DerivedCategory.Q.obj` of the exact complexes. The subsequent
  `DerivedCategory.homologyFunctor` clause gives vanishing in the specified
  interval, not merely in an unspecified interval.
- Q(N_A C) and Q(N_B C_B): the next two quantified clauses apply the intrinsic
  pro-étale constructibility predicate to every derived cohomology sheaf of
  those two explicitly localized termwise comparisons, and give vanishing
  outside precisely the same [a,b]. This uses the canonical fixed-module
  encoding of the ordinary module derived categories on the two sites.
- More precise H^q(N_R C') isomorphisms: the final clause of the main theorem
  gives `Nonempty` isomorphisms of the cochain homology sheaves for both C and
  C_B, with N_R applied to the original homology on the right. These are the
  cohomology sheaves of Q by `DerivedCategory.homologyFunctorFactors`.
  This clause concerns sheaf cohomology, so it is not a replacement of a derived
  object isomorphism by only per-degree isomorphisms.
- No flatness of B/A or of C's terms occurs in any binder. No assertion equates
  this ordinary scalar extension with a left-derived scalar extension.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the equivalent scheme
  cover criterion is in `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and its maps.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and ordinary derived-category interfaces.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, including its finite model clause.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing ordinary sheaf tensor.
  `WeilConjectures.SixFunctors.ProEtale.ScalarExtension` supplies its published
  constant-coefficient specialization `ProEtale.etaleSheafExtendScalars` and
  `ProEtale.etaleSheafExtendScalarsAdjunction`; these are reused without defining
  a second scalar functor.
- `Sheaf.Paper.ComparisonPullbackExact`: `comparisonPullbackExact`, including
  exactness and its natural cohomology comparison; its public dependency
  supplies `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `ProEtale.FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`, and
  the exact canonical realization of fixed-module sheaves as modules over the
  specified coefficient sheaf. The statements use the equivalent fixed-module
  category to agree with the recorded intrinsic constructibility predicate.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, which publicly retains the
  intrinsic ringed-site predicate and includes positive size and finite stalks.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, used with the separate
  constructibility hypothesis; no extra closure condition on strata is imposed.
- Proof imports include all recorded project proof dependencies:
  `siteConstantModuleFunctorGeneral`, `etaleInverseImageModulesExact`,
  `PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses`,
  `SheafOfModules.RingedTensor.exists_inverseImageTensorComparison`,
  `ProEtale.supportSiteComparison_pullback_coherent`,
  `Scheme.proEtaleModuleRestriction_isEquivalence`,
  `Scheme.proEtaleModuleRestriction_constructible_iff`, and
  `Scheme.IsConstructibleSheaf.cokernel` (with the corresponding kernel closure).
  The Mathlib proof leaves are supplied by the module-category/sheafification
  imports, `Scheme.etalePrecoverage_le_proetalePrecoverage`,
  `DerivedCategory.homologyFunctor`, and `GrothendieckTopology.W_iff` /
  `W_iff_isLocallyBijective`.

Sources opened: Stacks etale-cohomology.tex, labels lemma-tensor-constructible
(0GKB) and lemma-constructible-abelian (03RZ), and the complete forward comparison
proof in the node's main-20261015 blueprint source. The node is a source-grounded
helper, not the blueprint unit's own statement. No statement correction or
STATEMENT-DISPUTED flag was needed; no new node or dependency replacement is made.
The historical CompactObject example module is withdrawn locally; its current
record names the upstream module, which was read for the conventions instead.

Edge cases checked before delivery: the empty scheme with zero input strata
(explicit one-empty-stratum conclusion); empty or redundant individual strata;
zero complex; a=b; zero coefficient rings; A=B and identity maps; and the nonflat
map Z/4 → Z/2, where ordinary tensor is intentionally not a derived scalar model.
No nonempty constant model is assumed on an empty étale object. Finite rings in
any universe can be represented in the common coefficient universe by lifting or
shrinking their finite carriers; neither site's object universe is collapsed.

Searches for an existing statement:

- msearch leanfinder: "Constructible etale module sheaf finite scalar extension
  preserves same finite stratification and proetale comparison bounded cohomology".
  Eight hits, all unrelated algebraic etaleness statements; no coefficient/site
  constructibility-square theorem.
- msearch loogle: "Sheaf, ModuleCat.extendScalars" returned no hits (unqualified
  Sheaf unknown); follow-up "ModuleCat.extendScalars" returned 12 useful results,
  including the ordinary functor and extension/restriction adjunction, not this
  constructibility statement.
- msearch grep: "extendScalars|changeOfRings" in
  Algebra/Category/ModuleCat/Sheaf returned its ChangeOfRings import. Direct rg
  through project WeilConjectures and Sheaf found the upstream
  `ProEtale.etaleSheafExtendScalars` and the older input-model helper, but no
  occurrence of this node's id, `CoefficientSiteSquare`, or `coefficientSiteSquare`.
  Existing input-model statements additionally assume flatness/Tor conditions
  and do not provide this arbitrary underived finite coefficient statement.
- Direct source searches read the recorded constructible predicates, finite
  stratification, comparison, cohomology, and scalar-extension signatures and
  docstrings. No private copy of any predicate or tensor functor was introduced.

Validation: the complete delivered module passed scompile.py both as the sandbox
module and under its final library module path (16.7 s and 18.6 s in the last
compile), with no errors or unexpected warnings. autoImplicit and
relaxedAutoImplicit are disabled explicitly. Every line is at most 100 characters.
Only the item's lean record differs from the base node, and its statement is
extracted verbatim from the main theorem signature. All four module declarations
are listed in lean.declarations. The prescribed dry run and delivery follow.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
