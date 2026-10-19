## Worker report

Item: `lem-zl-specified-hom-scalar-evaluation`, group NK, 2026-10-18.
Module: `Sheaf.Paper.SpecifiedHomScalarEvaluation`.

The module has two concrete helper definitions and six statements, all theorem proofs
`by sorry`. Together they state the node, including the representative normalization,
not merely existence of some Hom isomorphism. The node's statement is unchanged. No
new nodes, dependency modules, or statement corrections are needed.

### Hypotheses and objects

* `l : ℕ` with `[Fact l.Prime]` is the coefficient prime. `D : FiniteFieldDatum`
  supplies `p`, `a`, `D.prime`, `D.exponent_pos`, the field of cardinality `p^a`,
  and its fixed algebraic closure `D.k`. `_hl : l ≠ D.p` is the distinctness condition.
* `X : Scheme`, `[X.Over (Spec (.of D.k))]`, and instances `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` on its structure morphism render precisely
  a separated finite-type scheme over that closure. The finite-field datum is the
  existing one from `Sheaf.Paper.FiniteFieldFiber`, not a private copy.
* `E`, `L` are fields with `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances;
  `ι : E →ₐ[ℚ_[l]] L` renders the inclusion. This uses the library's finite field
  models and their actual embedding, rather than imposing a particular carrier in
  the algebraic closure. Every finite inclusion in the node admits this model and
  every such embedding can be realized inside an algebraic closure. No unrelated
  scalar map is supplied. Rings, chosen uniformizers, quotients and their transition
  maps are those of `Padic.coefficientExtension*`.
* The common ambient universe `u` is arbitrary. The small site has objects in `u+1`
  and morphisms in `u`; completed rings and modules have size `u+1`. This does not
  identify the site's object and morphism universes. It follows the existing
  `sfIntegralConstructible` and normalized scalar-operation interfaces.
* `integralTowerModules l E X` is the existing module category over the completed
  integral sheaf, not modules over the discrete constant integer ring.
  `integralDerivedInternalHom` unfolds to the recorded `derivedInternalHomOfUniverses`;
  `integralOrdinaryDerivedScalar` is exact ordinary derived extension;
  `integralScalarExtension` is the recorded strict Roos construction.
* `hM`, `hN : sfIntegralConstructible ...` impose exactly derived completeness,
  constructibility of every positive reduction, and the one common finite interval.
  No boundedness or constructibility is imposed on the ambient Hom for the integral
  comparison. Constructibility of that Hom is required only by the rational pair domain.

### Each conclusion and normalization

1. `specifiedHomScalarEvaluation` first asserts `IsSfDerivedComplete` of the ambient
   Hom, then `IsIso` of each of the three specified completion components. Its next
   clause is exactly `χ_H ≫ θ.hom = c ≫ H.map (χ_M.inv.op, χ_N.hom)` in Lean's
   left-to-right composition notation. Here `θ` is the existing
   `scalarHomCompleteInputs`, the same `scalarHomCompleted` used in
   `integralHomScalarComparison`; its proof arguments are irrelevant.
2. The last clause applies the inverse of `CoefficientClosedStructure.transpose`
   to the identified specified map and equates it with the inverse normalized
   `scalarClosedTensor` comparison followed by scalar-extended evaluation. This API
   uses Hom tensor input, just as the recorded finite-free Hom base-change theorem
   does. The node's input tensor Hom convention is the equivalent Koszul-swapped
   expression. It introduces the same `(-1)^(degree(input)*degree(Hom))` in both routes.
3. `specifiedHomIdentified` is a concrete composite of the specified Hom map and
   its three canonical completion identifications. It is not a fresh Hom comparison.
   `scalarCompletion` is uniquely normalized on good representatives by
   `integralScalarCompletionChain`, whose quotient tensor coordinates and zero shifted
   coordinates are the same canonical units used by the finite-free comparison node.
   Different presentations of ordinary derived extension are compared canonically;
   no arbitrary isomorphism of limit objects enters the statement.
4. `specifiedHomScalarChain` takes flat-term K-flat `P,Q` via
   `integralOperationsGoodComplex`, any K-injective `I`, and a quasi-isomorphism
   `q : Q ⟶ homComplex P I`. The objects represented by `P,I` are constructible as
   in the node. It asserts a **unique actual chain map** δ to Hom of extended P into
   the fixed replacement of extended I. For every degree `r,m`, site object `U`,
   sections `x,y`, and target scalars `s,b`, its component equation says exactly
   `δ(x tensor s)(y tensor b) = j(q(x)(y) tensor (s*b))`. Evaluation uses the actual
   `coefficientHomComponent` at the identity slice object. Scalars are arbitrary,
   not restricted to constants or to one.
5. The second clause in that unique-map predicate is its actual localization square.
   It uses the fixed Hom factorization, the source Hom map induced by the fixed
   K-injective augmentation, the ordinary derived scalar factorization, and the target
   Hom factorization. Thus the chain formula is identified with `scalarHomOrdinary`
   before inserting completion units. The source Hom need not itself be K-flat:
   that is precisely why the arbitrary good resolution `Q` and its `q` remain.
   The source K-injective `I` is not assumed to remain K-injective after extension.
   `specifiedHomResolutionUnit` supplies the actual existing replacement augmentation
   using the same Grothendieck-abelian witness as `coefficientHomResolution`.
6. `specifiedHomScalarCoherence` gives the identity equation with the normalized
   multiplication unit, and quantifies over every further finite extension `F` and
   embedding `j` for the direct/successive comparison equality. The successive second
   map is `scalarHomOrdinary`, i.e. the identified map from the main theorem. The
   associator is the prescribed `integralOrdinaryDerivedScalarComp`. Its pure-section
   formula and the δ formula give the node's common `h(m)` with the product `bss'`;
   passing to input-first order inserts the same Koszul sign on the two routes.
7. `specifiedHomScalarRationalEvaluation` is the displayed integral equality after
   cancelling the Hom-output completion unit and applying the **raw** localization
   functor. The endpoints are the existing permitted constructible Hom objects.
   Its right side is the localized conjugate of the actual ordinary evaluation
   transpose, not an unspecified rational comparison.
8. `specifiedHomScalarRational` identifies the actual `rationalHomScalarComparison`
   with localization of `integralHomScalarComparison`. It then states naturality
   for arbitrary arrows `a,b` in the raw rationalized categories, with the required
   contravariance of `a`. No integral lift or pure-tensor representation is assumed.
9. `specifiedHomScalarRationalCoherence` gives the explicit rational identity and
   tower equations, using the already specified `sfRationalScalarUnit` and
   `sfRationalScalarComp`. The pair domain imposes precisely bounded constructibility
   of the integral Hom, as required by the final sentence of the node. No idempotent
   completion or perfectness is assumed.

### Dependency declarations read and reused

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting `Padic.coefficientExtension*`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `Scheme.ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the imported unrestricted completed sheaves.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its localization factorization.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`,
  `nonempty_derivedChangeOfRingsCochainModel`; ordinary extension here is its exact
  finite-free specialization, using `integralOrdinaryDerivedScalar`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and its normalized resolving-class comparison;
  the equal-ambient-universe `integralScalarExtension` is the retained specialization.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its full category.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarComparison`, `completedScalarChainComparison`,
  `finiteFreeCompletedScalarComparison`, including the zero shifted coordinate.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarCompletion`, `scalarCompletionIso`, `scalarIntegralClosed`,
  `scalarIntegralModels`, `scalarClosedTensor`, `scalarHomOrdinary`,
  `scalarHomOrdinary_isIso`, `scalarHomCompleted`, `scalarHomCompleteInputs`,
  `scalarInternalHom_complete`, and the ordinary unit/tower statements.
* `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleIntegralHomPairs`, `constructibleIntegralHom`,
  `integralHomScalarComparison`, `constructibleRationalHomPairs`,
  `rationalDerivedInternalHom`, `rationalHomScalarPair`, `rationalHomScalarComparison`,
  and `commonStageDerivedInternalHom_existsUnique` (the comparison's actual consumer).
* `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`:
  `CategoryTheory.ringedFiniteFreeHomBaseChange`, especially its normalized transpose
  and its documented Hom-first convention.
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension`; these are raw scalar localizations.
* `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
* `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
* `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`, `homComplex_exists`, with its product projections and differential.
* `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, its `evaluation`, `transpose`, `tensor`,
  `CoefficientTensorModels` and actual sheafified pure-tensor generators.
* `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `coefficientHomComponent`, `coefficientHomResolution`, `coefficientHomResolutionIso`,
  `coefficientHomSectionEvaluation`.
* Existing coherence declarations are reexported by the dependency modules:
  `integralOrdinaryDerivedScalarUnit`, `integralOrdinaryDerivedScalarComp`
  (`Sheaf.Paper.ScalarExtensionComposition`) and `sfRationalScalarUnit`,
  `sfRationalScalarComp` (`Sheaf.Paper.SfScalarExtensionComposition`).

### Source and edge checks

Read the node's statement and all eight proof steps, each statement dependency and
its Lean record, the recorded declarations and docstrings, and the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/def-weil-derived-pullback-tensor-hom.md`.
The comparison construction of the integral-operations dependency fixes the exact maps.

Checked: `E=L` and identity embeddings; arbitrary further finite embeddings, including
ramified ones; zero inputs and empty schemes; unbounded/nonconstructible ambient Hom;
negative Hom and input degrees; the Hom-first versus input-first Koszul sign;
arbitrary site-local scalars; arbitrary K-injective source representatives and good
Hom resolutions; raw rational morphisms with denominators in either variable.
No hypothesis that the Hom is perfect or constructible enters the integral statement.
No mathematical statement fault or unresolved dispute was found.

### Searches

All wrapper searches are recorded in the sandbox's `searches.jsonl`.

* `msearch.py ... leanfinder`, query “The specified completed internal Hom scalar
  extension comparison is the evaluation transpose”: 8 hits, ordinary ModuleCat
  evaluation/change-of-rings statements, none the completed derived assertion.
* `msearch.py ... loogle`, query
  `CoefficientClosedStructure.transpose, derivedInternalHomOfUniverses`: no hits;
  service reports the side-project name unknown, so source inspection was used.
* `msearch.py ... grep`, query
  `scalarHomCompleted|coefficientBaseChangeHom|completedScalarComparison`: no Mathlib hits.
* `msearch.py ... leansearch`, query “Derived internal Hom commutes with finite free
  scalar extension and its evaluation map”: 8 hits, ordinary tensor/Hom and categorical
  evaluation declarations, none the strict completed scalar comparison.
* `rg` in Mathlib, the named upstream `WeilConjectures` tree, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: all eight delivered declaration names absent.
  Upstream node-id search finds no declaration of this item. Source searches in
  `lean/Sheaf/Paper` found the normalized comparisons and raw rationalizations reused
  here; none states their representative identification and all clauses of this node.

Validation: every delivered module is checked through `scompile.py`; final dry-run
preflight and delivery results are recorded below after they run. No global build,
direct Git mutation, live source edit, or launcher-script edit is performed.

## Second reading by NK

Author's clause-by-clause recheck, under the dispatcher's direct-delivery workflow;
the maintainer supplies the independent reading. The node and complete module were
open together. The recheck retained each global hypothesis in the main theorem,
all three completion maps, the fixed rather than arbitrary K-injective augmentation,
the quasi-isomorphism from a good Hom resolution, inverse first-variable transport,
actual localization square, identity and tower equations, and the raw rational
arbitrary-morphism cases. The tensor convention was explicitly matched to the
Hom-first convention of the recorded finite-free theorem. The first compiler pass
exposed a base-field universe mismatch and the class name `IsSeparated`; both were
corrected. A later augmentation elaboration required explicit independent site
universes and a typed local Grothendieck-abelian witness. No node text was changed.

Validation update: `scompile.py NK lem-zl-specified-hom-scalar-evaluation` completed
for the whole final module (sandbox and library paths), with no errors or warnings.
The node changes only `lean`; all eight public declarations are recorded. The stored
main signature retains the file's exact line breaks and spacing. Every Lean line
is at most 100 characters.

Delivery dry run: `deliver2.py NK lem-zl-specified-hom-scalar-evaluation --no-push`
printed `OK (dry run): commit 9f8dacfa7b passes the preflight and compiles; nothing pushed`.
The staged set is precisely the module, item node, and report.
