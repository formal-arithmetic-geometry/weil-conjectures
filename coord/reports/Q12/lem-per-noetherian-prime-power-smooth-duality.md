## Worker report

The module states `noetherianPrimePowerSmoothDuality`. Its only postponed proof is that theorem, whose docstring includes the node's complete sixteen-step natural-language proof with the dependency ids. Every helper definition has real data: canonical functor composites or a proposition specifying equations. `Datum` collects conclusions, rather than assuming an orientation, a deformation comparison, or tensor invertibility. The unchanged natural statement is encoded as existence of one coherent family over all maps and positive levels, making the compatibility clauses literal equations for the same orientations.

| Hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| Positive n, Lambda_n = Z/(ell^n) | `Family` quantifies `n` and `1 ≤ n`; `FiniteSmoothPurity.coefficient ell n` is the existing harmless universe lift of the literal quotient |
| Noetherian source and target | `[IsNoetherian P] [IsNoetherian X]` |
| Smooth of pure relative dimension r ≥ 0 | `(r : ℕ) [SmoothOfRelativeDimension r p]` |
| Separated and finite type | `[IsSeparated p] [QuasiCompact p]`; local finite type follows from smoothness and also compactifiability |
| Compactifiable | `[HasCompactification p]`, the recorded open/proper factorization predicate |
| ell invertible on both schemes | `hP`, `hX : IsUnit ((ell ^ n : ℕ) : Γ(-, ⊤))`; for n positive, an invertible nth power is equivalent to an invertible base element |
| Ordinary small-etale categories and compact-support right adjoint | `DerivedCategoryModule (coefficient ell n) X`, `rightDerivedUpperShriek (ModuleCat ...) p`; its chosen adjunction is with ordinary `rightDerivedLowerShriek` |
| Orientation Lambda_P(r)[2r] ≅ p! Lambda_X | `Datum.alpha.inv`, inverse to `alpha : dualizingComplex ... p ≅ line ... P r` |
| Inverse from diagonal base change, section deformation, inverse vector purity | `Datum.normalized : OrientationNormalized ... geometry hP alpha`; that published equation uses `finiteSmoothDiagonalFactor`, the t=1-normalized Rees specialization, `bundleSectionAdjoint`, and the canonical normal-cone/bundle comparison |
| P1 Chern class integrates to one; ordered affine product | `OrientationNormalized` uses the existing bundle adjoint of `vectorBundleIntegration`, normalized by the ordinary P1 datum and ordered affine trace; comparisons use `projectiveLineTraceTransport`, which fixes roots and scalar generators |
| Every K in D+ and the counit tensor map is an isomorphism | `Datum.tensor_isIso` quantifies the entire `DerivedCategory.Plus` and asserts `IsIso (FiniteSmoothPurity.gamma ... K.obj)`; gamma is tensor with alpha inverse followed by `smoothTensorDualityMap` |
| The unit gamma equals the orientation | `Datum.unit_normalization` explicitly identifies gamma at the coefficient unit with alpha inverse through inverse-image-unit and tensor-unit constraints |
| Noetherian base change of orientation and gamma | `BaseChange` gives both the unit-orientation equality using `smoothDualizingBaseChangeMap` and the D+ gamma equality using `smoothExceptionalBaseChangeMap`; `baseChangeSource` consists of the canonical tensor and roots-pullback comparisons |
| Open and etale restriction | Target restriction is the open/etale instance of `BaseChange`. Source open or separated etale restriction is `Composition` with the first dimension zero, together with `Datum.dimension_zero` |
| Composition under exceptional transitivity | `Composition` identifies gamma for `p ≫ q` with gamma for p followed by p! of gamma for q; `exceptionalComp` is adjunction conjugation of the actual compact-support composition isomorphism, and `compositionSource` concatenates the ordered shifted Tate factors |
| Relative dimension zero is the etale adjunction comparison | `Datum.dimension_zero`, including every graph-normalized comparison family C; `etale_comparison_exists` supplies such a normalized family so this clause is not vacuous |
| Reduction N ≥ n carries gamma_N to gamma_n | `Reduction` compares `ordinaryScalar(...).map alpha_N.inv` followed by the actual `ExceptionalCoefficients.mateMap` and its unit identification, with `(e.tensorPower r).hom ≫ alpha_n.inv` |
| Tate reduction is u ↦ u^(ell^(N-n)) | `CoefficientLineComparison.roots_power` fixes the underlying kernel map to multiplication by `(ell^N)/(ell^n)` in the additive roots presentation, equal to ell^(N-n); `generators` and `derived_normalization` fix scalar extension and the derived comparison |
| No excellence or field assumption | No such binder occurs. All categories in the theorem and its predicates are ordinary etale categories. Existing helper imports also expose pro-etale interfaces, but those are unused in the assertion |

The base-change equation explicitly binds the inherited `[IsNoetherian (pullback p b)]` structure needed to read the family and its alpha projection. This adds no geometric restriction: its locally Noetherian and compact-space fields follow from finite-type base change over the Noetherian base, so the constructor `⟨⟩` supplies it whenever the original hypotheses hold. Proof irrelevance makes the equations independent of this structure witness. Smooth relative dimension after base change is inferred from the published instance. Composite dimension is written s+r: this equals r+s, and the actual tensor comparison uses the order of the right-adjoint composite, with the q-line before the p-line. Its even shifts introduce no Koszul sign. Quantified structure instances on composites express the inherited structures and impose no extra geometric restriction.

Dependency interfaces used:

- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-asd-compactifiable`: `Sheaf.AlgebraicGeometry.CompactifiableOverField`, `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `thm-amb-etale-exceptional-adjoint`: `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `def-asd-finite-etale-tate-twist`: `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`, `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`.
- `def-pur-finite-smooth-canonical-maps`: `Sheaf.Paper.FiniteSmoothPurityMaps`, `AlgebraicGeometry.Etale.FiniteSmoothPurity.proGamma`.
- `def-pur-finite-smooth-adjunction-data`: `Sheaf.Paper.FiniteSmoothAdjunctionData`, `AlgebraicGeometry.Etale.FiniteSmoothPurity.SmoothLevel`.
- `def-pur-finite-smooth-coefficient-arrows`: `Sheaf.Paper.FiniteSmoothCoefficientArrows`, `AlgebraicGeometry.Etale.FiniteSmoothPurity.proCoefficientMap`.
- `def-amb-p1-trace`: `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`, `AlgebraicGeometry.Etale.projectiveLineTrace`.

Further canonical maps used from already recorded proof modules include `smoothExceptionalBaseChangeMap`, `smoothDualizingBaseChangeMap`, `smoothSquarePullbackIso`, `vectorIntegrationBaseCoefficientPullback`, `unboundedEtaleLowerShriekCompIso`, `finiteSmoothAdjointCoordinates`, and `ExceptionalCoefficients.mateMap/unitIso`. The statement's additional dependencies cite the published finite smooth map, coefficient-arrow and adjunction-data modules and the P1 trace transport; no existing notion is copied.

Edge cases checked: n=1; N=n, where root reduction is power one and scalar extension is the identity comparison; r=0, including identities, open immersions and nontrivial separated etale maps; empty source or base (global sections form the zero ring, where its unique element is a unit); nonconstructible and unbounded-above D+ complexes; nonflat quotient coefficient maps; arbitrary Noetherian bases with nilpotents and without excellence or a field. There is no nonempty hypothesis, no positive-dimension restriction, and no constructibility or finite Tor restriction on K. Universe u is explicit throughout, with coefficients and module sections in u+1 and derived categories in u+2, as in the recorded ordinary-etale interface.

Searches from the resumed sandbox, including those retained from the interrupted turn:

- msearch `leanfinder`, query `smooth Noetherian scheme prime power etale coefficients purity canonical diagonal orientation exceptional inverse image` (subdirectory ``): 8 hits. Top results: Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial, StandardEtalePair.hasMap_X, Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq, StandardEtalePair, StandardEtalePresentation, Algebra.etaleLocus, Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime, Algebra.exists_etale_of_isEtaleAt.  No exact diagonal/DNC smooth-duality family.
- msearch `grep`, query `smooth.*duality|smooth.*purity|dualizingComplex` (subdirectory `AlgebraicGeometry`): 0 hits. Top results: none.  No exact diagonal/DNC smooth-duality family.
- msearch `loogle`, query `AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.Etale.rightDerivedUpperShriek` (subdirectory ``): 0 hits. Top results: none. loogle: unknown identifier 'AlgebraicGeometry.Etale.rightDerivedUpperShriek' No exact diagonal/DNC smooth-duality family.
- msearch `leansearch`, query `smooth morphism etale derived category dualizing complex Tate twist diagonal purity` (subdirectory ``): 8 hits. Top results: AlgebraicGeometry.IsSmooth, AlgebraicGeometry.IsSmooth.mk, AlgebraicGeometry.IsSmooth.casesOn, AlgebraicGeometry.IsSmoothOfRelativeDimension.mk, AlgebraicGeometry.IsEtale.instIsSmooth, AlgebraicGeometry.IsSmooth.recOn, AlgebraicGeometry.isSmooth_iff, AlgebraicGeometry.instLocallyOfFinitePresentationOfIsSmooth.  No exact diagonal/DNC smooth-duality family.
- `rg` in upstream WeilConjectures for the item id: no match. Names and concepts `noetherianPrimePowerSmoothDuality`, `NoetherianSmoothDuality`, smooth purity, orientation and dualizing comparison were searched in upstream and side Lean. Existing finite-smooth interfaces were found and read, but their final general-base theorem is over a field and includes pro-etale bounded constructible finite-Tor assertions, so it is not this ordinary Noetherian D+ statement.
- Read the DAG statement and every original statement dependency's Lean record/mathlib match and source signatures. Read Scholze's Theorem 7.19 and its following paragraph in the retained extracted source, and the current blueprint orientation and DNC sections. The item is a detailed child, not a unit statement. No source-based correction was needed.

Validation: compiled with the prescribed scompile.py wrapper, separately in sandbox and library naming modes. A costly initial specialization of the tensor comparisons was repaired by defining baseChangeSource and compositionSource generically in A and specializing only their uses. This uses the upstream derived tensor API's documented coefficient specialization convention and does not alter universes or mathematical scope. The completed module compiled cleanly in 21.6 seconds (sandbox) and 21.9 seconds (library name); the delivery dry run additionally checks the final proof-dependency import list, compiler and preflight.

No new nodes or dependency repairs. No STATEMENT-DISPUTED flag.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
