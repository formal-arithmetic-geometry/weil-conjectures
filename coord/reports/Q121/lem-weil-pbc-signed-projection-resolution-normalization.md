## Worker report

The module `Sheaf.Paper.SignedProjectionResolutionNormalization` states the node without
correcting its natural-language statement. The namespace is
`AlgebraicGeometry.Scheme.SignedProjectionResolution`. All theorem proofs are `sorry`;
all definitions have explicit data. The two postponed declarations belong to this node:
`model_properties` is its first conclusion, and `normalization` is its final conclusion.
The intermediate definitions name the exact comparison formulas required by the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `X Y : Scheme.{u}`, `f : X ⟶ Y` give the arbitrary scheme morphism.
- `R : Sheaf (ProEt.topology Y) CommRingCat.{u+1}` and the corresponding `S` on X give
  the two commutative ring sheaves on the original small sites. Their object universe is
  u+1 and their morphism universe is u, as in the published operations.
- `c : (proEtaleSheafInverseImage f CommRingCat.{u+1}).obj R ≅ S` is exactly the fixed
  coefficient identification. No constant-coefficient, flatness-of-f, or properness assumption
  is imposed.
- `proEtaleRingModules`, `DerivedCategory`, `DerivedCategory.Q`,
  `proEtaleRingDerivedPullback`, and `proEtaleRingDerivedDirectImage` are the published
  ordinary, uncompleted, unbounded categories, localizations, and functors.
- `a : ProEtaleTensorModel Y R` and `b : ProEtaleTensorModel X S` supply the existing
  representative presentations of derived tensor. The canonical mate uses the uniquely
  normalized `proEtaleCanonicalTensorComparison`, not an arbitrary pullback isomorphism.
- `K`, `P` are arbitrary objects of these derived categories. `I`, `hI : I.IsKInjective`,
  and `alpha : K ≅ DerivedCategory.Q.obj I` give the chosen K-injective representative.
- `F`, `beta : DerivedCategory.Q.obj F ≅ P`, and `bounded` give exactly the bounded
  coefficient representative, with beta pointing from QF to P as in the node. Boundedness
  is `∃ l h : ℤ, ∀ r, r < l ∨ h < r → IsZero (F.X r)`.
- `package : StrictPerfectCoefficientPackageOnSite ... F` supplies `N`, `i`, `p`, and
  `splitting : i r ≫ p r = 𝟙 _`. These are degreewise maps, with no chain-map condition.
- `pulledCoefficient` applies the exact ordinary module pullback termwise.
  `sourceComplex` is C, `targetComplex` is J, and `pushTargetComplex` is B.
  Each tensor is the existing `CochainComplex.mapBifunctor` with the existing sheaf tensor,
  whose second differential is multiplied by (-1)^a in bidegree (a,r).
- `totalMate` instantiates the existing `CategoryTheory.tensorAdjunctionTotal` to give
  the ordinary signed total counit mate t, from the cited arrows dependency.
  `totalInverse` instantiates the existing `tensorAdjunctionTotalInverse` with exactly
  this pullback, direct image, module adjunction, normalized ordinary tensor comparison,
  unit comparison, I, F, bounds, and package.N/i/p/splitting. Its existing summand theorem
  gives `(1 tensor p_r) q_{I^a,N_r} f_*(1 tensor f^*i_r)`; no arbitrary inverse is supplied.
- `derivedComparison H` is eta_H, namely the component of `rightDerivedFunctorUnit`
  on the homotopy class of H. This definition has no injectivity assumption on H.
- `model_properties` concludes `proEtaleFlatRepresentatives Y R F` and the analogous
  predicate for `pulledCoefficient`. The predicate is exactly K-flatness plus flatness
  of every term. It also concludes J.IsKInjective, IsIso eta_I, and IsIso eta_J.
- `sourceModel` is an actual isomorphism S in D(R_Y). Its first factor is tensor of
  `(Rf_* alpha) ≫ eta_I^{-1}` with beta^{-1}, followed by `proEtaleMixedTensor` on Y.
- `targetModel` is an actual isomorphism T in D(R_Y). It applies Rf_* to tensor of alpha
  with `Lf^*(beta^{-1}) ≫ ell_F`, followed by the mixed tensor on X, and then eta_J^{-1}.
  Here ell_F is `proEtaleRingDerivedPullbackFactors.app F`.
- Both mixed comparisons use the existing `proEtaleMixedTensor` unique characterization
  for every flat-term K-flat resolution, which is the node's fixed-tensor normalization.
  In particular no K-flatness of f_*I is assumed.
- `normalization` states pi = S.hom ≫ Q(t) ≫ T.inv, which is precisely
  pi = T^{-1} composed with Q(t) composed with S in conventional composition notation.
- `inverse` is T.hom ≫ Q(s) ≫ S.inv. The final two conjuncts of `normalization` say
  pi ≫ inverse = identity on the source and inverse ≫ pi = identity on the target.
- All representatives, derived isomorphisms, and degreewise packages are universally
  quantified. Neither K nor I has a boundedness binder. The inverse uniqueness and
  choice-independence argument is included in the theorem's proof docstring.

Dependency interfaces used/read:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the original
  `Sheaf.AlgebraicGeometry.ProEtaleOperations` declarations `proEtaleRingModules`,
  `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`, their adjunction,
  and the ordinary derived functors; the constant specialization is not imposed.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` reexports
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: `ProEtaleTensorModel`,
  `proEtaleOrdinaryTensor`, `proEtaleFlatRepresentatives`,
  `proEtaleOrdinaryTensorPullback`, its naturality, and the normalized derived comparison.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` reexports
  `Sheaf.Paper.StrictPerfectPackageOnSite`: `StrictPerfectCoefficientPackageOnSite`.
  This is its independent-universe degreewise package, not the unused localized
  representation specialization.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`: `proEtaleProjectionUnit_existsUnique`,
  `proEtaleStrictPerfect_flat`, and `proEtaleMixedTensor`; its reexported general module
  `Sheaf.Paper.ProjectionFormulaArrows` supplies `tensorAdjunctionTotalInverse`
  and `tensorAdjunctionTotalInverse_summand`, as well as the forward
  `tensorAdjunctionTotal` and `derivedProjectionFormulaMate` used directly in the signature.
- `Sheaf.Paper.ProjectionMateExact`: `ringedProjectionMateExact`, the canonical
  natural counit projection mate and its exactness interface. The small-site mate is written directly as
  `derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
  (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
  a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K P`.
  This is exactly the body of the convenience name `proEtaleProjectionFormulaMate`,
  without requiring its owning node as a statement dependency.
- `Sheaf.Algebra.Homology.FixedTensorLocalizationComparison`:
  `SheafOfModules.FixedTensorLocalization.fixed_tensor_localization_comparison`;
  the mixed-comparison characterization in the arrows module expresses this normalization
  with the actual small-site universes and the chosen tensor presentations.
- `Sheaf.Paper.ProEtaleMixedProjectionMate`: `proEtaleMixedProjectionMate` is imported
  privately for proof step 6, as its node is a recorded proof dependency. The statement
  uses neither its theorem nor its convenience definition `proEtaleProjectionTotal`.
  Its node is absent from stmt_deps.
- All other stated proof dependency modules are imported privately: FlatOnSite,
  BoundedAboveFlatSheafKFlat, SplitPerfectTensorKInjective, KInjectiveTotalDerived,
  KFlatFixedTensorTriangulated, ModulePullbackTensorIso, the upstream homotopy adjunction,
  Mathlib's right-adjoint limit preservation, and BifunctorShift. Their recorded interfaces
  were read. No dependency repair or new independent definition node is needed.

Edge cases checked before drafting and again against the completed signatures:

- Rank N_r=0 is permitted by `ℕ` and `Fin (package.N r)`; the existing inverse summand
  theorem includes this empty finite product.
- The zero coefficient complex and the empty scheme are not excluded.
- A single nonzero coefficient degree may occur in any integer degree; no bounds are fixed.
- Nonzero coefficient differentials are permitted: the package imposes no differential
  compatibility on i_r/p_r. The existing signed total inverse uses naturality of inverses.
- I and K can be unbounded in both directions. Only F is bounded.
- Alpha and beta may be arbitrary derived isomorphisms, rather than localizations of
  complex maps; the constructions use mapIso and their inverses directly.
- The identity morphism and arbitrary coefficient identification c are included.

Searches (2026-10-22):

- msearch leanfinder: "Derived projection formula on arbitrary K-injective and bounded
  finite projective representatives equals the localized signed total counit mate".
  Eight projective-resolution/left-derived comparison hits; no matching projection theorem.
- msearch loogle: `"derived_counit"`. One hit, `CategoryTheory.Adjunction.derived_counit`,
  an abstract adjunction-localization identity, not the signed finite-retract normalization.
- msearch leansearch: "The canonical derived projection mate is the localization of the
  signed total counit map on arbitrary K-injective and bounded finite projective
  representatives". Eight hits, including derived_counit, derivedε, totalLeftDerivedCounit,
  totalRightDerivedUnit, and Q; none states this node.
- msearch grep: `projectionFormula|tensorAdjunctionTotal|mixedProjectionMate`,
  Mathlib/CategoryTheory: zero hits. Direct rg over Mathlib/CategoryTheory and
  WeilConjectures gave no matching signed normalization. The required grep of the node id
  in WeilConjectures also gave zero hits.
- rg over Sheaf/Paper found and reused the ordinary total/inverse and mixed comparison
  declarations. `PerfectProjectionFormula.Resolution.sourceModel`, `targetModel`, and
  `totalization_compatibility` were read at the source's specified place: they specialize
  to an adic coefficient datum and its quotients, so do not state the present arbitrary
  ring-sheaf and arbitrary P theorem. No second definition of tensor, package, mate,
  or mixed comparison is introduced; the new names only assemble the node's C/J/B/S/T.

Validation: scompile.py checked the repaired module in sandbox and library module modes
successfully, with no errors or unexpected warnings (37.3 s and 19.8 s). Delivery validation uses
only the prescribed wrapper. No global build, direct Git command, or write to the read
repository was performed. No statement dispute or mathematical correction was needed.

## Second reading by Q121

Author's self-check, not an independent review: re-read the node alongside the completed
module, checked the directions alpha:K→QI and beta:QF→P and both inverse equations,
and expanded the definitions of S and T. The source comparison uses eta_I inverse after
Rf_*alpha; the target comparison uses Lf^* through the published exact pullback,
then ell_F, mixed tensor, and eta_J inverse. The chain inverse uses the supplied package,
not a freely supplied map. Checked the original small-site universes and all six original
statement-dependency interfaces. The repair removes the extra statement dependency and changes its import to private;
`totalMate` now uses the arrows node's `tensorAdjunctionTotal`, and all three occurrences
of pi directly use `derivedProjectionFormulaMate` with the canonical tensor comparison.
The original six statement dependencies and natural-language statement are retained.
These replacements are the bodies of the former convenience definitions, so the
comparisons, signs, and inverse identities have the same mathematical meaning.
The maintainer supplies the independent review, as required by the dispatcher brief.


## Returned-delivery repair

Repaired H2 from independent review of immutable head `e4c167ad0106`:
removed `lem-weil-pbc-proetale-mixed-projection-mate` from stmt_deps and removed
its public import. The new assembly definition `totalMate` calls
`CategoryTheory.tensorAdjunctionTotal` from the already cited arrows dependency,
using the same pullback, direct image, adjunction, tensor comparison, and naturality
arguments as `totalInverse`. No bounds or splitting are required to define t.
The theorem writes pi directly using `derivedProjectionFormulaMate` and the
published canonical tensor comparison, as requested. All other conclusions and
hypotheses from the accepted reading are retained.

The H9 advisory was checked against the recorded proof_deps. The private imports
are the modules of those proof dependencies, required by stages/2-statements.md
§3.7 as the future proof plan. In particular the mixed-mate module stays private
for proof step 6; no declaration from it is referenced by a public signature or
by the data of a public definition.

Compared the retained packet with the current read-only node: before this repair,
only stmt_deps and lean differed. After restoring the original six stmt_deps,
only lean differs. No statement correction or new node is needed. The delivery
wrapper prepares the current-base commit; no direct Git command was used.
