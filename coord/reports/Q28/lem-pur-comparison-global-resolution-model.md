## Worker report

The module `Sheaf.Paper.ComparisonGlobalResolutionModel` states
`AlgebraicGeometry.ProEtale.comparisonGlobalResolutionModel`, with `sorry` as its
only postponed proof. No natural-language node field is corrected. No dependency
module or independent definition node is needed. The helper declarations package
the given pair of resolutions and construct its maps; they introduce no new site,
coefficient category, derived functor, or comparison adjunction.

Hypotheses and clauses, checked individually against the node:

- The finite discrete commutative coefficient ring is `(Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ]`. The fixed-ring sheaf presentation has no topological
  parameter: it is precisely the discrete coefficient presentation, rather than
  sheaves of topological modules. The comparison and coefficient realization are
  those already supplied by the dependencies.
- The common larger universe is explicit: `U : Scheme.{u}`, both small sites have
  object universe `u + 1` and morphism universe `u`, and the coefficient objects
  are `ModuleCat.{u + 1} Λ`. There is no extra equality of site universes. This
  implements the metatheoretic `def-weil-size-convention`, which has no declaration.
- An arbitrary etale module sheaf is the binder `F : Sheaf U.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)`. This is the recorded definition of the etale derived
  category. On the pro-etale side the fixed-ring presentation is the same one
  used by the recorded global comparison. `finiteCoefficientRealization` is its
  canonical equivalence with `FiniteCoefficientModules U Λ`; its exactness
  transports injectives and K-injectivity, and `finiteCoefficientComparison` is
  literally comparisonUpperStar followed by this realization. Thus the encoding
  retains the node's constant-ring module categories, without an arbitrary map
  or an additional assumption.
- `comparisonResolutionSingle F` is the actual degree-zero cochain complex,
  bundled as bounded below using its existing strict lower bound. It has no
  postponed data. Its localization is the explicit model of `F[0]`.
- `ComparisonGlobalResolution.I` and `.J` are bounded-below cochain complexes on
  the respective sites. The fields `nonnegativeI/J : _.IsStrictlyGE 0` require
  zero terms below zero, not merely vanishing negative cohomology. The fields
  `injectiveI/J` require injectivity of every term. `kInjectiveI/J` use Mathlib's
  `CochainComplex.IsKInjective` from `def-pur-kinjective-complex`.
- The fields `i` and `t` have exactly the prescribed sources and targets, and
  `quasiIsoI/T` assert quasi-isomorphism of their underlying integer complexes.
  `Nonempty (ComparisonGlobalResolution U Λ F)` asserts existence of all this
  data. The subsequent `∀ R` covers every such pair, not only one chosen pair.
- `R.targetIdentification` is the canonical exact-functor localization factor
  followed by `Q.map (A.map i ≫ t)`. Its asserted `IsIso` is exactly the specified
  identification of `QJ` with `A F[0]` (in the forward orientation).
- `R.adjoint` is the hom-equivalence of the existing comparison adjunction
  applied termwise to `R.t.hom`. Thus it is exactly `h`, not a separately assumed
  map. `R.sourceSections` and `.targetSections` evaluate at the terminal etale
  object and its image under `Scheme.toProEt`. `R.sectionMap` evaluates h there;
  its target uses the definitional restriction identity `(NJ)(U) = J(U)`.
- `eI` and `eJ` are computing isomorphisms from localized section complexes to
  derived sections of `F[0]` and `A F[0]`. Their displayed equations require
  `eI.hom ≫ RΓ_et(Qi) = alpha_I` and
  `eJ.hom ≫ RΓ_proet(beta) = alpha_J`, where alpha is the actual right-derived
  comparison unit. As the postcomposed augmentation maps are invertible these
  equations uniquely determine the isomorphisms. They do not permit an arbitrary
  identification with the target cohomology object.
- `comparisonResolutionGlobalMap` specializes the recorded
  `finiteComparisonGlobalSections` to this model of `F[0]`, removing its derived
  identity functor by `Functor.mapDerivedCategoryPlusIdIso`. The equality
  `Q.map R.sectionMap ≫ eJ.hom = eI.hom ≫ comparisonResolutionGlobalMap U Λ F`
  is exactly the asserted normalized global-comparison computation.
- `q : ℕ` covers every integer q >= 0 including zero. A
  `z : R.sourceSections.obj.cycles (q : ℤ)` is a global cocycle, represented in
  Mathlib's canonical kernel of the outgoing differential. Every ordinary
  closed section has a unique such kernel lift, so no cocycle is excluded.
  `comparisonResolutionCycleClass` projects to homology and uses the existing
  canonical homology-factor isomorphisms to enter the localization. The displayed
  equation on these elements applies the specified comparison to the source
  class and gives the class of `cyclesMap R.sectionMap.hom q z` in J, transported
  by the normalized `eJ`.
- The final equality evaluates `R.adjoint.f q` on the closed section
  `R.sourceSections.obj.iCycles q z` and identifies it with `R.t.hom.f q` applied
  to the comparison unit's terminal section. In this fixed-ring presentation
  that is precisely `t(A(z))`: scalar actions remain Λ-linear and the constant
  unit is the one identified in `comparisonPullbackExact`, not a free choice of
  a ring isomorphism. No hypothesis says A preserves injectives.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, together with
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`,
  `DerivedCategory.Plus.Q`, and homology functors.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `finiteCoefficientEtaleRealization`,
  `finiteCoefficientRealization`, their equivalence/exactness declarations,
  and `finiteCoefficientComparison`. The statement uses their canonical
  fixed-ring sheaf presentation, as does the recorded global comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`; its defining adjunction is the
  `comparisonAdjunction` of
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`, whose functors are
  `comparisonUpperStar` (left Kan extension/sheafification) and
  `comparisonLowerStar` (restriction). These are used directly, not copied.
- `Sheaf.Paper.ComparisonPullbackExact`:
  `AlgebraicGeometry.comparisonConstantRingMap` and `comparisonPullbackExact`,
  giving the normalized constant-ring identification, exactness, compatibility
  with homology, and preservation of quasi-isomorphisms.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the dependency's exact Mathlib match.
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`:
  `finiteComparisonGlobalSectionsUnit`, `finiteComparisonGlobalSections` and
  `isIso_finiteComparisonGlobalSections`. The actual specified map is reused.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`:
  `comparisonLowerStarCompGlobalSectionsIso` and
  `comparisonLowerStarCompRightDerivedGlobalSectionsIso`. Their terminal-object
  normalization is the one in the proof; the recorded finite normalized map
  supplies its D+ formulation, so no second global comparison is defined.
- Proof imports include the recorded Grothendieck module-sheaf theorem, bounded
  below injective-resolution theorem, normalized comparison-unit theorem, and
  right-adjoint preservation of injectives. The remaining proof dependencies
  are Mathlib enough-injectives, bounded-below K-injectivity, and the unit of
  `Functor.rightDerivedFunctorPlus`. All seven proof steps are in the theorem
  docstring; no proof is supplied in this stage.

Sources opened: the current blueprint's relative Kummer proof opening paragraph;
Stacks `proetale.tex`, lemma-compare-cohomology (099W), with the preceding
comparison construction (099R); `injectives.tex`,
theorem-K-injective-embedding-grothendieck (079P); and the existing normalized
unit/global-comparison declaration docstrings.

Edge cases checked before stating: arbitrary schemes including the empty scheme;
the zero sheaf and zero coefficient ring; degree zero, where nonnegative complexes
have no incoming nonzero term; arbitrary nonnegative degree; every admissible pair
of resolutions with its own i and t. No qc/qs, separatedness, characteristic,
nonzero-ring, or injective-preservation hypothesis is added. The computing
identifications are fixed by i and t A(i), so replacing an augmentation by an
automorphism cannot silently change the meaning of the comparison.

Searches actually run:

- `msearch.py ... leanfinder`: "The etale to pro etale global cohomology comparison
  is represented by the adjoint chain map of an injective resolution of the
  pullback". Eight results include
  `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal`,
  `SheafOfModules.PullbackConstruction.adjunction`,
  `CategoryTheory.InjectiveResolution.toRightDerivedZero'`, and unrelated
  representation-theory resolutions. None states the normalized two-resolution
  global comparison with its cocycle formula.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction, "derived_unit"`.
  One hit, `CategoryTheory.Adjunction.derived_unit`, supplies a generic derived
  adjunction formula, not this site-specific resolution statement.
- `msearch.py ... grep`:
  `comparison.*(resolution|injective)|(resolution|injective).*comparison`.
  One unrelated Condensed/Discrete/LocallyConstant injectivity hit.
- `rg` for the item id and prospective declaration names in both `lean/Sheaf`
  and `lean/WeilConjectures`, and the upstream name index: no existing item
  declaration or declaration-name collision.
- `rg` for resolution/comparison/cocycle combinations in the project located
  `PurityComparisonUnitInjectiveModel` and `SiteComparisonEdgeSection`.
  The first is the already cited derived-unit proof input; the latter is the
  downstream edge-section consumer and has no statement of this resolution
  model. It is not imported, avoiding a dependency on that consumer.
- Read the recorded normalized global map and the earlier ordinary derived
  global map. Neither supplies the two simultaneous resolutions or the
  normalized formula for every augmentation/cocycle.

No STATEMENT-DISPUTED flag or node fault was found. No data is selected from a
postponed existence theorem. Compilation and delivery validation are recorded
below once complete.

Validation: `scompile.py` typechecked the full statement against the current server
sources. The final `deliver2.py --no-push` passed the per-file compile with no
unexpected warnings and passed the maintainer preflight (dry-run commit
`a0da80e61d1`). Diagnostic options and scratch checks are removed. The permanent
`backward.isDefEq.respectTransparency false` setting resolves the nested canonical
category interfaces within the default 60-second file limit. A sandbox audit
confirmed that only `lean` changes in the JSON, that its signature is verbatim,
that all 238 source lines satisfy the 100-character bound, and that the only
`sorry` is the main theorem. The worker delivers directly; the maintainer supplies
the independent review, as prescribed by the current dispatch brief.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
