## What changed

The original theorem signature and the canonical-arrow definition are unchanged.
The existing instance and predicate declaration texts move to
Sheaf.AlgebraicGeometry.CartierKummerData, publicly re-exported by the original
module. This permits the proof lemmas to import the predicates without a cycle;
see coord/changes/cartier-kummer-data-extraction.md.

The main proof establishes a concrete annihilating exponent n+1 from the DVR
maximal-ideal and quotient APIs; constructs the unique ordinary etale family
pointwise from supported_cartier_boundary_existsUnique; obtains its unique
published-Tate realization by cartier_kummer_descent; obtains coefficient and
geometric compatibility by cartier_kummer_naturality; and proves the Chern clause
using the already proved integral coefficient-unit equation and supported Kummer
Chern calculation. Pointwise boundary uniqueness, function extensionality and product
extensionality assemble the simultaneous unique families.

The two transport results are separate pieces of the source's final paragraph:
descent/exponent independence, and naturality of an already realized family.
Neither simply renames the main theorem. The combination proof also establishes
the annihilator, ordinary family existence/uniqueness, and Chern equation.

Validation: remote lcompile.py --all compiled all four delivery modules without
warnings against the current published library and sandbox dependencies. The
compiler accepted each module with its configured limit. The family and Chern
proofs were also checked in focused diagnostics during development. The diagnostic
files and options were removed. Busy-server responses were retried.

The current two unchanged consumers were inspected: neither explicitly uses a
relocated declaration, and re-export preserves their public API and instances.
Their recompilation is stopped by an unrelated private-overlay dependency failure
in IntegralCompactSupportCoefficientComparison at revision 84c221d72d27:
lines 289--314 leave an EssentiallySmall universe unsolved and later scalarTensor
names are unavailable. The import paths go through
ConstructibleExceptionalAdjunctionCoefficientsData and QcqsCompactSupportRealization;
that dependency is absent from CartierKummerMap's import closure. No consumer
adaptation or unrelated upstream repair is included.

## Proved and sorry left

Original holes: one, AlgebraicGeometry.Etale.cartier_kummer_map.
The main module has no sorry; its proof is a decomposition through
two strictly smaller sourced statements, rather than a net closure of one hole.

Added holes:

- AlgebraicGeometry.Etale.cartier_kummer_descent
  (lem-amb-cartier-kummer-descent): unique exponent-independent realization of
  an already normalized ordinary family.
- AlgebraicGeometry.Etale.cartier_kummer_naturality
  (lem-amb-cartier-kummer-naturality): coefficient and geometric naturality of
  an already realized family.

No sorry occurs in a definition, instance or private helper. The unique-choice
definition cartierKummerMap retains its original determining theorem.

## No longer needed

The original module's following direct proof imports are removed:

- WeilConjectures.AlgebraicGeometry.EffectiveCartier
- WeilConjectures.AlgebraicGeometry.Sites.GmPicard
- Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
- Sheaf.CategoryTheory.Sites.TorsorWithSection
- Mathlib.Algebra.Homology.Embedding.ExtendHomology
- Mathlib.Algebra.Homology.HomologySequence
- WeilConjectures.AlgebraicGeometry.DerivedCategories
- WeilConjectures.AlgebraicGeometry.EtaleSheaves
- WeilConjectures.AlgebraicGeometry.Sites.Kummer
- Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison
- Sheaf.AlgebraicGeometry.ClosedSupportHom
- Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.CategoryTheory.Linear.FunctorCategory
- Mathlib.CategoryTheory.Linear.Yoneda
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- WeilConjectures.SixFunctors.OpenClosed.Exact
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
- WeilConjectures.SixFunctors.Finite.Stalk
- WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
- Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
- Sheaf.AlgebraicGeometry.PullbackConstantModule
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.Paper.PbcCoefficientTwists
- Sheaf.Paper.PurTwistSheafLocallyFree
- Sheaf.Paper.ComparisonPullbackExact
- Sheaf.CategoryTheory.ModulePullbackTensorIso
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
- Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence
- Sheaf.Algebra.Homology.ChangeOfRingsKFlat
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.CategoryTheory.SiteInverseImageTensor
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

The original five public imports are retained verbatim, alongside the new public
Data import. The original unit-route imports ProEtaleSiteComparison and
IntrinsicCoefficientTwistsUnrestricted are retained as required by the unit route.

The main node now directly uses the existing boundary existence, derived-unit
forgetting and Chern realization results, plus the two named transport results.
The generic torsor, scalar, stalk, open-closed and site-comparison ingredients
remain in the proof plans of those dependencies where needed; they are not
claimed globally unnecessary. The new statement modules import only their Data interface; they do not import
the unused proof-plan modules GeoCartierCycleClass, SupportedKummerBoundaryScalar
or SupportedKummerBoundaryPullback. Those remain declared proof dependencies for
the workers proving the two transport lemmas. No Lean module is withdrawn, no adopted source
declaration is removed, and no blueprint unit route is bypassed. The unit
sk-prop-sf-cbc has no fixed realized proof steps to replace. Old top-level
tool_uses are removed from this node because they are no longer direct proof
uses; the new nodes explicitly retain their relevant dependencies.

Removed direct proof-dependency and tool-approval edges (their declarations
and modules remain, and their downstream uses are retained):

- def-pc-divisor-line-bundle
- lem-sc-line-bundle-torsor
- lem-amb-relative-torsor-cohomology
- lem-amb-kummer-any-base
- lem-weil-pbc-derived-module-underlying-comparison
- lem-amb-closed-support-hom
- lem-weil-pbc-open-closed-short-exact
- lem-pur-derived-change-of-rings
- lem-pur-sheaf-ring-derived-coefficient-adjunction
- lemma-weil-pbc-finite-stalk-formula
- lem-kun-inverse-image-monoidal
- lem-kun-stalk-as-pullback
- lem-kun-pullback-constant
- prop-weil-pbc-geometric-stalks-exact
- lemma-weil-pbc-geometric-stalk-conservative
- lem-asd-etale-finite-twist-pullback
- prop-weil-pbc-inverse-image-modules-exact
- lem-asd-finite-etale-twist-line
- lem-pc-bounded-above-flat-kflat-site
- def-coefficient-twists-detailed
- lem-pur-twist-sheaf-locally-free
- lem-sf-comparison-pullback-exact
- lem-weil-pbc-ringed-topoi-module-pullback-tensor
- lem-cbc-proetale-extension-zero-comparison
- lem-sf-proetale-open-closed-sequence
- def-sf-comparison-derived-pullback
- lem-pur-kflat-change-of-rings
- def-weil-proetale-inverse-image
- def-weil-pbc-site-comparison-morphism
- lem-weil-pbc-left-exact-site-inverse-image-tensor
- prop-weil-pbc-proetale-constant-ring-map
- lem-weil-pbc-etale-module-cohomology-forget
- lem-cbc-open-closed-recollement

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The ordinary boundary existence and Chern/unit
lemmas already prove the first several expanded steps, so repeating those
constructions would duplicate completed library work. The published Tate target
still requires the finite Tate descent and normalization argument, not merely an
ordinary etale root tensor. Empty schemes and empty divisors are covered by the
same unit calculations; positive coefficient levels and exponents are retained.
For reductions a=b the normalized map is the identity, and nonflat coefficient
or scheme maps are covered by the stated derived universal properties.

## New nodes

def-amb-cartier-kummer-data records the unchanged relocated instance and
normalization interfaces. It introduces no new mathematical condition.

lem-amb-cartier-kummer-descent records the source's comparison transport,
exponent independence and uniqueness argument, using the existing finite Tate
descent and ordinary Cartier-class interfaces.

lem-amb-cartier-kummer-naturality records the source's derived scalar-extension
and Cartier-preserving pullback naturality for a realized class.

Change record: coord/changes/cartier-kummer-data-extraction.md.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
