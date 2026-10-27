## Worker report

The main module states `etale_chart_comparison_isos` and constructs its scheme,
nonnegative finite-root twist, and signed-shift comparisons. It uses ordinary
unbounded derived categories of fixed constant-ring module sheaves. The scalar
comparison is a natural transformation with invertible components on the specified
bounded constructible finite-Tor subcategory, characterized on every flat-term
K-flat representative. No assertion is replaced by cohomology-only comparisons.

Hypothesis and clause correspondence:

- `k`, `[Field k]`, `p`, `[CharP k p]`, `hp`, `ell`, `hell`, and `hne` render
  the positive-characteristic field and prime different from the characteristic.
- `T T' : Over (Spec (CommRingCat.of k))`, the finite-type instances
  `LocallyOfFiniteType` and `QuasiCompact`, the two `IsSeparated` instances,
  and `v : T' ⟶ T` render the two separated finite-type schemes and k-morphism.
- `A B`, their `CommRing` and `Finite` instances, `f : A →+* B`, `n`, `hA`,
  and `hB` render the unital finite coefficient map and annihilation by ell^n.
  Positivity of N follows from `Nat.pow_pos hell.pos`; n=0 is retained.
- `Et`, `Pro`, and `nu` use the recorded ordinary coefficient categories and
  the existing comparison inverse image. `etPull` and `proPull` use the existing
  scheme inverse images; the latter is definitionally the recorded sheaf pullback.
- `Etale.DerivedCategory.boundedConstructibleFiniteTor` renders boundedness,
  constructible cohomology, and finite Tor amplitude, without perfectness or a
  flatness hypothesis on B over A.
- The first existential gives the B-module natural scalar comparison and
  `IsIso (alpha.app K)` gives its derived isomorphism. `ScalarModel` gives the
  exact counit square with `scalarSheafIso` on every flat-term K-flat P, including
  the invertibility of both computation counits. `scalarSheafIso` is the mate of
  commuting restriction of coefficients and sections, with the ordinary balanced
  tensor's B-action. Mathlib's B-first tensor convention is the symmetry-equivalent
  presentation of the node's x tensor b convention; it keeps the same b.
- `schemeSheafIso` is the recorded site square with its endpoints exposed;
  `schemeIso` is its canonical localization. `etId`, `proId`, `etComp`, `proComp`
  and `SchemeCoherent` state the identity and composition equations.
- `finiteEtaleTateTwist` is the recorded etale twist. `proTwist` starts from
  `finiteRootProTensor`, the actual balanced tensor of roots, and uses the constant
  unit at zero and tensor powers thereafter. `rootIso` is the existing comparison
  fixed by its root/unit and tensor-generator formulas. `twistSheafIso` iterates
  the canonical tensor comparison. `twistLineIso` passes to degree zero and
  `twistIso` tensors with L using the canonical derived tensor comparison.
- `TwistNatural` records naturality in L explicitly. `RootPullbackNormalized` identifies first-power pullback with the recorded
  same-unit root map and zero-power pullback with the unit map, and states tensor
  recursion. `TwistPullbackLaw` is the full derived pullback square for L(c).
- `shiftIso` is the existing natural shift comparison of the exact termwise
  functor, for every integer s, with the signed cochain differential.

The tensor-source and tensor-target helper theorems expose the existing bifunctor
object formulas. Their equality transports are identities, used to keep kernel
checking within the per-file limit; they change neither the tensor map nor its
normalization. `nuTensor`, `etTensor`, and `proTensor` are the existing canonical
derived tensor comparisons with these endpoint formulas exposed.

Every definition has real data. The postponed assertions have proof docstrings
attached to their owning node, including the auxiliary invertibility of N on a
scheme over k. The scalar derived functor is selected by its universal derived
pair, which determines it up to unique counit-compatible isomorphism.

Dependency declarations inspected (the applicable interfaces are imported):

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-etale-constructible-sheaf`: `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-pc-cochain-complex-modules`: `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`.
- `def-pc-flat-sheaf-modules`: inspected `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`. This ring-sheaf interface is not imported: `ScalarModel` uses exact tensor in the recorded fixed-coefficient category.
- `def-pc-kflat-complex`: inspected `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`. This ring-sheaf interface is not imported: `ScalarModel` uses the existing `HomologicalComplex.quasiIso.kFlat` predicate for fixed coefficients.
- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `lem-pur-derived-change-of-rings`: the current record is Q84's `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`, publicly retaining `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`. Its ordinary-module signature and generic ring-sheaf interface were inspected. The item needs module-valued sheaves on the two sites; its five fixed-coefficient scalar helpers supply that presentation locally. The dependency node and both published interfaces are not delivered or rebound.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.upperStar`.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`.
- `lem-asd-finite-etale-twist-line`: `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`, `AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line`.
- `lem-amb-finite-root-site-comparison`: `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`, `AlgebraicGeometry.Scheme.finiteRootSiteComparison`.

Additional existing APIs used: `Functor.leftDerivedFunctor`,
`Functor.leftDerivedFunctorNatIso`, `Functor.leftDerivedFunctorCompIso`,
`Functor.leftDerivedTensorComparison`, `Functor.singleFunctorCompLeftDerivedFunctorIso`,
`Functor.mapDerivedCategoryFactors`, `supportSiteComparisonCoefficientPullbackIso`,
`supportSiteEtaleComparisonId/Comp`, `supportSiteProEtaleComparisonId/Comp`,
`Scheme.finiteEtaleTwistPullbackData`, `Scheme.finiteRootSiteComparison`,
and `Scheme.finiteRootProTensor`.

Edge cases read against the signatures: empty schemes; zero coefficient rings;
n=0 and N=1 (annihilated rings are then zero); c=0 and c=1; positive and negative
s; identity and composite scheme morphisms; nonflat coefficient maps such as
Z/ell^2 to Z/ell. There is no choice of a root trivialization and no flatness
assumption on the scalar map. The ordinary sheaf tensor unit handles c=0.

Searches made with the prescribed msearch wrapper:

- LeanFinder: "Derived inverse image from etale to proetale commutes with scalar
  extension Tate twists and scheme pullback": eight hits, including
  `Scheme.Modules.pseudofunctor_mapComp_hom_τl` and etale base-change facts;
  no exact fixed-coefficient derived chart comparison.
- LeanSearch: "Derived inverse image commutes with extension of scalars and tensor
  products on sheaf categories": eight hits, including `SheafOfModules.pullback`,
  `pullbackComp`, `restrictScalars` and `PullbackConstruction.adjunction`;
  these supply generic underived ringed-site APIs, not this statement.
- Loogle: "Functor.leftDerivedTensorComparison,
  AlgebraicGeometry.ProEtale.comparisonUpperStar": zero Mathlib hits, unknown
  identifier for the project-only derived tensor API.
- Mathlib grep: "derivedExtendScalars|leftDerivedFunctor|proetale" in
  AlgebraicGeometry: ten proetale-topology/ell-adic-cohomology hits, no comparison.
- Project rg: the item id has no occurrence in WeilConjectures. Names
  `etale_chart_comparison|scalarSheafIso|fixedCoefficientDerivedExtension|RootPullbackNormalized`
  have no existing declaration in Sheaf. Searches for finite-root/twist notions
  located `FiniteEtaleTateTwist` and `FiniteRootSiteComparison`, which are reused.
  Broader derived comparison searches located the upstream tensor and site-square APIs.

No statement correction and no disputed statement.

## Return repairs

H13: removed `dag/nodes/sec-smooth-purity/lem-pur-derived-change-of-rings.json`
from this packet, so the live Q84 record is preserved without a field delta.
Removed the separately owned `FixedCoefficientDerivedChangeOfRings.lean` and its
import. Moved `CategoryTheory.fixedCoefficientScalarExtension`, its additive
instance, `fixedCoefficientScalarExtension_hasPointwiseLeftDerivedFunctor`,
`fixedCoefficientDerivedExtension`, and `fixedCoefficientDerivedExtensionCounit`
into `EtaleChartComparisonIsos.lean`. All five are listed in the item's
`lean.declarations` and their source docstrings now carry the item's blueprint id.
The derivability theorem is an auxiliary assertion for this item's scalar
comparison; it is no longer recorded as the general change-of-rings theorem.
The definitions still use the same balanced tensor and universal derived pair.
No mathematical statement or theorem signature changed.

H11: replaced the previous disclaimer with the concrete second reading below,
matching the node's hypotheses, four comparisons, and normalization clauses.

Advisory: removed the unused `FlatOnSite` and `KFlatIndependentCoefficients`
imports. Their `SheafOfModules` predicates were not used for the fixed-coefficient
`Sheaf J (ModuleCat R)` objects; the existing exact-tensor and K-flat predicates
in `ScalarModel` retain those conditions.

## Second reading by Q109

Read the saved node statement against the entire repaired module, including the
five relocated helpers and the Charts paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`.
The following is the clause-by-clause check and its findings.

1. The positive-characteristic field is `(k : Type u) [Field k]`, `[CharP k p]`
   and `hp : 0 < p`; primality and the unequal prime are `hell : ell.Prime` and
   `hne : ell ≠ p`. The two objects of `Over (Spec (CommRingCat.of k))` and
   `v : T' ⟶ T` retain the k-structures and their compatibility. Both triples
   `[LocallyOfFiniteType] [QuasiCompact] [IsSeparated]` express separated finite
   type. There is no smoothness, affineness, or nonemptiness assumption.
2. `A B : Type (u + 1)` with commutative-ring and finite instances and
   `f : A →+* B` give the unital finite coefficient map. The exact equations
   `hA` and `hB` kill both rings by `ell ^ n`; `Nat.pow_pos hell.pos` supplies
   N positive without excluding n=0. The site objects live in u+1 with morphisms
   in u. The fixed-coefficient helpers use precisely those universes and add no
   site-universe equality or flatness hypothesis on f.
3. `Et` and `Pro` are the ordinary `Sheaf ... (ModuleCat R)` categories and
   `DerivedCategory` is their unbounded localization. They are the endpoints of
   `nu`, `etPull`, `proPull`, and `fixedCoefficientDerivedExtension`. The last
   functor is the universal derived extension of sheafified `extendScalars f`,
   with its actual `totalLeftDerivedCounit`. No completed category or arbitrary
   selected functor replaces these objects. The helper theorem's proof docstring
   explains flat-term K-flat resolutions and tensor invariance.
4. The scalar existential gives a natural transformation whose values lie in
   D(B_proet); its components are therefore B-linear. The quantified K has
   `boundedConstructibleFiniteTor`, and `IsIso (alpha.app K)` gives exactly the
   first displayed isomorphism. `ScalarModel` quantifies over every K-flat P
   with exact right tensor by each term, asserts that both computation counits
   are invertible, and equates the two paths through `alpha`, `nuQFactor`, the
   counits and `scalarSheafIso`. The latter is the left-adjoint-uniqueness mate
   of the commuting restriction square. This fixes the balanced-tensor map and
   its B-action; Mathlib places the B factor first by symmetry. Nonflat maps
   such as Z/ell² to Z/ell remain allowed.
5. `schemeSheafIso` is the existing site inverse-image square, and `schemeIso`
   is its explicit localization through `leftDerivedFunctorCompIso` and
   `leftDerivedFunctorNatIso`. These definitions already provide the second
   displayed isomorphism naturally in L. `SchemeCoherent A k` and
   `SchemeCoherent B k` separately give the identity equation and the two paths
   for a composite `v.left ≫ w.left`, with `etId/proId` and `etComp/proComp`.
   The order of the contravariant pullbacks in the composite equation agrees
   with the node; no comparison is left as an arbitrary isomorphism.
6. The etale twist is the recorded `finiteEtaleTateTwist`; `proTwist` has the
   constant tensor unit at zero, the actual `finiteRootProTensor` at one, and
   its tensor powers above one. `rootIso` chooses a comparison already pinned
   by `finiteRootSiteComparison`'s generator laws, sending the root to the same
   unit and retaining the scalar. `twistSheafIso` uses the inverse unit map at
   zero and inverse monoidal tensor comparison followed by the previous power
   and `rootIso` at each induction step. `twistLineIso` places it in degree
   zero; `twistIso` is the derived tensor comparison followed by one tensor
   that line map. It therefore gives the third displayed isomorphism for both
   R=A and R=B and every c, without choosing a root trivialization.
7. `TwistNatural` spells out the square for every morphism L to M in the stated
   bounded constructible finite-Tor range. `RootPullbackNormalized` identifies
   the transported first-power arrow with the existing intrinsic root-tensor
   pullback, the zero-power arrow with `Functor.OplaxMonoidal.η`, and higher
   powers with `δ` and the preceding arrows. Thus the transport does not merely
   define away the root-pullback normalization. `TwistPullbackLaw` compares the
   full derived square using `schemeIso`, `etTwistPullback`, `twistIso`, and
   `proTwistPullback`. Both rings occur in all three predicates in the theorem.
8. `shiftIso R T s` is a natural isomorphism of functors for every `s : ℤ`.
   It is constructed from the exact termwise functor's `commShiftIso`, conjugated
   by its derived-localization isomorphism. This retains the signed cochain
   differential and covers the fourth display, including negative s. This
   comparison, like `schemeIso` and `twistIso`, is a construction in the module;
   it need not be re-asserted as an existential conjunct of the theorem.
9. Checked n=0/N=1 with zero coefficient rings, c=0 and c=1 before recursion,
   the empty scheme, zero and negative shifts, identity morphisms and composites,
   and a nonflat f. The unit branches and modulus proof signature admit all
   these cases. No added hypothesis excludes them.

Found and repaired the ownership mismatch H13: a theorem proving existence only
of the fixed-coefficient derived functor was attached to the general
change-of-rings node. It now belongs solely to this item, and the published
Q84 record is untouched. Found and removed the two unused ring-sheaf imports.
The repaired item otherwise retains the reviewed mathematical signatures and
canonical maps; no statement correction, new node, or dependency module is needed.
