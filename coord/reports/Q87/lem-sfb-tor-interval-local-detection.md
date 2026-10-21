## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection` states
`AlgebraicGeometry.Scheme.proEtale_torInterval_local_detection`, with its single proof
left `sorry`. Its conjunction is precisely clauses (i) and (ii) of the node. No new
construction or predicate is defined. The natural-language proof in the docstring follows
all four DAG steps and identifies every tool used there.

Hypothesis and clause correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`.
- The arbitrary commutative ring sheaf is
  `(A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})`. It need not be constant.
  The original small site retains object universe `u+1` and morphism universe `u`;
  modules and coefficients live in `u+1`, the maximum of those sizes.
- The unbounded derived object is
  `(K : DerivedCategory (proEtaleRingModules X A))`. The latter module category is
  the existing `ringedSiteModules` / Mathlib `SheafOfModules`, and its localization
  instance is the existing standard localization from `ProEtaleOperations`.
- The integers and their order are `(c d : ℤ) (_hcd : c ≤ d)`.
- Each interval assertion is expanded as `∀ (M : proEtaleRingModules ... ...) (q : ℤ),
  q < c ∨ d < q → IsZero (...)`. Thus it tests EVERY module sheaf, with one fixed
  interval, without requiring that the test module be flat, constructible or locally
  constant. `DerivedCategory.singleFunctor _ 0` places that module in degree zero;
  `DerivedCategory.homologyFunctor _ q` is its cohomology sheaf. The tensor is the
  existing `SheafOfModules.siteDerivedTensorIndependentCoefficients`, the localization of total tensor on
  flat-term K-flat representatives, not an arbitrary bifunctor.
- For each scheme morphism `f` used in either clause, the source coefficient ring is
  exactly `(proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A`.
  `proEtaleRingDerivedPullback f A _ (Iso.refl _)` uses that same ring with identity
  structural isomorphism. The underscore is inferred from `Iso.refl _`, not a new
  coefficient parameter. Its defining exact termwise functor is the recorded module
  inverse image followed by extension along the identity, canonically inverse image.
- Clause (i) quantifies over `𝒱 : X.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale)`
  and `QuasiCompactCover 𝒱.toPreZeroHypercover`. This is the standard Mathlib presentation
  of a pro-etale covering family: jointly surjective weakly etale arrows with the
  affine finite-subcover condition of the pro-etale precoverage. `QuasiCompactCover`
  here is the local covering condition, not finiteness of the family or quasi-compactness
  of X or of each covering arrow. The local premise quantifies over `t : 𝒱.I₀` and
  tests the inverse image of K on every module on `𝒱.X t`. The conclusion is the same
  explicit interval test for K on X.
- Clause (ii) quantifies over arbitrary `Z U : Scheme.{u}` and maps `i : Z ⟶ X`,
  `j : U ⟶ X`, with `IsClosedImmersion i`, `IsOpenImmersion j`, `QuasiCompact j`.
  Complementarity is exactly `Set.range j = (Set.range i)ᶜ`. The two successive
  premises are the explicit interval tests on inverse images along i and j. Its
  conclusion repeats the original test for K on X.
- Neither clause has a quasi-coherence, Noetherian, bounded-complex, finite-cover,
  nonempty-index, torsion-coefficient or constructibility hypothesis.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`, the weakly-etale precoverage together with `QuasiCompactCover`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, via
  `proEtaleRingModules`, which is its transparent specialization.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `HomologySequence` supplies `homologyFunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its compatibility with the
  live `IsAcyclicTensorKFlat`. This is the recorded K-flat dependency; its tensor
  localization supplies the tensor used here, without introducing another predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleModuleInverseImage`, imported through the existing operations module.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly reexports the
  general ring-sheaf operations through `ProEtaleOperationsCanonicalAdjunction`:
  `proEtaleRingModules`, its standard derived instance, and
  `proEtaleRingDerivedPullback`. The arbitrary ring-sheaf interface is used;
  the constant-coefficient specialization is not substituted for it.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: `SheafOfModules.siteDerivedTensorIndependentCoefficients`, the
  generic ringed-site definition owned by `lem-weil-pbc-site-derived-tensor-descent`.

The last two existing landed nodes were added to `stmt_deps` to name the actual
canonical helpers appearing in the signature. No dependency record was repaired,
no new node was introduced, and the node's mathematical statement is unchanged.

All already stated proof dependencies are imported without `public`: geometric
inverse-image exactness (`GeometricInverseImageExact`), exact-functor derivation
(`ExactFunctorDerivedFunctor`, including the Mathlib factorization), ringed-topos
tensor comparison (`RingedTopoiCanonicalTensorPullbackOfUniverses`), site-object
restriction (`ProEtaleObjectInverseImageRestriction`), cover-local isomorphism
(`Mathlib.CategoryTheory.Sites.LocalProperties`), and open/closed zero detection
(`ProEtaleOpenClosedDetection`). Exact-functor cohomology compatibility is also
available in that import closure. Their full node statements and the statement
dependencies' source signatures and docstrings were read.

Source checked: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure, `sk-def-localizing-closure-ctf-equals-bc.proof.md`, Locality
and Strata. The node expands those restriction/conservativity arguments, rather
than asserting an additional projection formula.

Edge cases checked mathematically: c=d tests all degrees except that one;
negative c,d use ℤ throughout; zero K passes each vanishing test; arbitrary unbounded
complexes are allowed. An empty covering index is permitted and is a cover only
of the empty scheme. Either member of the complementary open/closed pair can be
empty, reducing detection to the other member. Infinitely many cover members are
allowed. Arbitrary coefficients include the zero ring, non-Noetherian rings and
nonconstant ring sheaves. The example F_ℓ over Z/ℓ² is not incorrectly forced to
have finite Tor amplitude. No mathematical statement dispute was found.

Searches:

- `msearch.py ... leanfinder` query: “Tor amplitude of sheaves is detected on
  proetale covers and complementary open closed immersions”. Eight hits, generic
  `DerivedCategory.IsGE`, `IsLE`, t-structure and etale-site results; no match.
- `msearch.py ... loogle` query: `DerivedCategory.torAmplitudeIn, SheafOfModules`.
  Zero hits; the search endpoint does not know the project-only torAmplitudeIn name.
- `msearch.py ... grep` query: `torAmplitude|TorAmplitude|torInterval`, subdirectory
  `Algebra/Homology`. Zero Mathlib hits.
- `msearch.py ... leansearch` query: “Tor amplitude of a complex of arbitrary ring
  sheaves is detected on a proetale cover and a complementary open closed
  decomposition”. Eight generic etale-locality and sheaf results, no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: searched TorAmplitude,
  torAmplitude, TorInterval, torInterval, interval predicate definitions, and cover,
  closed and local theorem names. Existing finite-coefficient categorical Tor
  interfaces, constant-coefficient pro-etale predicates and principal affine cover
  lemmas do not state this arbitrary-ring-sheaf assertion. The generic tensor was
  found and reused. `ProEtaleTorLocalGlobal` has private generic small-model cover
  helpers, but its public theorem is finite Tor dimension on quasi-compact X with
  constant coefficients, not the two fixed-interval detection assertions here.
- Exact item id search in `lean/WeilConjectures`: no match. Exact new declaration
  search in Mathlib, both project trees and `dag/lean_names_upstream.json`: no match.

Validation: scompile was invoked twice. The captured second invocation failed while
compiling the existing imported `Sheaf.CategoryTheory.SiteInverseImageTensor`, before
reaching this module. Both local overlay and automatic SERVER CONFIRMATION report:
`object file .../WeilConjectures/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.olean
of module WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings does not exist`.
Reading that exact current server module with `scompile.py --source` succeeds and
confirms the source exists; this is a missing published build artifact, not a missing
mathematical declaration to be replaced. No library, artifact or launcher tool was edited.

## Second reading by Q87

Author's self-check, not an independent review: reopened the written node and file
and matched the two conjuncts against clauses (i) and (ii). Each local and global
condition tests every degree-zero module outside the same interval; all ring sheaves
on sources are actual inverse images. The cover's QuasiCompactCover condition is the
pro-etale topology's covering condition, not a finite-cover hypothesis. The geometric
hypotheses and complementary range condition match clause (ii). The derived category
is uncompleted and unbounded. Formatting was adjusted to keep every line at most
100 characters. At that earlier attempt the compiler infrastructure failure prevented claiming
that the signature elaborates; independent review belongs to the maintainer.

Delivery dry run: `deliver2.py ... --no-push` also stopped before this theorem and
pushed nothing. Its server confirmation advanced to the existing
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` but then failed at import processing:
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean` does not exist.
This is a second missing upstream build artifact in the published import closure.
The local static checks found no overlong lines or mismatched delimiters, and the
node's recorded signature exactly matches the file.

A further prescribed scompile retry again failed before checking this module. The
local overlay additionally reported missing `WeilConjectures.Mathlib.CategoryTheory.
Sites.SheafHom.olean`; SERVER CONFIRMATION again failed on the missing
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean` in
`ProEtaleInverseImage`. This persisted across direct compile and delivery dry run.
Restoring published upstream build artifacts is outside this worker's read-only
library permissions; the module, node record and report remain in the sandbox.

## Saved-packet retry, 2026-10-21

Retained the prior packet and began with the prescribed `deliver2.py Q87
lem-sfb-tor-interval-local-detection --no-push`. It failed before elaborating the
item: the overlay and SERVER CONFIRMATION both reported the missing published
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients.olean`
while loading `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleObject`.
A direct prescribed `scompile.py` retry failed on that same missing artifact.
Reading the current upstream module with `scompile.py --source` succeeded.

A further `deliver2.py --no-push` retry advanced the server-side cached overrides,
but still failed before checking this item. Its SERVER CONFIRMATION reported:
`Sheaf/AlgebraicGeometry/ProEtaleOperations.lean:6:0: error: object file
'/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/
SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.olean' of module
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
does not exist`.

The source import closure was checked: `ProEtaleConstantRingOperations` reexports
`ProEtaleOperationsCanonicalAdjunction`, which imports `ProEtaleOperations`;
that owning module imports `ProEtaleInverseImage`, whose public import is the
missing finite-coefficient Defs module. The item uses the owning declarations
`proEtaleRingModules`, `proEtaleRingDerivedPullback`, and
`proEtaleSheafInverseImage`. This is a missing published build artifact in the
required existing interface, not a missing notion or an elaboration diagnostic
for the packet. No launcher tool, live source, build artifact or import was
modified; no push was attempted. The statement signature still matches its
record verbatim, autoImplicit is false, and the Lean maximum line width is 83.

## Current-source repair and self-check, 2026-10-21

The saved packet was retained and the prescribed dry run run first. Its import
closure advanced past the formerly missing artifacts, but failed in the existing
`Sheaf.Paper.IntegralScalarExtensionWellDefined` at line 451 on a missing
`SMulCommClass` instance, before elaborating this item. Tracing the source imports
showed that only the paper-specific `WeilTensorProduct` import led to that module.

The existing recorded `lem-weil-pbc-site-derived-tensor-descent` supplies the
smaller `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
module and `SheafOfModules.siteDerivedTensorIndependentCoefficients`. Its full
signature and docstring were opened: it is the resolving-class localization of
flat-term K-flat tensor, determined by the natural representative comparison and
unique-extension property. It applies with site objects in `u+1`, morphisms in
`u`, and coefficients in `u+1`; Mathlib already supplies the relative essential
smallness instance. The statement now uses this recorded derived tensor. The
previous packet's added `def-wf-tensor-product` edge was replaced by the existing
descent node. This is a change of existing derived-tensor presentation, whose
compatible natural isomorphism preserves every displayed `IsZero` condition,
without a mathematical statement change, new node, or dependency-node repair.
No live source, build artifact, or launcher script was edited.

Author's self-check reopened the node, source proof, and complete Lean signature.
The arbitrary scheme and ring-sheaf binders, unbounded derived object, ordered
integer interval, all-module tests, fpqc weakly-etale cover condition, both
immersion hypotheses, quasi-compact open, and complementary-range equation
match the node clause by clause. Every local ring is the actual inverse-image
ring, and its identification in pullback is the identity. The empty-cover,
empty-stratum, zero-coefficient, single-degree, and negative-degree cases are
retained. All variables and the universe are explicitly bound; autoImplicit is
false. The proof remains one named theorem with `sorry`. Independent review
remains the maintainer's, as required by this dispatcher brief.

Validation after this repair: prescribed `scompile.py` compiled the sandbox and
library module cleanly (4.6 s and 4.3 s). The prescribed `deliver2.py --no-push`
then printed `OK (dry run): commit cb8ce4cd9fb passes the preflight and compiles;
nothing pushed`. No non-sorry compiler warning was reported. The earlier
artifact/overlay failures recorded above are historical and are superseded by
this successful compile and preflight.
