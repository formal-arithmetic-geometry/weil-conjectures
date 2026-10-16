## What changed

Added the fully proved module `Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction`
with public theorem
`AlgebraicGeometry.Scheme.exists_affineEtale_finite_colimit_construction`.
It implements the complete finite-family route: large-site strictification, all four
finite site axioms, equivalences, covering and cospan-pullback preservation, the strict
coefficient equations and Arrow comparison, continuity and finite-limit-preserving left
adjoints on `Type u` sheaves, object and arrow set colimits, equivalence to the limit site,
and the exact description of finite colimit covers as images of stage covers. Its final
criterion is `R` covering iff `Finite R.uncurry` and its image covers.

Generalized three unclaimed modules:
`SiteSystemStrictificationCategory` now separates index, object and hom universes;
`SiteSystemFiniteCoverings` and the continuity part of `SiteSystemFiniteSheafTransport`
allow an object universe larger than the hom universe. Finite-cover transport now needs
only finite indexed composition and finite indexed base change. The previous
specializations and existing conclusions are preserved. The unchanged original source of
`SiteSystemStrictificationData`, the direct consumer, compiled against the modified overlay.
No held module was adapted. See
`coord/changes/site-system-finite-large-universes-W4.md` for old/new signatures and users.

The assigned module retains its exact original theorem signature and original hole. It
imports the completed finite construction and proves five private diagnostics:
`labelled_presieve_obstruction`, `labelled_precoverage_no_reflection`,
`finite_fibers_of_finite_cover_reflection`,
`finite_presieve_of_finite_image`, and `finite_cover_reflection_iff_finite_fibers`.
Its final arbitrary-presieve claim is marked `STATEMENT-DISPUTED` for the precise route
failure below. No Challenge declaration changed.

The new construction and all five diagnostics compile. `#print axioms` for the construction
reports exactly `propext`, `Classical.choice`, `Quot.sound`; the five diagnostics and the
categorical construction helpers were checked with the same allowed axioms. Compilation
uses only lcompile.py; the final delivery check is the required deliver3.py dry run.

## Proved and sorry left

Original holes closed: 0 of 1. New holes added: 0. Split-off holes: 0.

The one original hole remains:
`AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation_finite`
(node `lem-weil-pbc-affine-etale-colimit-presentation`). Its signature is unchanged.
The original existential statement as a whole is unresolved. The proof plan's raw labelled
presentation fails its final unrestricted reflection clause; proving the existential would
require a different presentation together with a justification of that stronger clause.

Fully proved new public declaration:
`AlgebraicGeometry.Scheme.exists_affineEtale_finite_colimit_construction`
(node `lem-weil-pbc-affine-etale-finite-colimit-construction`). This is a verified strict
part of the argument. It proves all construction clauses, including the exact stage-image
precoverage and its finite site axioms, with the finite-presieve qualification at the end.
It uses no sorry-bearing dependency. The finite-family proof handles `n = 0` as well:
all finite-index upper-bound arguments include the target stage, even for empty indices.

The new module has no `sorry`. The three modified utility modules have no `sorry`.
The assigned module's only `sorry` is the original named theorem above.

## No longer needed

Removed the assigned module's proof import
`Sheaf.AlgebraicGeometry.AffineEtaleDescentData`
(node `lem-weil-pbc-affine-etale-descent-data`): object, morphism, equality and finite-cover
descent are already explicit hypotheses of the assigned statement. Its entire dependency
branch is unnecessary for this construction. The redundant proof import
`WeilConjectures.CategoryTheory.FinitePrecoverage` is removed; its public wrapper remains
because the statement uses the finite precoverage classes.

The old direct proof dependency `def-weil-pbc-finite-precoverage` is also removed
from the assigned node's `proof_deps`; it remains a statement dependency and a
proof dependency of the new finite construction, so its module remains imported.

Removed `Sheaf.Paper.SiteCoveringIsomorphicFamily`
(node `lem-weil-pbc-site-covering-isomorphic-family`) from `SiteSystemFiniteCoverings`.
A direct finite base-change proof indexed by distinct arrows replaces it and avoids its
unrestricted site axioms. The small-universe `SiteSystemStrictificationData` and
`SiteSystemStrictification` modules are not imported by the new construction; their
underlying explicit pair-category API is reused after its universe generalization.
The generic `FilteredColimitCategories` package is unnecessary here: homs are constructed
directly in the target, and Mathlib's filtered set-colimit criteria verify both colimits.

For completeness, the project-module import closure of the assigned item changes from
169 to 10 modules: 163 old modules disappear and
4 are introduced. This is the local item closure; the global target-closure ledger is
a separate measure and may retain these modules through other branches. Every removed
project module is listed here:

- `Sheaf.AlgebraicGeometry.AffineChartBaseChangeIso`
- `Sheaf.AlgebraicGeometry.AffineChartDirectedRingModel`
- `Sheaf.AlgebraicGeometry.AffineChartTensorComparison`
- `Sheaf.AlgebraicGeometry.AffineEtaleCoveringEventually`
- `Sheaf.AlgebraicGeometry.AffineEtaleDescentData`
- `Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramArrows`
- `Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramDescent`
- `Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects`
- `Sheaf.AlgebraicGeometry.AffineEtalePullbackArrowComparison`
- `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionLargeSets`
- `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionUnit`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteBaseChange`
- `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem`
- `Sheaf.AlgebraicGeometry.EtaleAffineChartDescent`
- `Sheaf.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate`
- `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact`
- `Sheaf.AlgebraicGeometry.FinitePullbackHomDescent`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`
- `Sheaf.AlgebraicGeometry.TensorMapPolynomialPresentation`
- `Sheaf.CategoryTheory.InverseMateEquivalence`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
- `Sheaf.RingTheory.ConormalPolynomialInverse`
- `Sheaf.RingTheory.EtalePolynomialCertificate`
- `Sheaf.RingTheory.EtalePolynomialCertificateColimit`
- `Sheaf.RingTheory.EtaleRingMapConormalCriterion`
- `Sheaf.RingTheory.TensorPolynomialEquationsColimit`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets`
- `WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.AcyclicSwallowing`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGeneratedCover`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeCardinal`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeEnlargement`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeSmallObject`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlus`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf`
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`
- `WeilConjectures.FromJoel.Algebra.Homology.Double`
- `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology`
- `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv`
- `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexLimits`
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`
- `WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex`
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim`
- `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Bifunctor`
- `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits`
- `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor`
- `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism`
- `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Basic`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.Double`
- `WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.Mathlib.Algebra.Polynomial.Laurent`
- `WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Gluing`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
- `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.CommaSites`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`
- `WeilConjectures.Mathlib.CategoryTheory.NatIso`
- `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Over`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.HasCardinalLT`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`
- `WeilConjectures.Mathlib.RingTheory.Adjoin.FG`
- `WeilConjectures.Mathlib.RingTheory.Filtration`
- `WeilConjectures.Mathlib.RingTheory.FinitePresentation`
- `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`
- `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`
- `WeilConjectures.Mathlib.RingTheory.Flat.Localization`
- `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Operations`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.Operations`
- `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal`
- `WeilConjectures.Mathlib.RingTheory.IsTensorProduct`
- `WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG`
- `WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT`
- `WeilConjectures.Mathlib.Topology.Constructible`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.Topology.Stratification`

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the prescribed labelled-pair construction cannot establish the final
covering-reflection equivalence for arbitrary presieves. Finiteness of the covering image
does not imply finiteness of a presieve under an equivalence.

The formal diagnostic takes the induced category on `Σ _ : ℕ, C`, with projection `W` to `C`.
For any object `A`, the arrows from `(n,A)` to `(0,A)` given by `𝟙 A` form an infinite
presieve: its distinct source labels give an injection from `ℕ`. Its image under `W` is
exactly the singleton identity covering. Any precoverage whose covers are finite therefore
fails to reflect this covering. This is precisely the global-labelled category of the
constant identity system on a nonempty category. Stage-cover images are finite, so the counterexample applies to the
precoverage prescribed by the node's proof plan.
`labelled_precoverage_no_reflection` proves the full negation of that reflection
equivalence for every finite-cover precoverage on the raw labelled category.

The second formal diagnostic proves a necessary condition for the unrestricted clause:
if a fully faithful `W` reflects every covering presieve into a finite-cover precoverage,
then each fiber `{B // W.obj B = W.obj A}` is finite. Apply reflection to all lifts of the
identity at `W.obj A`, and inject that object fiber into the covering presieve's arrows.
The raw natural-number labels violate this condition. Two further diagnostics prove
the converse: for faithful functors with finite object fibers, a presieve with finite
image is finite. Consequently the unrestricted reflection equivalence for the finite
inverse-image precoverage holds exactly when the fully faithful functor has finite
object fibers (assuming every target covering presieve is finite). This isolates precisely
what any alternative presentation would have to supply.

These results refute the proposed construction's unrestricted inference. They do not
refute the existential theorem for every possible alternative presentation. Accordingly,
the original statement and hole are retained, and the complete source-supported finite
construction is saved separately. No false helper is introduced to hide the missing step.
The original node also had stale text claiming there was no current Lean attachment;
its proof fields now describe the verified finite portion and this exact gap.

The Stacks sources inspected were official tags 004A, 0A34, 09YL and 0EYL. The finite-family
framework in 09YL supports the completed theorem. The commentary on 0EYL itself points out
the need to address strictification rather than assume base-change is strictly associative.
The local literature files named by the node were unavailable, so the official pages were
read: [004A](https://stacks.math.columbia.edu/tag/004A),
[0A34](https://stacks.math.columbia.edu/tag/0A34),
[09YL](https://stacks.math.columbia.edu/tag/09YL), and
[0EYL](https://stacks.math.columbia.edu/tag/0EYL). Searches used msearch leansearch
(service unavailable), leanfinder, loogle and grep plus Mathlib/source-library rg.

## New nodes

`lem-weil-pbc-affine-etale-finite-colimit-construction` is the fully proved finite-family
construction in `Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction`. Its proof
record follows the five grouped parts of the Lean construction; it adds no hole. It records the
finite qualification explicitly and makes no claim to prove the original unrestricted
existential. Existing node copies record the utility universe/finite-axiom generalizations
and prune the unrestricted isomorphic-family dependency. The change record is
`coord/changes/site-system-finite-large-universes-W4.md`.

## Second reading by W4

1. I compared every delivered module with the repository version. The assigned theorem signature is byte-for-byte unchanged. The utility API generalizations and the new finite construction are declared in `coord/changes/site-system-finite-large-universes-W4.md`; no unrelated held module was adapted. Verdict: pass.

2. I compiled all sandbox modules with `lcompile.py`. The construction and diagnostics compile without errors, and the only `sorry` is the original named theorem. The unchanged direct consumer `SiteSystemStrictificationData` also compiled against the delivered overlay (`scratchpad/second-reading-consumer.log`). No forbidden declarations or hollow definitions were found. The construction's checked axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. The added finite construction is a strict, separately named reduction and is not a restatement of the assigned theorem. Its finite-cover qualification is explicit. The private diagnostics are true consequences isolating the arbitrary-presieve obstruction; they add no holes or public interface. An independent leanfinder search for filtered categories, finite presieves and eventual descent returned finitely presentable objects and extensive-site results, none supplying this construction; a fresh `rg` search of both project roots found no duplicate. The sources [004A](https://stacks.math.columbia.edu/tag/004A), [0A34](https://stacks.math.columbia.edu/tag/0A34), [09YL](https://stacks.math.columbia.edu/tag/09YL), and [0EYL](https://stacks.math.columbia.edu/tag/0EYL) support the finite-family route. Verdict: pass.

4. The proof follows the shortest validated route available: the finite-family construction is proved directly, while the unrestricted reflection clause is not asserted. Imports removed from the assigned module and utility modules are listed under `## No longer needed`; the old descent branch is not used. I checked `dag/units/sk-thm-p1.json`: neither removed proof node realizes a required unit step. No unit statement or step is bypassed. Verdict: pass.

5. DAG proof fields and dependencies match the Lean route. The original node remains split with its unchanged statement, and the new construction node records the exact finite conclusion and source. Verdict: pass.

I added this second-reading section and completed `## No longer needed` with the removed direct finite-precoverage proof dependency. No Lean or node changes were needed. Independent compile and axiom-check logs are in `scratchpad/second-reading-compile.log` and `scratchpad/second-reading-axioms.log`; the construction and all five diagnostics use only the permitted axioms, and the unchanged original theorem additionally uses `sorryAx`.
