## What changed

Retained and repaired the previous attempt. Proved unboundedLocalizingPullback from
a proved cover/model transport lemma and the existing library APIs. Public
signatures and the canonical shift structure are unchanged. Both modules compile.
The resumed delivery dry run passed compilation and preflight; the compile server
was too busy to answer one axiom probe, which the delivery and merge rerun. Exactness is transported
from mapDerivedCategory. A bounded flat representative proves Tor preservation for
all coefficients uniformly. The localizing restriction is constructed directly from
the defining intersection; a proved support-shrinking argument handles every existing
coproduct in the larger indexing universe.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.unboundedLocalizingPullback (1 of 1 original holes).
Added holes: none. Proved the new theorem
AlgebraicGeometry.ProEtale.pullback_finiteConstantLocalModel, node
new-unbounded-pullback-finite-constant-local-model, in full. Both delivered modules
have zero sorry. The earlier split is now proved within this session; this delivery
is a proof, not a decomposition. Existing imported library theorems may still use sorry.

The new proof uses the base-changed cover with explicit fields. Its first projection
is typed from that chosen cover member before constructing module isomorphisms.
This avoids costly kernel conversion between the cover's projected domain and the
pullback scheme deep inside the monoidal coefficient instances. The same annotation
is used for pulled-back strata in the item module. No definition or signature changes. The main proof docstring now follows the four
actual proof steps and no longer describes the abandoned coefficient-specific route.

## No longer needed

Removed direct imports:

- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.Algebra.Homology.HomologicalComplexLimits
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.Algebra.Homology.BoundedFlatReplacement
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible
- Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
- Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.CondensedConstantConstructibility
- Sheaf.Paper.CondensedModuleDerivedPushpull
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.LocalizingAdmissibleCoefficients
- Sheaf.Paper.LocalizingClosureCtfEqualsBc
- WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

The unused planned dependencies are def-weil-proetale-inverse-image,
def-weil-proper-morphism, det-def-localizing-closure-ctf-equals-bc,
det-proper-image-localizing-principle, lem-kun-grothendieck-derived-coproducts,
lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-bounded-flat-replacement,
lem-pc-sheaf-modules-tensor-closed, lem-pur-ringed-site-grothendieck-abelian,
lem-sfb-pullback-constant-model-constructible, lem-weil-pbc-ringed-topos-kflat-pullback,
sk-def-sfb-derived-categories, and sk-def-sfb-derived-tensor-hom.
The flat-model API directly supplies both directions needed for all coefficients;
internal inverse-image flatness avoids a section-module K-flat comparison; exact
termwise derived functors avoid resolution construction. LocalizingClosureExistence
and Mathlib's full-subcategory APIs replace the holed localizing-functor principle.
Some removed modules remain transitive dependencies of the library APIs; this report
claims removal of direct dependencies only. Removed tool_uses entries are
lem-pur-ringed-site-grothendieck-abelian, lem-kun-grothendieck-derived-coproducts,
lem-pc-sheaf-modules-tensor-closed, lem-pc-kflat-bounded-flat-replacement,
lem-pc-bounded-above-flat-kflat-site, and lem-weil-pbc-ringed-topos-kflat-pullback.

## Where the brief, the DAG or earlier work was wrong

The prior work had a retained proof and a report; its local-model split was still open.
The original earlier attempt had lacked a report and did not compile against current sources.
It also changed public signature expressions to a reducibly equal wrapper; these
changes were reverted. It omitted the import providing constructibility invariance.
The planned integral/field ctf=bc detour is unnecessary: bounded flat representatives
and inverse-image flatness treat all coefficients. The unit realization record is
empty; its inverse-image component remains the theorem proved here.

## New nodes

new-unbounded-pullback-finite-constant-local-model proves preservation of a
single module's finite constant local models under inverse image. Source: the
blueprint's pulled-back-stratification/local-model argument. Empty schemes and covers,
zero modules, and zero coefficient rings cause no extra hypothesis. It leaves the
finite stratification, cohomology bounds, Tor amplitude, and localizing restriction
to the complete proof in the assigned module. No existing definition or statement
was changed, so no change record or forced adaptation is needed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
