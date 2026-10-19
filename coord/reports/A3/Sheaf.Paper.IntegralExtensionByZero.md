## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.integralExtensionByZero with its
signature and public imports unchanged. The proof uses existing exactness and
triangulated instances, the derived open adjunction for coproducts, and two new
proved interface lemmas for products and reduction. All private helpers are proved.

The limit argument constructs the kernel of the difference of the two product maps
from an arbitrary existing limiting cone. The existing pretriangulated kernel
preservation theorem and Mathlib buildIsLimit prove preservation without assuming
that arbitrary equalizers exist in the derived categories.

Constructibility follows from the existing constant-model sheaf extension theorem
and the exact-functor homology comparison. A private conversion retains the native
stratification's domains, immersions and local models. Equality transport uses an
explicit API to avoid expanding coefficient inverse images. Minimality of the
localizing closure then applies to the inverse image of the target localizing class.

The retained reduction split-off is now proved. Specialize the existing locally
closed projection formula to j followed by the identity and evaluate its bifunctor
isomorphism at the degree-zero quotient. The point-pullback composition isomorphism
and exact derived pullback identify that coefficient with the quotient on U. The
proof works for every n, including zero, without a separate cone calculation.
The new lemma states precisely the finite-type setting required by the item.

Validation on resuming against current sources (2026-10-19): lcompile.py --all
compiled all three modules without warnings or errors: products 0.8 s, reduction
18.1 s, item 6.5 s. The required delivery checks are run separately by deliver3.py.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.ProEtale.CondensedRing.integralExtensionByZero,
node det-cor-int-compactness-ii-extension-zero.

Also proved both new public theorems:

- AlgebraicGeometry.ProEtale.CondensedRing.condensedOpenExtensionProducts,
  node lem-sfb-condensed-open-extension-products.
- AlgebraicGeometry.ProEtale.CondensedRing.integralOpenExtensionReduction,
  node lem-sfb-integral-open-extension-reduction.

Zero holes added; zero sorry remains anywhere in the three delivered modules.
These are proofs from the existing stated library dependencies, some of which
still have their own sorry. No unresolved obligation is handed on by this delivery.

## No longer needed

Removed direct proof imports from the item:

- Sheaf.Paper.DerivedNakayamaResolution
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
- Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
- Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
- WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
- Mathlib.CategoryTheory.Monoidal.Mod
- Sheaf.SixFunctors.IntegralTensorInverseImage
- Sheaf.Paper.CartesianCoefficients
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

Exactness and the derived adjunction already exist for the precise condensed
extension functor, so the item's proof does not reconstruct them through the
internal-module equivalence or arbitrary ringed-open-closed formalism.
The product lemma still uses the arbitrary-ring product theorem and reduced
complement, as recorded in its node. Its own imports of
Sheaf.Paper.IntegralDerivedCoefficientData and
Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme were also removed: the
needed general constructions already come from its remaining imports. No whole module is claimed globally
unreachable without the maintainer's reachability calculation.

The direct reduction proof no longer uses det-pe-derived-nakayama-resolution's
cone comparison: the existing det-lem-int-tensor-projection supplies the natural
comparison for all n. The coefficient definitions still come from the resolution
module through IntegralDerivedCoefficientData.

The direct sk-lem-int-tensor dependency is replaced by the constant-model sheaf
extension theorem lem-sf-open-extension-zero-constant-model-constructible, followed
by exactness. It proves the same stratification-and-zero-complement step of the
unit. The new reduction proof also uses det-lem-int-tensor-projection from the
unit sk-lem-int-tensor. Unit statements and mathematical route are retained.

Obsolete top-level tool approvals are removed except
 det-def-localizing-closure-existence, used directly. The item's proof_deps records
only the dependencies of the written proof; generic product and reduction
interfaces have their own explicit dependencies.

## Where the brief, the DAG or earlier work was wrong

The declared sk-lem-int-tensor Lean interface uses upstream boundedConstructible
and finite intermediate coefficient fields. The item instead uses finite constant
scalar models and arbitrary finite extensions. The existing constant-model sheaf
extension theorem supplies exactly the needed assertion. Native Scheme.Stratification
and FiniteLocallyClosedStratification differ, requiring a forgetful conversion.

Mathlib's ordinary products/equalizers preservation theorem assumes all equalizers
exist. The delivered existing-limit argument avoids that extra assumption.
The retained attempt's reduction obligation was stronger than necessary: a proof
under the standing finite-type assumptions follows directly from the existing
projection formula. No existing library signature or definition was changed.

## New nodes

lem-sfb-condensed-open-extension-products, module
Sheaf.Paper.CondensedOpenExtensionProducts: proved existence and preservation of
products in the exact condensed-coefficient derived category. Localization
uniqueness handles independent universe choices; the coefficient restriction is
an exact equivalence. Empty products are included.

lem-sfb-integral-open-extension-reduction, module
Sheaf.Paper.IntegralOpenExtensionReduction: proved natural compatibility with
integral reduction in the standing finite-type setting. Its proof specializes
the existing projection formula and transports the coefficient module from the
point. No characteristic, boundedness, or completeness restriction is needed.
Change record: coord/changes/IntegralExtensionByZero-proof-scope.md documents the
proof-scope commands flagged by the checker. All existing signatures and public
imports are unchanged.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
