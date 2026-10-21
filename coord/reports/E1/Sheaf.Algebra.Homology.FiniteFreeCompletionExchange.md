## What changed

The exchange proof is reduced to the ordinary cochain comparison and universal derivation
of the quotient Roos functor. The main module constructs the representative comparison,
descends it along the K-flat resolving subcategory, and proves compatibility with the unit
by the product projections and the two signed cone coordinates. Existing statement
signatures and public comparison definitions are preserved. The quotient, product and cone
coordinate identities determine the comparison maps; the completion pair is universal.
The direct consumer FiniteFreeCompletionExchangeCoherence already explicitly imports the
normalization and site modules removed from this module's public imports.

PrincipalQuotientCompletionExists constructs the strict quotient augmentation, proves its
transition identity and naturality, and obtains the derived unit by the universal property.
It has no holes. Its tensor-unit naturality proof uses an explicit equation for the unit
object before making the localized monoidal structure locally irreducible. This prevents
unnecessary expansion of sheafification and total tensor colimits.

ChangeOfRingsKFlatAllIndependentCoefficients also proves that ordinary
scalar extension preserves every K-flat complex, by extracting the tensor-cancellation
branch of the existing proof; the main module uses it directly. A proved private
biproduct matrix lemma handles the coordinate calculation with abstract objects, avoiding
unnecessary expansion of the chosen products of complexes.

## Proved and sorry left

The original hole of
CategoryTheory.PrincipalQuotientCompletion.finiteFreeCompletionExchange is closed from
smaller statements. CategoryTheory.PrincipalQuotientCompletion.nonempty_model is proved
from exists_derivedQuotientRoos, including the actual construction of its augmentation and
unit. The descent, augmentation-square and exchange-combination helpers are proved.
SheafOfModules.changeOfRings_isKFlat_independentCoefficients proves K-flat preservation
without termwise-flatness and is used for the target completion counit.

Two holes are added, so this is a decomposition, not a net proof closure:

- CategoryTheory.PrincipalQuotientCompletion.exists_derivedQuotientRoos,
  node lem-pur-principal-quotient-roos-derived: universal derivation and K-flat computation,
  without any unit or finite free extension.
- CategoryTheory.PrincipalQuotientCompletion.finiteFreeQuotientRoosComparison,
  node lem-pur-finite-free-quotient-roos-comparison: the balanced quotient tower,
  product and signed cone comparisons before deriving completion.

No definition contains a hole. There was one original hole and there are two newly retained holes.
All five modules compile; the cleaned main module compiled without warnings in 50.1 seconds.
The new statements include rank zero, the arithmetic identity e=1, and arbitrary sections
where no regularity assumption is used. The quotient Roos statement derives the ordinary
cokernel-quotient tensor functor itself and does not assume a two-term Koszul quotient
resolution for a zero divisor.

## No longer needed

The main proof does not use a separately constructed triangulated derived scalar-extension
functor: Mathlib's isIso_of_isLeftDerivedFunctor_of_inverts applies directly to F.universal
and exactness of F.E. Thus lem-sf-exact-functor-derived-triangulated is removed from its
proof dependencies.

Removed direct imports from the item:

- Sheaf.CategoryTheory.StrictTowerArithmeticRestriction (replaced by its definition module)
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Free (replaced by the colimit instances)
- Mathlib.CategoryTheory.Localization.Predicate
- Sheaf.CategoryTheory.SiteCoveringAxioms
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.CategoryTheory.StrictRoosComparison
- Sheaf.CategoryTheory.FiniteFreeScalarCoordinates
- WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Algebra.Homology.ChangeOfRingsKFlat
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.CategoryTheory.StrictRoosAdditiveComparison
- Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance

The flat-term-only lem-pur-kflat-change-of-rings is replaced by the proved independent-universe
K-flat-preservation lemma. Its tensor-cancellation argument requires no termwise flatness.

The finite-coordinate, additive-cone and arithmetic arguments remain needed by the cochain
comparison node. Tensor cancellation is used by the proved K-flat-preservation module.
K-flat representative invariance and the existing compatible-homotopy theorem remain
needed by the derived Roos node. These are not claimed as globally pruned modules. The original
normalization of strict derived limits is not needed a second time in the descent proof:
the preserved Model and RepresentativeComparison signatures already specify the actual
strict quotient augmentation and signed cone maps. No upstream declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not directly provide the two needed assertions at the stated
interfaces. ChangeOfRingsKFlat has the coefficient universe max u v and requires flat terms;
the item permits an independent coefficient universe and asks for every K-flat
representative. The independent-coefficient version now in the library also retains
the termwise-flatness hypothesis. KFlatRoosRepresentativeInvariance is stated for an
algebra tower, whereas
this module uses the explicitly fixed ordinary cokernel-quotient tensor tower. The new
statements retain these independent universes and the prescribed concrete maps.

The unit equation requires a separate verification using the two cone coordinates. It does
not follow merely from existence of a natural derived isomorphism. The delivered argument
performs that calculation and descends it from K-flat resolutions.

The public import change is recorded in
coord/changes/finite-free-completion-exchange-imports.md. The direct consumer is held by M4; no consumer edit is needed.

## New nodes

lem-pur-principal-quotient-roos-derived is the universal derivation of the fixed ordinary
quotient Roos functor, computed on all K-flat complexes. It has its own module and hole.

lem-pur-principal-quotient-completion-exists constructs the normalized completion model
from that universal pair. Its module proves the statement, including strict augmentation
naturality and the unit's factorization equation.

lem-pur-finite-free-quotient-roos-comparison constructs natural balanced quotient tower
maps and their signed cone and arithmetic comparisons. It is entirely before completion
localization and has its own module and hole.

lem-pur-kflat-change-of-rings-all-independent proves preservation of every K-flat complex
under ordinary scalar extension. It extracts the first branch of the existing independent
change-of-rings proof, whose separate flat-terms assertion uses the removed hypothesis.
Its module has no holes.

Change record: coord/changes/finite-free-completion-exchange-imports.md.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
