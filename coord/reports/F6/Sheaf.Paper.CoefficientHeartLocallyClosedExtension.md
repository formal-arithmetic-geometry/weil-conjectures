## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_locallyClosedExtension` in
`Sheaf.Paper.CoefficientHeartLocallyClosedExtension`, with its statement, universes,
public imports and definitions unchanged.

An immersion transfers topological Noetherianity by its embedding. Its existing
locally-finite-type instance supplies local Noetherianity, and compactness supplies
`IsNoetherian`. The same facts give quasi-compactness of the immersion and all the
open immersions in the statement. The range of the canonical scheme-image inclusion
is its kernel ideal's support, hence the closure of the original range.

The closed exactness step now uses the already proved
`CondensedRing.closedSupport_lowerStarExact` from
`Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`. It applies to the actual
internal-module `CondensedRing.lowerStar`, with the canonical complementary open.
This avoids constructing another internal/sectionwise module comparison. The open
factor and the composite are exact by existing instances. Whiskering
`ShortComplex.homologyFunctorIso` gives the natural cohomology comparison; the existing
quasi-isomorphism instance and `mapDerivedCategoryFactors` give the last two clauses.

Updated the item's DAG proof, proof dependencies and proof origin. Removed the obsolete
`lem-sfb-proetale-identified-open-closed` tool approval. For the independent reader:
`det-lem-formal-closed-support-adjunction` is used as a generic tool for closed-image
exactness. Its explicit companion declaration `closedSupport_lowerStarExact` is proved
and has exactly the required functor and hypotheses. The coefficient-heart unit does
not supply a second such theorem. The unit's prescribed canonical closure, exact open
and closed factors, and unbounded derived descent are all retained. Please record this
replacement tool use on review; no new tool approval was added by the worker.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.coefficientHeart_locallyClosedExtension`
(node `lem-sfb-coefficient-heart-locally-closed-extension`).

Remaining holes in the item: zero. Holes added elsewhere: zero. Split off: zero.
No statement or definition was weakened or changed.

Validation: the complete theorem compiled through `lcompile.py` with no errors or
warnings after unused proof imports were removed. An additional `#print axioms` probe
reported `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx` from
existing dependencies; this delivery closes the item's own proof hole and adds none.
The temporary probe was removed from the delivered source. The proof handles empty schemes,
zero coefficients and unbounded complexes through the same general constructions.

## No longer needed

Removed these six private proof imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: direct exact-functor
  localization supplies descent, without choosing resolutions.
- `Sheaf.CategoryTheory.SheafTensor`: no explicit tensor/sectionwise comparison is needed.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: no transport of module
  presentations is needed.
- `Sheaf.CategoryTheory.RingedSiteModules`: the existing internal-module instances suffice.
- `Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`: replaced by the proved exactness
  theorem directly for internal condensed-coefficient modules.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the immersion's locally-finite-type instance
  suffices for local Noetherianity.

Removed from the item's direct proof dependencies:
`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`sk-def-sfb-sheaf-tensor`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`def-weil-sheaf-of-modules-category`,
`sk-def-sfb-coefficient-morphisms`,
`lem-sfb-proetale-identified-open-closed`, and
`sk-def-sfb-derived-categories`.
The first is replaced by the direct locally-finite-type argument. The next five belong
to the unused sectionwise-comparison route. The last is replaced by the exact-functor
localization leaf. Definitions that occur in the statement remain statement dependencies;
all original public imports remain. These are local pruning claims: no library module
or upstream declaration is withdrawn, and another consumer may still need them.

## Where the brief, the DAG or earlier work was wrong

The planned sectionwise-module transport was unnecessary: the existing closed-support
adjunction already proves finite-colimit preservation for the precise internal-module
closed direct image in this statement. This is a shorter implementation of the same
exact open/closed closure-factorization route.

The cohomology leaf's recorded qualified name `CategoryTheory.Functor.homologyFunctorIso`
is inaccurate for the pinned Mathlib. Its actual name is
`CategoryTheory.ShortComplex.homologyFunctorIso`; whiskering it by the short-complex
functor produces exactly the required comparison. The leaf's mathematical claim is valid.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
