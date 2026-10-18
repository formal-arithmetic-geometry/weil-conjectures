## What changed

Replaced the proof hole of
`AlgebraicGeometry.Etale.isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative`
with a degreewise geometric-stalk proof. The existing declaration and its public imports
are unchanged. Degree zero uses the actual unit-map comparison with
`localAcyclicityAlpha`; positive degrees use the local-acyclicity vanishing; negative
degrees use the proved nonnegative right-derived-functor theorem. The final step applies
geometric-stalk conservativity and the bounded-below homology isomorphism criterion.

Added and proved `localAcyclicity_strict_fibre_comparison` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityStrictFibreComparison`. It applies the existing
strict-base closed-point localizations theorem to the canonical pointed strict-local
maps, including invertibility of the strict-local map, the first-projection equation,
and the equality of maps to the original scheme.

Added and proved `closedFibre_derivedUnit_target_stalks` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks`. Its proof checks affineness
and qcqs, applies the unrestricted strict-henselization stalk formula, identifies the
pullbacks, and transports the coefficients and cohomology along an isomorphism over X.

Added and proved the generic categorical normalization
`CategoryTheory.Adjunction.derivedPlus_unit_homology_zero` in
`Sheaf.CategoryTheory.DerivedAdjunctionSingleZero`. Its proof derives the actual
unit on single complexes from the existing derived-unit factorization, then applies
the proved single-unit homology comparison and the left-exact degree-zero isomorphism.
This isolates categorical coherence from geometry.

Proved `closedFibre_derivedUnit_zero_stalk_comparison` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm` from that normalization,
exact inverse-image homology naturality, and the ordinary comparison
`closedFibre_unit_stalk_comparison` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm`.
The latter is the only new theorem still containing a hole. Its signature compares
the actual ordinary sheaf unit on stalks with the canonical local-acyclicity map;
it contains no derived categories and assumes no local acyclicity.

The item node now follows the Lean argument; the five new declarations have
matching new nodes. No definition, existing signature, target statement, or consumer
module was changed. No change record is needed.

## Proved and sorry left

Original holes: 1. Closed: the hole in
`AlgebraicGeometry.Etale.isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative`.
The item module now has zero holes.

Added holes: 1, in
`AlgebraicGeometry.Etale.closedFibre_unit_stalk_comparison`
(node `lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ`). Its proof is exactly
`by sorry` in its own module, with source and a complete proof in words. What remains is
the compatibility of the canonical ordinary exchange comparison with strict-local
restriction and the coefficient transports. Existing
`strictHenselizationSectionRestriction_naturality` and
`strictLocalUnderivedMateSections_eq` provide the representative-section identities.
Restriction naturality was also checked experimentally using the representative germ
colimit; that unused private helper is not delivered. The canonical ordinary exchange comparison must be identified with the
degree-zero map in the unrestricted stalk formula; existence of an arbitrary
object-level isomorphism does not establish that identification. The docstring
specifies A via strict-local sections and the inverse pullback along the canonical
strict-local isomorphism, avoiding a separate functoriality assertion under p. The derived-unit normalization
and object-level target-stalk computation are proved separately. The source docstring
gives the pointed-neighbourhood calculation needed for this final morphism equality.

This is a decomposition of the original hole, with one hole closed and one added,
not a net hole reduction. The strict-fibre, target-stalk,
generic derived-unit normalization, and derived degree-zero comparison theorems are
proved, as are all private glue lemmas in the delivered modules. The only delivered
`sorry` is the declaration named above. Existing dependencies may still have their own
holes, as permitted by stage 3.

Compiled the strict-fibre comparison, target-stalk comparison, generic normalization,
ordinary comparison signature, derived degree-zero comparison, and complete item proof through `lcompile.py`.
The item also compiled after removing unused proof imports. The delivery dry run
compiled all six modules and passed preflight, with review class CODEX for the new nodes
and modules. The new statements retain arbitrary geometric
point field extensions. Edge cases checked: zero sheaf, empty geometric fibre, degree
zero, positive degrees, negative degrees, and no properness or torsion hypothesis.

## No longer needed

Removed these proof imports from the item module:

- `Sheaf.Paper.StrictHenselizationFunctoriality`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.
- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The item now imports only the two comparisons its proof calls, exact-derived-functor
compatibility, negative derived vanishing, and geometric-stalk conservativity, in
addition to its existing public imports. The geometry and stalk dependencies removed
from the item are retained where the lower comparison proofs need them; they are not
claimed as globally pruned.

Removed direct proof edges that remain as lower comparison inputs:

- `lem-weil-pbc-affine-morphism-permanence`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-inverse-image-stalk-germ`.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
- `lem-weil-pbc-strict-base-closed-point-localizations`.
- `lem-weil-pbc-strictly-henselian-sections-stalk`.
- `lem-weil-pbc-unrestricted-strict-henselization-stalk`.
- `pqf-def-affine-morphism`.

`def-pc-fibre-product`, `def-weil-pbc-direct-image`, and
`prop-weil-pbc-derived-inverse-image-adjunction` also leave the direct proof list;
they remain statement inputs. These are moved edges, not globally pruned nodes.

`lem-weil-pbc-fibre-product-affine-spectra` is unnecessary for this argument: affineness
of the geometric-fibre projection follows from the affine-morphism base-change property.
No explicit tensor-product presentation is constructed. The affine-morphism definition
and permanence properties remain dependencies of the lower stalk calculation.
No existing Lean module is withdrawn, and no blueprint unit statement or realized proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan's explicit affine-spectrum
calculation was longer than the available base-change argument. The negative-degree
step is supplied directly by the existing proved right-derived-functor vanishing theorem.

Several remote compilation requests returned no server response after their automatic
retries. Successful requests supplied compiler diagnostics and verified the proofs;
these transport failures were not treated as Lean time-limit failures. No launcher
script was edited or bypassed.

## New nodes

`lem-weil-pbc-local-acyclicity-strict-fibre-comparison`: the strict-local fibre geometry
over X, proved in `LocalAcyclicityStrictFibreComparison.lean`. It is a consequence of
the existing strict-base closed-point localizations theorem, with the canonical-map
and equality transports made explicit. It retains the canonical strict-local
isomorphism and first-projection equation needed by the remaining ordinary comparison.

`lem-weil-pbc-local-acyclicity-closed-fibre-stalks`: the target-stalk cohomology calculation,
proved in `LocalAcyclicityClosedFibreStalks.lean`. It includes the qcqs check and all
coefficient and cohomology transports, without any local acyclicity assumption.

`lem-weil-pbc-local-acyclicity-closed-fibre-unit-germ`: the derived canonical
morphism comparison in degree zero, proved in `LocalAcyclicityClosedFibreUnitGerm.lean`.
It combines the generic normalization and the ordinary germ equation by naturality.

`lem-weil-pbc-derived-adjunction-single-zero`: the generic single-object derived-unit
normalization, proved in `DerivedAdjunctionSingleZero.lean`. The existing bounded-below
derived-adjunction and single-unit homology-comparison declarations supply its inputs;
no blueprint unit statement or realized step is bypassed.

`lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ`: the remaining ordinary sheaf
morphism comparison, stated in `LocalAcyclicityClosedFibreOrdinaryGerm.lean`.
It is strictly part of the original proof: it neither asserts a derived isomorphism
nor uses local acyclicity or positive/negative-degree vanishing. It still needs the
pointed-neighbourhood germ calculation described in its docstring.

All five nodes follow Stacks Tag 0GJU within the original blueprint ancestor and unit.
Searches of the blueprint, project library, and Mathlib found no duplicate of these
comparisons. The actual search queries and outcomes are recorded in the new nodes.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
