## What changed

Replaced the entire proof hole of
`AlgebraicGeometry.ringComplex_cech_baseChange_quasiIso` by a proof from two strictly
smaller statements, in new modules `Sheaf.Paper.RingComplexCechScalarModel` and
`Sheaf.Paper.RingComplexCechAugmentationHom`. The existing theorem's signature,
visibility, options, and docstring are unchanged. No existing definition, target,
source-library declaration, or consumer changes.

The scalar-model theorem concerns only P and its actual extension; it has no target
complex L and no comparison χ. The Hom theorem concerns a single ring, no extension,
no K-flatness, and no quasi-isomorphism conclusion. Neither restates the item. They
isolate original proof steps 1–2 and the augmentation universal property in step 3.

The combining proof uses pure-tensor extensionality to turn the normalization into
the cochain equation χ ≫ εL = εE. Surjectivity of the Hom map constructs an inverse
ψ in the derived category. Its injectivity, separately on the source and target
endomorphism sets, proves both inverse equations. Mathlib's criterion then gives
QuasiIso χ. The witness εE is used only inside this proof; no definition chooses data
from an unproved existence theorem.

## Proved and sorry left

Closed the one original local hole:
`AlgebraicGeometry.ringComplex_cech_baseChange_quasiIso`
(node `lem-weil-pbc-ring-complex-cech-base-change`). The item module has zero holes.

Added two whole-proof holes, each with a complete source-based argument in its
docstring and a matching DAG node:

- `AlgebraicGeometry.ringComplex_cech_scalar_model`
  (`lem-weil-pbc-ring-complex-cech-scalar-model`).
- `AlgebraicGeometry.ringComplex_cech_augmentation_hom_bijective`
  (`lem-weil-pbc-ring-complex-cech-augmentation-hom`).

This is a decomposition, not a sorry-free proof or positive net hole reduction:
one upper hole closed and two lower holes added. The two remaining arguments are
finite localization-model transport and localization-cone orthogonality.

Edge cases were checked mathematically before stating the lemmas: I=0 with an empty
list gives A[0]; I=A gives the zero derived object; zero or nilpotent denominators
give zero localizations; repeated generators obey the same localization maps; the
zero ring is included. Nonflat ring maps are allowed because scalar transport uses
K-flatness of P, rather than exactness of arbitrary scalar extension.

## No longer needed

Removed these five proof imports from the item:
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`,
`Sheaf.Paper.RingComplexCechData`, and
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
The model data already comes through the public semilinear-extension import. The
resolution, bounded-flat, localization-flat, localization-base-change, and K-flat
change-of-rings nodes remain needed by the scalar-model argument; they are recorded
on its node rather than imported by a proof that does not yet use them. The tensor
construction remains part of K-flatness. No mathematical dependency or module is
claimed globally pruned or withdrawn. The new Hom theorem needs neither scalar
extension nor K-flatness. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing dependency declarations supply generic flatness, localization tensor
identifications, K-flat resolution, and preservation of quasi-isomorphisms. Their
signatures do not state the augmented-model transport or augmentation Hom bijection.
Those two missing steps are now stated explicitly; the supplied plan itself is
mathematically retained. The scalar-model docstring also spells out the comparison
with every generating list required by the actual model predicate, rather than
only the image of one source list.

The nearby `ringedExtendedCech_reflector_core` concerns derived completeness via
internal Hom, while the required statement is torsion coreflection via tensor.
The flat ringed Čech unit comparison assumes flatness and a quotient isomorphism,
which the item does not assume. Neither can substitute for these steps. Mathlib's
`localCohomology` is an Ext-colimit construction, not this augmented derived model.

## New nodes

`lem-weil-pbc-ring-complex-cech-scalar-model`: Stacks dualizing.tex Tag 0ALZ and
algebraization.tex Tag 099D(c). It states existence of the normalized augmentation
and preservation of the Čech model under scalar extension of K-flat P. The original
generic dependencies are retained here. The fraction isomorphism, K-flat roof,
augmentation equality, and generating-list refinement are spelled out.

`lem-weil-pbc-ring-complex-cech-augmentation-hom`: Stacks dualizing.tex Tag 0A6R.
It states the derived Hom bijection between two models for the same finitely
generated ideal. The proof contracts generator localizations, filters the
augmentation cone, applies localization/restriction adjunction in all shifts, and
uses the triangle Hom sequence. Searches used LeanSearch, LeanFinder, Loogle,
and source grep; no existing declaration states either step. The current blueprint
searches for the Stacks labels and augmented localization found no duplicate node.
No change record is needed: no existing public interface was changed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
