## What changed

Completed `AlgebraicGeometry.parameterRoot_punctured_cover_tower` with its original signature
and all original definitions unchanged. Constructed the actual power transitions and labelled
root inclusions, proved the finite and refinement monomial bases, localized the maps and
universal property, established finite etale faithful flatness, and assembled the full
spectrum limit and singleton pro-etale cover. Degree one, empty tuples, zero rings and
nilpotent denominators are included.

Added five fully proved helper modules under `Sheaf.RingTheory`: `ParameterRootAlgebra`,
`ParameterRootColimit`, `LocalizationColimit`, `ParameterRootLocalization`, and
`PresentedRingColimit`. Their constructions reuse the existing finite root quotient and
actual compatible-root quotient. New data are constructed, never selected from a postponed
existence theorem. The supplied eleven-step proof route is retained. The only shorter
subargument obtains transition etaleness from the etale levels by restriction of scalars.

Updated the parent proof node and attached a new node to each helper module. The public
imports and original declaration signatures are unchanged. Change record:
`coord/changes/A2-parameter-root-tower-proof-api.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.parameterRoot_punctured_cover_tower`
(node `lem-sfb-parameter-root-punctured-cover-tower`).
Added zero holes. There are no `sorry` declarations in any of the six delivered modules.
All five helper modules are fully proved, including the monomial basis, refinement basis,
localization comparison, compatible-root colimit and scheme limit universal properties.
This is a proof from the existing unit-binomial and etale comparison statements, rather
than a decomposition into new postponed theorems.

Validation: all six modules compile individually in import order through `lcompile.py`;
all are below the 60-second single-file limit. The delivery preflight additionally probes
the declaration axioms. Existing imported statements may still rest on their assigned
holes, as intended by stage 3.

## No longer needed

Removed direct private imports from the assigned module:
`Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale` (used through ParameterRootLocalization),
`Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras`,
`Sheaf.RingTheory.IndEtaleUniverseTransport`,
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.LinearAlgebra.TensorProduct.Defs`,
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`.
The required Mathlib material is supplied by the proved helper APIs and retained imports.
The two Sheaf wrapper imports are replaced by the adopted source ring-map colimit API and
the universe lift of the actual divisibility index; no source declarations are removed.
The final proof needs no separate tensor-product calculation or explicit etale-covering
composition lemma. The monomial basis faithful-flatness API and Algebra.Etale.comp perform
those steps directly. Thus the parent drops direct dependencies
`def-weil-pbc-module-tensor-product`, `lem-weil-pbc-etale-covering-composition`,
`lem-weil-pbc-morphism-affine-schemes-affine`, and the low-level definitions now recorded
on helper nodes. The monic quotient, unit-binomial, directed-colimit, and spectrum-limit
facts remain needed through helper nodes, and are not claimed pruned from the library.
Removed obsolete top-level tool-use approvals for monic quotient, unit binomial,
etale covering composition, directed colimit, spectrum limit and affine-scheme morphism
from the parent after recording actual direct dependencies. The former two and colimit
facts remain represented through the appropriate helper nodes.

No module is withdrawn or deleted. No global unreachability claim is made for the
wrappers or general lemmas, since other targets may still use them.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. `TameRootOrder` is a subtype of naturals and its inherited
order is numerical, whereas this diagram requires divisibility. A separate wrapper supplies
the correct order; its universe lift meets the source filtered-colimit API's universe
requirements. In the zero coefficient ring the basis construction must use a subsingleton
linear equivalence instead of a degree calculation; the proof handles it separately.
The current latest blueprint's paragraph (3) uses the open direct-image result as a black
box; this item's more detailed extracted tame-boundary subargument is retained intact.

## New nodes

`lem-sfb-simultaneous-root-algebra-api` attaches the fully proved finite quotient and
refinement API, especially `Algebra.ParameterRoot.exists_basis`.

`lem-sfb-compatible-root-quotient-colimit` attaches the actual full-quotient universal
property `Algebra.ParameterRoot.full_isColimit` and divisibility-index construction.

`lem-sfb-localization-presented-colimit` attaches the fully proved common-denominator
localization API `Algebra.LocalizationColimit.existsUnique_lift`.

`lem-sfb-simultaneous-root-localization-api` attaches the localized finite faithful flat
and etale calculations, especially `Algebra.ParameterRoot.punctured_etale`.

`lem-sfb-presented-ring-colimit-geometry` attaches the categorical assembly, especially
`Algebra.PresentedRingColimit.faithfullyFlat_indEtale` and its scheme limit property.

Each node has source, a complete proof in words, three recorded kinds of Mathlib search,
its exact primary declaration signature, and all declarations of its helper module.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
