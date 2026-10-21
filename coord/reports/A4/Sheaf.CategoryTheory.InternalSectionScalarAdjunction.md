## What changed

Proved `CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction`
without changing its statement or any existing public definition. Restriction is the
identity on underlying sections. Extension is the inverse adjunction mate of this
restriction square; the mate unit equation proves its Hom transpose compatibility.
The internal coequalizer generator is a scalar multiple of the unit, so linearity
and the specified section unit prove the required pure-tensor formula.

Added `Sheaf.CategoryTheory.DerivedSectionScalarTransport`, containing the proved
`derived_section_scalar_transport`. This separate localization result takes the
ordinary squares and their transpose compatibility as input. It constructs the
internal universal derived pair by conjugation, transports its Kan extension
property, proves computation on sectionwise K-flat complexes, and compares the
specified derived adjunctions. The scalar pair normalization gives its unit identity
first on flat-term K-flat complexes; naturality along a K-flat resolution proves it
on every complex. The transported ordinary unit square then gives the independently
specified internal derived unit equation.

The item adds private proof imports for adjunction mates, opposite adjunctions,
and the new transport theorem. The new module privately imports the independent
site/monoidal tensor comparison to convert the resolution's categorical flatness
to site flatness. Updated the parent node's proof route and dependencies and added
the transport node. No source-library file, existing signature, or consumer changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction`
(node `lem-sfb-internal-section-scalar-adjunction`).

Also proved the new theorem
`CategoryTheory.InternalAbelianSheafModule.derived_section_scalar_transport`
(node `lem-sfb-derived-section-scalar-transport`). Holes added: zero. Holes remaining
in the delivered modules: zero. This is a proof from the existing declared
change-of-rings and coefficient-adjunction results, not a decomposition into new
unfinished statements. Existing dependencies retain their own proof status.

## No longer needed

Removed these private imports from the item:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`:
  `lem-pc-sites-sheaf-tensor-bilinear-universal` is unnecessary for this comparison.
  The mate identity and scalar linearity prove the generator formula directly.
  Removed this node from the parent's proof dependencies and top-level `tool_uses`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: no direct use
  in the item; the derived transport theorem still uses `lem-pc-kflat-resolution`.
- `Sheaf.Algebra.Homology.SheafRingDerivedHomComparison`: no direct use in the item;
  the existing normalized coefficient adjunction supplies the scalar pair.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: no direct use; the pair's
  homotopy comparison gives the complex comparison, using the quotient factorization.

The original direct dependencies on `lem-pe-internal-section-tensor-comparison`,
`def-weil-abstract-derived-category`, `lem-pc-kflat-resolution`,
`sk-def-sfb-derived-extension-of-scalars`, and
`lem-pur-sheaf-ring-derived-hom-comparison` are replaced by the new transport
result or the existing coefficient-adjunction theorem. The tensor/exact derived
infrastructure, K-flat resolutions and normalized derived Hom theorem remain
needed transitively. No module withdrawal or global removal is claimed.
The scalar-six blueprint unit and its realized steps are preserved.
No existing source-library declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no repair of an existing public definition was required.
Preflight required a change record for the added command scopes and a LeanSearch
entry distinct from LeanFinder/Loogle; both are supplied. The original exported
additive-instance attribute is preserved verbatim.
The planned ordinary tensor-coequalizer comparison was longer than necessary:
adjunction mates provide the canonical comparison, and the generator formula
follows from its unit equation. The first concrete derived transport proof reached the 60-second limit. Profiling
showed expensive elaboration and kernel checking around the reconstruction and
restricted-adjunction data. The final proof uses a generic private localization
theorem and private irreducible constructions with proved unit/Hom APIs in the
same module. This keeps the full argument and compile limit intact. The derived
module then compiled cleanly in 22.3 seconds.

The resolution theorem gives categorical flatness,
so using its terms in the site-flat normalization requires the already proved
site/monoidal tensor comparison; this conversion is explicit in the proof.

## New nodes

`lem-sfb-derived-section-scalar-transport`, in chapter `sec-six-functors-basics`
and unit `sk-prop-scalar-six`, realizes the localization and normalized derived-unit
portion of the original argument. It assumes both ordinary squares and their
transpose identity and proves only the derived conclusions, for an arbitrary
section-ring map. Its module is
`Sheaf.CategoryTheory.DerivedSectionScalarTransport`; its proof is complete.
It does not restate the original theorem: it neither constructs the ordinary
comparison nor proves its identity-on-sections or balanced-generator formulas.
Edge cases (identity scalar map, zero rings, and non-flat scalar maps) require no
extra hypothesis: all constructions use equivalences, exact restrictions and the
existing unbounded derived pair. The change record is `coord/changes/A4-internal-section-scalar-proof-commands.md`;
it records the added proof commands and unchanged public interface and consumers.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
