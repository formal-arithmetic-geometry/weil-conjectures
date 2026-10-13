## What changed

Proved `AlgebraicGeometry.Scheme.affine_koszul_section_colimit` with its signature and
existing docstring unchanged. The proof follows the spectrum presentation, finite
principal-open cover, existing affine Koszul comparison, and isomorphism transport.
The private `existsFiniteKoszulOpen` and `transportHomColimit` helpers are fully proved.
The latter constructs the transported Type-valued diagram and cocone explicitly and
checks the leg formula and both inverse identities before transporting the colimit.

Added the fully proved module `Sheaf.AlgebraicGeometry.SpectrumStructureRestrictionComparison`.
Its theorem compares the structure complex and full restriction functors, including
Modules.overEquiv. It supplies the chosen localization on the spectrum open subscheme
using the proved localization-transfer helper. It makes no Koszul-tail or colimit claim.
Proof-only `import all Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence` reuses the
existing explicit module equivalence and its inverse localization comparison. No
existing definition, signature, visibility, public import, or target changes.
Declaration-scoped heartbeat options keep each file within the 60-second compile limit.
Both delivered modules compile without warnings; no whole-library build was run.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_koszul_section_colimit`
(node `lem-sc-affine-koszul-section-colimit`).

Added holes: none. Sorries left in delivered modules: none.
The new theorem `AlgebraicGeometry.Scheme.exists_spectrum_structure_restriction_comparison`
(node `lem-sc-spectrum-structure-restriction-comparison`) is fully proved.
This is a proof from existing dependency declarations, not a decomposition into new holes.

The finite-cover proof accepts the empty finite set and thus the empty open. The
comparison theorem assumes neither compactness nor a nonempty scheme/open and applies
to the zero ring. The categorical helper works in arbitrary categories with the given
morphism universe, without boundedness of the object. All data are explicitly constructed
or determined by the localization/equivalence universal properties. No complex or arbitrary
witness is selected from an unproved existence theorem.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare` from the item. Its theorem
remains needed in the new comparison module, so its node is moved to that module's
proof dependencies rather than globally pruned. Every original mathematical dependency
remains used by the delivered proof or its comparison module. Globally pruned nodes and
modules: none. No unit statement or unit proof step is bypassed; the unit record's
realized statement/step arrays are empty, and the original spectrum route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing restriction-square interface concerns localized sites only. The target
uses restriction followed by Modules.overEquiv, so a further conjugation by the localized
overEquiv equivalences is necessary; the new proved comparison supplies it explicitly.
The existing derived-equivalence theorem gives only the forward comparison. Reusing its
explicit private module equivalence supplies the inverse comparison needed for forward
perfectness transport, without restating or adapting any dependency.

Tag 09IR, cited as isomorphism transport in some existing dependency docstrings, actually
states the Koszul detector lemma, not an isomorphism-transport result. The new module
cites the actual Mathlib transport constructions and Tag 08DC for the structure complex.
No inherited docstring or mathematical statement was changed. The Stacks source files
and unit text are absent from this checkout; the unit record was read and Stacks Tags
08DC, 08DD and 09IR were read online. The formal transport proof was written from the
library declarations and Mathlib source. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as a negative search result.

## New nodes

`lem-sc-spectrum-structure-restriction-comparison` records the fully proved structure
object and full restriction comparisons in
`lean/Sheaf/AlgebraicGeometry/SpectrumStructureRestrictionComparison.lean`. Its statement
has no quasi-coherent object, perfect system, compactness, or Hom-colimit assertion.
The source, complete proof, existing dependencies, three actual search kinds, Lean
signature, and parent blueprint route are recorded. No change record is required because
all existing public interfaces remain unchanged.

## Second reading by S3

1. Compared the delivered item module with the repository version. The target theorem signature and existing docstring are unchanged; only proof code, proof-only imports, and local helpers differ. The added module is new and has the declared node.
2. Compiled both delivered modules with `lcompile.py`; both compile cleanly with no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The constructions are explicit and no data is selected from an undetermined existence theorem.
3. Checked the split-off comparison statement against its node and searched Mathlib and the library for an existing declaration. It is a genuine structure/restriction comparison needed by the proof, with no extra quasi-coherence, compactness, or colimit hypotheses.
4. Read the proof from the target downward. The route uses the existing spectrum presentation, finite principal-open cover, affine perfect-open comparison, derived equivalence, and restriction comparison; the transport helper is private and fully proved. No shorter available declaration was found, and no imported node was bypassed.
5. Checked the DAG node, proof dependencies, source/search records, and unit route. The node and Lean statement agree, and the unit's realized statement/step route remains intact.

Changed during second reading: added this review record only; no Lean declarations or statements were altered.
