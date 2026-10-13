## What changed

Proved the existing declaration
`AlgebraicGeometry.exists_ideal_wedge_selfTor_coordinates` from the new, strictly
restricted principal-localization calculation
`AlgebraicGeometry.exists_basic_ideal_wedge_selfTor_coordinates`.
The existing statement, universes, visibility and docstring are unchanged.

The original module now contains complete private proofs of exterior restriction,
exterior scalar multilinearity, extension from restrictions of ambient ideal tuples
to all ideal tuples on a principal open, and descent from principal inclusions to
arbitrary nested affine opens. The denominator proof uses quasi-coherence of the
actual ideal module, the existing affine basic-open denominator lemma, linearity
of the canonical pullback unit, and invertibility of the localized scalar on the
closed inverse-image chart. The descent proof uses Mathlib's
`exists_basicOpen_le_affine_inter`, naturality of both chart maps and both units,
and `Q.isSheaf.section_ext`.

Added proof imports of
`Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`.
The new module retains the three original coordinate-construction dependencies.
Updated the original node's proof, proof_deps and proof_origin to match this route.
No existing definition, public signature, public import or other module is adapted.

Both modules compile locally through lcompile.py. The new statement was checked
mathematically at n=0, f=0, f=1, empty inverse images, the zero quotient and arbitrary
non-finitely-generated ideals: its normalization is for restricted global ideal
tuples only, and none of these cases requires regularity or a Koszul resolution.
The private denominator and descent proofs are uniform in n and do not assume a
nonempty scheme or an integral domain.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_ideal_wedge_selfTor_coordinates`
(node `new-e3-self-tor-ideal-wedge-coordinates`). No sorry remains in that module.

Added one hole, as the entire proof of the named public theorem
`AlgebraicGeometry.exists_basic_ideal_wedge_selfTor_coordinates`
(node `new-u4-self-tor-basic-ideal-wedge-coordinates`), in the new module
`Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates`.

This is a decomposition: one hole closed and one hole added, net zero. It is not
an axiom-free completion of the coordinate construction. The remaining statement
only tests tuples defined on the larger affine chart and only principal affine
inclusions; the complete Lean argument supplies denominator clearing, multilinear
extension and sheaf descent to recover the original conclusion. No data definition
uses a new unproved theorem, and no sorry occurs in a private lemma or definition.

## No longer needed

Removed from the original module the direct proof imports
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`,
`Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections`, and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`.
Their corresponding nodes
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-affine-open-kernel-conormal-sections`, and
`lem-sc-exterior-sheaf-restrict-iso` remain needed by the new coordinate-construction
node and are imported in its module. Thus no module is pruned from the target
closure, and no original proof dependency is claimed unnecessary for the argument.
No extra local-generation, finite-duality, regular-immersion or Koszul-acyclicity
module was imported. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations do not directly state the normalized
coordinate families or their localization equation. The resolution theorem gives
an augmented quasi-isomorphism, the conormal theorem gives its unit-normalized
section equivalence, and the exterior restriction theorem gives an isomorphism;
none alone supplies their compatibility with the fixed derived tensor. This
remaining construction/normalization is explicitly retained in the new node.
The source tags support it: 09PQ gives resolution-independent Tor products, 01R3
identifies the affine conormal, and 06YH gives the K-flat derived tensor. A direct
arbitrary quasi-isomorphism between two K-flat resolutions is not assumed;
comparisons can use a common K-flat refinement over the augmentation.

The searched source and Mathlib contain no exact coordinate theorem usable without
an import cycle. The downstream local-wedge and compatible-map theorems already
import this item and therefore cannot be used to prove it. LeanFinder found ideal
quotient localization and cotangent localization; Loogle found open restriction
interfaces; LeanSearch returned Internal Server Error. Actual searches are recorded
in searches.jsonl. Blueprint search for self Tor localization found no duplicate.

## New nodes

`new-u4-self-tor-basic-ideal-wedge-coordinates` states the shared coordinate-family
construction and its single principal-localization normalization, tested only on
restrictions of ideal tuples defined on the larger chart. Its new module has one
named public theorem with proof exactly `:= by sorry`, a source citation and a
complete natural-language proof. It inherits the original chapter and unit and
keeps the original source, conormal and algebraic normalization dependencies.
The original node cites it before the fully proved denominator and descent steps.
No change record is needed: no existing public interface changes.

## Second reading by U4

1. **Statements and visibility.** Compared the delivered theorem with the repository
statement byte for byte; its hypotheses, lets, conclusion, universes, visibility and
docstring are unchanged. The added basic-localization theorem is strictly smaller:
it restricts the tuple to the larger affine chart and assumes a principal inclusion.
Its node and Lean declaration agree exactly.

2. **Proof and trust.** Compiled both delivered modules with `lcompile.py --all`.
The original hole is closed by the basic theorem, denominator clearing, exterior
multilinearity, common-principal-open refinement and sheaf extensionality. The only
remaining `sorry` is the named basic theorem; no definitions contain `sorry`, and no
axiom, unsafe declaration, or opaque escape is used.

3. **Split statement review.** The basic theorem is a needed intermediate fact rather
than a relabeling of the target: it handles only tuples from the larger chart on a
principal open. Its proof docstring gives the resolution, localization, normalization,
and edge-case argument. Searches using LeanFinder, Loogle and grep found no existing
coordinate theorem with this statement.

4. **Pruning and dependencies.** The proof uses the new basic theorem, the three
quasi-coherence/localization dependencies, and the existing exterior and resolution
interfaces through that theorem. The removed direct imports are no longer referenced
by the original proof. The unit's coordinate construction route remains present.

5. **Edge cases and DAG agreement.** Checked n=0, zero and unit localization, empty
inverse images, zero quotient, and non-finitely-generated ideals against the displayed
formulas. Updated the item's proof, proof dependencies, and proof origin to match the
actual Lean route; the new node records its declaration, source, searches, and split
status.

Changed during second reading: no proof or statement repair was necessary; this report
section records the checks above.
