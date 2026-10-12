## What changed

The original statement of
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_etale` is unchanged.
The current base also has `GaloisCover.stalk_normalization_etale_local_charts`;
its signature and docstring are preserved and its hole is reduced through two
strictly smaller steps of the existing Stacks route. The existing final theorem
continues to assemble the Etale structure from these affine-chart maps unchanged.
Two non-public proof imports were added:
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood` and
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity`.

A proved private helper `normalization_etale_restrict` establishes etaleness on
`C_U` directly from Mathlib. The pullback of `P -> C` along `C_U -> C` is the
finite etale morphism `P -> C_U`. Integral morphisms have invertible
`toNormalization`, and normalization commutes with the smooth open inclusion.
Cancel these isomorphisms and the pullback/restriction comparison to obtain the
required etale restriction. This argument needs no normality, group or section.

The affine-chart proof constructs the local section by `pullback.lift`, proves its
projection to S is `S.fromSpecStalk s`, and uses the stalk's closed point to
produce a point of the etale neighbourhood above s. It then applies fibre
purity with that witness and the proved etale restriction.

The affine-chart node's DAG proof now records this assembly and the two new proof dependencies.
The original definitions, signatures and docstrings are unchanged. The second reading
replaced the unused public Functoriality import with the smaller public FiniteEtale
import needed by the signatures. The new modules import their planned proof
dependencies non-publicly.
There are no forced adaptations or changes to another existing module.

All three modules compile together through `lcompile.py --all`, without warnings.
Sources read: [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ), local claim;
[0EYI](https://stacks.math.columbia.edu/tag/0EYI), split-section trait test;
[0EY6](https://stacks.math.columbia.edu/tag/0EY6), depth-two extension and flat base change;
[0EY9](https://stacks.math.columbia.edu/tag/0EY9), power series full faithfulness;
[0EYE](https://stacks.math.columbia.edu/tag/0EYE), Cartier-divisor purity;
and [0EYB](https://stacks.math.columbia.edu/tag/0EYB), fibrewise dense open purity.

## Proved and sorry left

Closed the current base's hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_etale_local_charts`
(node `lem-sbc-stalk-normalization-etale-local-charts`). The existing final theorem
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_etale` remains proved
from that declaration. The item's module contains no sorry.
The private helper `AlgebraicGeometry.Scheme.normalization_etale_restrict` is
proved without project theorem dependencies.

Two new holes remain, each exactly the whole proof of a named public theorem:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_section_neighbourhood`,
  node `lem-sbc-stalk-normalization-section-neighbourhood`;
- `AlgebraicGeometry.Scheme.stalk_normalization_etale_of_fibre_neighbourhood`,
  node `lem-sbc-stalk-normalization-fibre-purity`.

This is a decomposition: one original hole closed, two lower holes added,
net minus one by hole counting. The two conclusions are separate mathematical
steps: etaleness only on an open containing the local section, and a purity
criterion for arbitrary finite etale punctured covers. The latter has no group,
section, generic torsor or rational-point assumptions. Neither restates the
original theorem. The affine-chart proof performs the necessary section-to-fibre
calculation and supplies the independent Mathlib normalization argument.

## No longer needed

Removed `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality` from
this module and retained only `FiniteEtale`, which supplies the category used in
its signatures. No module is claimed globally pruned from the target closure.
The current base affine-chart node has no old proof dependencies, so there are
no old direct dependency nodes to list as pruned. Generic full faithfulness and
action extension remain in the section-neighbourhood plan; normal depth two and
the flat depth formula remain in the two lower plans. The new modules import
those planned inputs non-publicly. The main theorem still uses the affine-chart
node, as in the current base.

## Where the brief, the DAG or earlier work was wrong

The original local argument relied on generic full faithfulness, action
extension and depth. Those Lean signatures do not include the trait test,
power series full faithfulness, or fibre-purity conclusion. The delivery makes
these missing geometric steps explicit as two items; it does not treat their
unproved status as an obstacle to assembling the original theorem.

During the delivery dry run, the current server base had gained the affine-chart
helper, with an equivalent chart formulation and a sorry. This delivery preserves
that public declaration and closes its actual hole, rather than deleting it or
counting the already-proved final theorem as a new closure. The existing main
node and its proof are preserved.

No mathematical error in the original statement or unit route was found.
The text of `dag/units/sk-prop-input-spreading.json` retains the trait test,
formal section calculation and purity steps; the new decomposition keeps them.
Its `realized` arrays are empty in the supplied repository; this item is not the
unit key node, and the delivery leaves that existing bookkeeping gap unchanged.
The existing module was read whole, as were the four dependency signatures.
Mathlib and both project roots were searched before introducing the two nodes.
Blueprint searches for the section/normalization and fibre/purity combinations,
and for tags 0EYI and 0EYB, returned no matching standalone blueprint nodes.
LeanSearch was unavailable (HTTP internal server error); this is recorded as
unavailable rather than as a negative search. LeanFinder returned etale-locus
and localization statements, and source grep returned no match for the missing
normalization/section or finite-etale purity statements.

Edge cases checked before stating the lower theorems: local dimension zero is
excluded by eta in U and s outside U; relative dimension zero in the formal
calculation needs no power series full-faithfulness theorem; an empty cover is
etale and has a trivial empty normalization; disconnected covers use their
stabilizer components. The neighbourhood assertion does not allow W empty,
because W must contain the explicitly constructed section point. In the purity
criterion the witnessing point similarly forces a nonempty intersection with
the special fibre. Smooth geometrically connected fibres are geometrically
integral, so that intersection contains its generic point. The purity criterion
makes no assertion from mere generic-point etaleness on an arbitrary scheme:
it retains the smooth normal local-base geometry and the actual normalization.

## New nodes

`lem-sbc-stalk-normalization-section-neighbourhood` is realized by
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationSectionNeighbourhood.lean`.
It states only the etale neighbourhood supplied by the tame section test or
formal section calculation, before propagation across the rest of the fibre.
Its docstring explains both dimension cases, localization, splitting, flat
descent, relative dimension zero and disconnected covers.

`lem-sbc-stalk-normalization-fibre-purity` is realized by
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationFibrePurity.lean`.
It states the independent propagation step using an etale open meeting the
special fibre, with no torsor or section assumptions. Its docstring explains
Cartier-divisor purity in dimension one and depth-two/fibrewise purity in
higher dimensions, including identification with the concrete normalization.

Both nodes inherit the original chapter, unit and nearest blueprint ancestor,
record the three searches actually run, and have signatures matching their Lean.
The deliberate public import pruning has change record
`coord/changes/StalkNormalizationEtale-imports.md`; existing declaration
interfaces are unchanged. Its sole importer already imports Functoriality directly.

## Earlier second reading (a previous round; superseded)

1. Compared the whole existing module with the repository using `diff`. Both
   public theorem signatures and existing docstrings are byte-for-byte identical;
   the final theorem body is unchanged. No definitions or target statements change.
   The import replacement is deliberate pruning, and the new signatures need
   only the finite-etale category, not fundamental-group functoriality.
2. All three modules compile without warnings through `lcompile.py --all`.
   The item contains no sorry; only the two reported public lower theorems have
   whole-proof sorries. There are no forbidden declarations or hollow definitions.
   A scratch-copy `#print axioms` checks the helper and both existing declarations,
   plus the two lower theorems. The helper has only standard axioms; the upper
   declarations still depend on sorryAx from the reported lower holes.
3. Read the two lower statements and their proof docstrings against Stacks
   0EYJ, 0EY9, 0EYB and 0EYE. In the DVR case the smooth special fibre is regular
   and irreducible; an etale target open meeting it contains its unique generic
   point, exactly what Cartier-divisor purity needs. In higher dimension the
   punctured open contains every fibre over a depth-at-most-one base point;
   adjoining W makes the closed fibre dense too, meeting 0EYB's assumptions.
   The finite normal extension is identified with the actual normalization,
   not an arbitrary witness. Dimension zero is excluded, relative dimension
   zero reduces to the section, and finite products/empty algebras cause no
   exception. Neither lower statement restates the whole item. Independent
   LeanFinder (extension across a closed fibre) and Loogle (normalization)
   searches and source searches for purity, punctured, tame and power-series
   full faithfulness found no existing theorem closing these geometric steps.
   These are substantial inputs and could not be closed in a few minutes.
4. Reviewed the Mathlib isomorphism/cancellation helper and the explicit
   section-to-special-fibre calculation. They provide a real reduction before
   the chartwise conclusion. Pruned Functoriality to FiniteEtale and kept all
   unit-level mathematical steps. No whole module is asserted globally pruned.
   The unit's already-empty realized fields are recorded above.
5. Checked node signatures against Lean and dependencies against each proof
   step. Found and repaired a circular edge: the new section-neighbourhood
   node incorrectly used the upper affine-chart node as its generic-full-
   faithfulness input. It now uses the actual normal-integral-generic-hom-full
   and generic-fibre-action-extension nodes. Also made both new node Lean
   signature records verbatim and imported their planned inputs non-publicly.

Changes in this reading: repaired the DAG cycle and new signature records,
added the missing planned proof imports, pruned the unused Functoriality import,
and corrected stale report claims about the current base and unit realization.
This remains a decomposition: one existing hole closed, two holes added (net -1),
not an axiom-free proof of the geometric claim.

The first dry run required an import-pruning change record; it is now included.
It also caught extra docstring text in the fibre node signature record, which
was corrected to begin at the actual theorem declaration.

Delivery tooling failure on the second dry run: deliver3.py's
check_import_sources imports refuse_missing and source_roots from import_cycles,
but the read-only repository tools/import_cycles.py does not export
refuse_missing (ImportError before preflight). The first dry run reached
preflight before this launcher/repository mismatch appeared. No tool was edited
or bypassed, and no delivery has been pushed.

## Second reading by E2

1. Compared each delivered module with the repository version. Existing declaration
signatures and docstrings are unchanged; the only interface change is the declared
proof-import pruning from Functoriality to FiniteEtale. The two added declarations
are new split-off statements recorded by matching DAG nodes.

2. Compiled all three modules with `lcompile.py --all`; they compile without errors
or warnings. There are no forbidden declarations or hollow definitions. The item
has no remaining sorry; the two split-off theorem bodies contain only their named
`sorry`s, as reported. The helper is proved and uses only permitted standard axioms;
the upper theorem's axiom output necessarily includes `sorryAx` through the two
open lower nodes.

3. Read both split-off statements and their docstrings against the cited Stacks
arguments and checked edge cases (dimension zero, disconnected covers, empty
finite algebras, and the required fibre witness). Each is a strictly smaller,
true intermediate claim and neither restates the original theorem. Searches in
Mathlib and the project found no existing theorem matching either statement.

4. Reviewed the proof from the target downward. The normalization restriction is
proved directly by pullback and normalization isomorphisms; the affine-chart
assembly uses exactly the two lower nodes and the explicit section calculation.
The Functoriality public import was unnecessary and was pruned; all imports of the
new lower modules are proof-only. The unit route and its listed steps remain in
place.

5. Checked the DAG proof, proof dependencies, proof origins, and Lean signature
records against the actual declarations. The lower nodes carry complete source
and natural-language proof documentation, and the prior circular dependency was
removed. No statement or definition was changed.

Changes made during this second reading: added this required review section only;
no Lean, DAG, or import changes were needed after the prior review.
