## What changed

The signature of `Algebra.exists_popescu_append_flat_parameters` is unchanged. Its proof
now uses initial flat coordinates and a parameter-selection theorem. It constructs the
localization map with `Localization.localRingHom` and proves its restriction directly.
It proves the ideal equality using both inclusions: the first coordinate ideal embeds
by polynomial renaming, each selected parameter is the image of an added variable,
and the reverse inclusion follows by mapping `Ideal.map_comap_le`.

Added `Sheaf.RingTheory.PopescuInitialFlatCoordinates`. Its public theorem is proved
from the existing 07E6 declaration. The private helpers prove preservation of geometric
regularity at the prime and bijectivity of the differential map under a field algebra
isomorphism. The proof transports essential finite type and the differential basis to
the image intermediate field, handles prime-characteristic and contracted-prime proofs,
and identifies the map from 07E6 with the canonical localization map.

Added `Sheaf.RingTheory.FlatRegularFibreParameterSelection` for the remaining argument:
selecting parameters in the regular closed fibre and applying 07DY and 00MP to the
appended polynomial map. It requires initial flatness and a regular closed fibre, and
makes no geometric-regularity, characteristic or differential-basis assumptions.

All three modules compile together with `lcompile.py --all`. No existing statement,
definition, visibility or public import changed. No other group's module was adapted.
No data is chosen from a theorem whose proof is missing: all constructed maps and
basis transports use explicit Mathlib constructions and proved bijectivity.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_append_flat_parameters`
(node `lem-weil-pbc-popescu-append-flat-parameters`).

Added and proved `Algebra.popescu_initial_flat_coordinates`
(node `lem-weil-pbc-popescu-initial-flat-coordinates`), including both private helpers
`geometricallyRegular_atPrime` and `differential_map_bijective`.

One new hole remains: `Algebra.exists_flat_regular_fibre_parameter_selection`
(node `lem-weil-pbc-flat-regular-fibre-parameter-selection`). Its proof is exactly
`by sorry` and its docstring supplies the source and complete argument. There are
no holes in the original module or the initial-coordinate module.

This is a decomposition: one original hole closed, one lower hole added, net zero.
The initial-coordinate proof still depends on the existing unproved declaration
`Algebra.exists_flat_polynomialLocalization_of_isGeometricallyRegular` (07E6).
Thus the main theorem is not yet a proof using only the three permitted axioms.

## No longer needed

Removed the original module's direct proof imports:
`Sheaf.RingTheory.GeometricallyRegularOverFieldFlat`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.PolynomialOriginRegularLocal`,
`Sheaf.RingTheory.FlatOverRegular`, and
`Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`.
The first is imported by the proved initial-coordinate module; the other four
remain imports of the parameter-selection module and are needed for its proof plan.
This is relocation of dependencies, not pruning those modules from the target closure.
No mathematical dependency or blueprint unit is discarded; no module is claimed pruned.
The original node's direct proof dependencies now name the two new nodes, whose
proof dependencies retain the relevant planned steps.


The old direct `proof_deps` replaced by the two new nodes are: `def-pc-field-extension`, `def-weil-pbc-essentially-finite-type-algebra`, `def-weil-pbc-flat-ring-map`, `def-weil-pbc-kahler-differentials`, `def-weil-pbc-localization-at-prime`, `def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-regular-sequence`, `def-weil-regular-scheme`, `lem-weil-pbc-criterion-flatness-fibre-noetherian`, `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-flat-over-regular`, `lem-weil-pbc-geometrically-regular-over-field-flat`, `lem-weil-pbc-localization-base-change`, `lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-localization-of-regular-ring`, `lem-weil-pbc-nakayama-local-generators`, `lem-weil-pbc-polynomial-ring-origin-regular-local`, `lem-weil-pbc-regular-local-generators-regular-sequence`. These are retained transitively as definitions or proof-plan steps, except `lem-weil-pbc-localization-of-regular-ring`: the initial-coordinate helper proves regularity of a localization directly from the Mathlib localization-of-localization isomorphism. Its old module can remain reachable through 07E6, so no closure pruning is asserted.

The second reader also removed unused `Mathlib.RingTheory.LocalRing.Module` from the new parameter-selection module.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically sound. Its stated dependencies did not provide
an immediately applicable interface for selection of a subset of generators and
identification of the appended polynomial closed fibre; this is the remaining node.
The existing 07E6 interface uses an intermediate field and a prime-characteristic
instance, whereas the item supplies an external field and positive characteristic.
These differences are now handled by actual Lean proofs rather than new assumptions.

The local literature checkout lacks the cited TeX files. Read the source at
https://stacks.math.columbia.edu/tag/07FH and
https://stacks.math.columbia.edu/tag/07E6; both match the stated route. The new generic
parameter-selection statement uses only the flatness and regular-fibre part of 07FH's
argument, so it does not need its positive-characteristic hypothesis.

Edge cases checked: an empty differential basis is preserved by the image-field
transport; a field closed fibre permits an empty selected parameter family; if r=0,
hys forces the localized maximal ideal to vanish. Repeated generators are harmless
because selection is from their spanning cotangent family. The explicit ideal proof
works for empty families without additional hypotheses. `sk-thm-p1`'s realized
statement and steps are untouched. Blueprint searches found no matching blueprint
statement for either new node. LeanSearch was unavailable and is recorded as such;
LeanFinder and actual Mathlib source grep gave no exact full statement.

## New nodes

`lem-weil-pbc-popescu-initial-flat-coordinates`, in
`dag/nodes/sec-proper-base-change/`, records the proved initial-coordinate step, with
module `Sheaf.RingTheory.PopescuInitialFlatCoordinates`. Its Lean proof uses 07E6
and explicit Mathlib transport and localization arguments. It does not select or
append parameters and does not assert equality of the maximal and coordinate ideals.

`lem-weil-pbc-flat-regular-fibre-parameter-selection`, in the same chapter directory,
records the remaining fibre-parameter argument, with module
`Sheaf.RingTheory.FlatRegularFibreParameterSelection`. It assumes the independently
obtained initial flatness and regular closed fibre, produces selected parameters
and flatness, and gives generation modulo the first ideal. The original module proves
the final ideal equality and the required map restriction from these conclusions.
Both nodes inherit the item's chapter, unit and blueprint ancestry. No change record
is needed because all existing interfaces are preserved.

## Second reading by C1

1. Compared the complete original module by diff and checked its sole theorem signature
   and public imports byte for byte. Verdict: unchanged; only the proof and private
   proof imports differ. The two additional modules are genuinely new. No definitions,
   existing docstrings, visibility, or other groups' modules changed; no change record needed.
2. Compiled all three delivered modules locally. Scratch copies with `#print axioms`
   checked all five declarations, including the two private helpers. Verdict: helpers
   use only propext, Classical.choice and Quot.sound; the three public theorems also
   use sorryAx, precisely because parameter selection and upstream 07E6 remain open.
   Exactly one delivered sorry occurs, in the named parameter-selection theorem.
   There are no forbidden declarations and no holed definitions or arbitrary witness data.
3. Read both new statements and the full natural-language proof of the remaining hole.
   Verdict: true and needed. Initial coordinates do not select parameters; parameter
   selection assumes already established initial flatness and a regular closed fibre,
   drops the characteristic and differential hypotheses, and leaves the final ideal
   comparison to the original theorem. This is a real reduction, not a renamed item.
   For a field fibre choose e=0; t=0 and r=0 are permitted; repeated ys are handled
   by extraction of a subset of their cotangent images. Locality places I₀ in m_L,
   so the fibre is nonzero and quotient generation lifts to m_L=I₀+(selected ys).
   The closed polynomial fibre is at the origin since all appended variables map
   into q, and their ideal over the first residue field is maximal. Thus 07DY and
   00MP apply with the finite nonzero L-module L, without finite type of Λ over k.
   Independently checked Stacks 07FH and 00MP, and inspected the existing interfaces
   for 00NQ, 00OP, 07DY and 07E6. New LeanFinder, Loogle and source searches found
   no exact replacement. Existing regular-quotient kernel parameter lemmas address
   a different construction; the proved minimal-generators theorem covers only the
   parameter-selection component. The full remaining hole cannot be closed in a few
   minutes from these interfaces.
4. Read the proof from the original goal downward. Verdict: it explicitly constructs
   the localization map, proves its restriction, embeds initial generators by rename,
   places selected variables in the contracted prime, and proves the reverse ideal
   inclusion by map_comap_le. The initial-coordinate proof constructs image-field and
   differential transports and reduces to existing 07E6. No shorter full route was
   found. All proof-only imports are private; removed the unused LocalRing.Module
   import. Remaining Sheaf imports in the holed module retain its documented proof
   plan. Expanded No longer needed to enumerate every replaced old direct dependency.
   Read sk-thm-p1.realized: neither its statement nor any realized step is bypassed.
   This delivery is one hole closed and one added, net zero, with no modules pruned.
5. Checked all three node Lean signatures against their modules, proof_deps against
   the union of proof-step uses, sources, status, created metadata, blueprint ancestry,
   chapter and unit. Verdict: consistent. The initial-coordinate steps describe the
   actual Mathlib transports and the original node describes the explicit ideal proof;
   the remaining node describes its sourced unfinished proof plan. Both new nodes
   carry the required fields and distinct strictly partial arguments.

Changes by the second reader: removed one unused private Mathlib import; added
parameter-specific search records to its new node; made the replaced direct
proof-dependency list exhaustive in this report; added this independent review.
No theorem statement, proof body or definition required repair.
