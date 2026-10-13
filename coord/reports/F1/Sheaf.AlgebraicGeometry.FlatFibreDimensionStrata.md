## What changed

Replaced the sorry in AlgebraicGeometry.exists_fibre_dimension_strata_of_flat_restrict
with a compiling proof from two strictly separate steps: construction of fibrewise dense
constant-dimension opens (Tag 054T), and containment of component generic points in any
dense fibre open (the topological argument implicit in Tag 054U). The proof constructs the
open union in each fibre, applies the generic-point inclusion, and transports membership
using Scheme.Hom.fiberι_asFiber. Added two proof-only imports and their new modules/nodes.
The original theorem signature and all public imports are unchanged.
The cover module also imports the new proved RestrictedFibreLocallyNoetherian module.

## Proved and sorry left

Closed AlgebraicGeometry.exists_fibre_dimension_strata_of_flat_restrict (one original hole).
This is a decomposition, not a sorry-free proof: one hole was added, net 0.
The topology and restricted-fibre lemmas are proved.
No sorry remains in the item module.

- AlgebraicGeometry.exists_fibre_dimension_opens_of_flat_restrict:
  lem-sbc-flat-fibre-dimension-strata-core, FlatFibreDimensionStrataCore.lean.

AlgebraicGeometry.generic_points_mem_dense_open_fibre_of_flat_restrict and
AlgebraicGeometry.isLocallyNoetherian_fibre_of_finite_presentation_restrict are proved,
using Mathlib only. The former uses a private proved noetherian-affine topology helper.

All four files compile in import order through lcompile.py. Empty fibres give vacuous
coverage and density. U empty allows all opens empty in the core; the cover lemma has no
admissible t. On a reducible fibre, the cover argument removes the other finitely many
components in a noetherian neighbourhood; it does not assume an irreducible fibre.
The cover statement contains no dimension assertion or existence of strata. Constant
dimension without density would not suffice (take every V_n empty).

## No longer needed

None. No original imports, nodes or modules were removed; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item had no proof dependencies, despite its proof using two substantial unstated steps.
These are now explicitly stated. Searches of both roots, Mathlib, the DAG and blueprint
found supporting topology/flatness APIs but no complete shorter route. LeanFinder gave
UniversallyOpen.of_flat for the construction and the noetherian-component-open lemma for
coverage; Loogle returned zero hits; LeanSearch was unavailable (Internal Server Error). The checked sources are
https://stacks.math.columbia.edu/tag/054T and https://stacks.math.columbia.edu/tag/054U,
with the construction's references Tags 045U and 02NM. No statement dispute or adaptation.

## New nodes

lem-sbc-flat-fibre-dimension-strata-core records Tag 054T with restriction and fibre
identifications: fibrewise density and dimension, without any generic-point coverage.
Its proof explains the Cohen-Macaulay locus and its relative-dimension decomposition.

lem-sbc-flat-fibre-dimension-strata-cover records that every dense open in a fibre over U
contains its component generic points, with no dimension hypothesis. The docstring gives
the finite-component argument in a noetherian affine neighbourhood.

lem-sbc-restricted-fibre-locally-noetherian is proved from the restriction pullback square,
the residue-field-map isomorphism and LocallyOfFiniteType.isLocallyNoetherian.

## Second reading by F1

1. PASS. Diffed the existing item module against the repository: the sole existing
declaration's signature and visibility are byte for byte unchanged; the changes are its proof
and two plain proof imports. The other three modules are new. There are no definitions or
interface adaptations, and no change record is needed.

2. PASS. All four modules compile locally in import order. A scratch copy with explicit
#print axioms checks found only propext, Classical.choice and Quot.sound for
AlgebraicGeometry.generic_points_mem_dense_open_fibre_of_flat_restrict and
AlgebraicGeometry.isLocallyNoetherian_fibre_of_finite_presentation_restrict. The item theorem
and AlgebraicGeometry.exists_fibre_dimension_opens_of_flat_restrict additionally use sorryAx,
exactly from the reported construction hole. There are no forbidden declarations, hollow
definitions or unreported holes.

3. PASS. Checked the remaining construction against Stacks
https://stacks.math.columbia.edu/tag/054T,
https://stacks.math.columbia.edu/tag/045U,
https://stacks.math.columbia.edu/tag/02NM and
https://stacks.math.columbia.edu/tag/02NJ. It is the dense-open construction part of the
argument; the original conclusion needs a separate locally noetherian component argument,
which is fully proved. This is a real decomposition with one closed and one added hole,
net zero, not a completed sorry-free proof. Empty U and empty fibres are vacuous; a
disconnected fibre with components of different dimensions permits different indexed opens.
The coverage proof works in a noetherian affine neighbourhood, so does not require global
noetherianity or irreducibility. New LeanFinder queries for Cohen-Macaulay fibre dimension
and dense opens containing component generic points, Loogle genericPoints/IsOpen, and grep
CohenMacaulay/relativeDimension/genericPoints_subset found supporting APIs, not a replacement
for the construction. Searched both project roots and the relevant DAG chapter; smooth-only
relative-dimension results do not apply to arbitrary flat finitely presented morphisms.

4. PASS. The item combines the two steps explicitly, and both topology helpers are
proved from Mathlib. All public imports supply names in signatures; new proof dependency
imports are plain imports. The original proof_deps was empty, so the No longer needed list
is complete. The unit sk-prop-normal-form and its realized fields are unchanged; this
construction is below its slicing step and bypasses no unit.

5. PASS after metadata repairs. Read all four nodes against the code and verified
proof_deps equals the union of proof-step uses. New nodes have source, natural-language
proof, creation, blueprint, searches and Lean records. Replaced literal backslash-u sequences
in all four lean.statement strings with the actual verbatim Lean signatures. Removed the
unrelated local-dimension node from the coverage node's stmt_deps. Existing-node changes
remain confined to the permitted proof and Lean fields.

Second reading changed only node signature encoding and the coverage node's extraneous
statement dependency. No Lean proof or statement needed repair.
