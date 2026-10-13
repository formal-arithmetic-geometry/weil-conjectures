## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.ideal_power_quotient_affine_lifting_section` with a
compiling reduction to two strictly smaller constructions. The original signature
and all existing public imports remain unchanged.

Added proof imports for `Sheaf.AlgebraicGeometry.IdealPowerAffineDenominatorMap`,
`Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

The main proof constructs the descent through K with `Submodule.liftQ`, using
`cokernel.condition`; proves the quotient restriction formula by naturality;
extends the resulting affine section map; and proves its scalar formula on every
smaller open using the already proved basic-open localization lemma. This last
step clears a local section's denominator, uses linearity and naturality, cancels
a unit power, and applies sheaf separation. Naturality of the power inclusion and
`hone` finish evaluation on the prescribed section `one n`.

Updated the item's DAG proof and dependencies to this route. New statements and
nodes retain the original sources, Stacks Properties 01PM and 01PQ, and the
Schemes 01I7/01IB affine adjunction and equivalence. These source pages were read.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.ideal_power_quotient_affine_lifting_section`
(node `lem-weil-pbc-ideal-power-quotient-affine-lifting-section`). No sorry remains
in the item's module.

Added exactly two named holes, each in its own module:

- `AlgebraicGeometry.Scheme.ideal_power_affine_denominator_map`
  (node `lem-weil-pbc-ideal-power-affine-denominator-map`). This constructs a
  linear map on sections over the single affine open, modulo a submodule K of
  the annihilator, and proves its scalar identity on restrictions of global
  affine sections. It does not produce a sheaf morphism or an evaluation on
  the local unit. It carries no `one` or `hone` hypothesis.
- `AlgebraicGeometry.Scheme.affine_section_linear_map_extension`
  (node `lem-weil-pbc-affine-section-linear-map-extension`). This is only the
  generic conversion of a prescribed affine linear section map to a sheaf map
  with that component on V. It has no ideal, exponent, annihilator, complement,
  or local evaluation condition. Only its source must be quasi-coherent.

This is a decomposition, not an unconditional proof: one hole closed, two added,
net -1 before accounting for the import closure. The main theorem's proof has no
remaining holes, but its axiom closure still contains `sorryAx` from those two
public intermediate theorems. No axiom or data definition was added.

All three modules compile through lcompile.py; the main module's last compile
was about 13 seconds. The final delivery dry run is recorded by deliver3.py.

## No longer needed

No original import was removed and no module is pruned. The following six old
proof dependencies are no longer direct dependencies of the main proof; all remain
needed by the denominator-map node (the adjunction also by the extension node):

- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-spec-module-tilde-sections`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `def-weil-pbc-module-localization-away`

 No unit statement or realized unit step is bypassed.
The new main proof uses the existing affine-basic-open-localization node to prove
local evaluation directly rather than leaving that part as an intermediate hole.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface correction. The original plan names localization
and tilde ingredients but does not already state the finite monomial denominator
map or its conversion on an arbitrary affine open to the `SheafOfModules.over`
interface. Those two gaps are now explicit items with full proof docstrings.

The affine extension lemma is mathematically the tilde-Gamma adjunction plus
transport along V = Spec O_X(V); its remaining task is this transport and the
component identity, not new mathematics. It deliberately allows an arbitrary
target module, as the adjunction does.

Edge cases checked in the natural-language proofs: empty V or W; zero source or
target; zero ideal (n=1, K=M, zero map and empty complement); unit ideal (n=0,
K=0 and the section multiplication map). The principal-open scalar proof handles
empty W through sheaf separation without choosing a point. No Noetherian or
global compactness/quasi-separatedness assumption was introduced.

Short-route searches used LeanFinder, Loogle, grep, and the source library.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as no match.
The existing upstream affine localization theorem is used directly. Blueprint
searches for affine lifting, affine section maps, and annihilator quotients found
no duplicate blueprint statement for either new node.

## New nodes

`lem-weil-pbc-ideal-power-affine-denominator-map` records steps 1 and 2 of the
original affine lifting calculation, including quasi-coherence of the source
power, the relation calculation modulo K, K's containment in the annihilator,
and the scalar formula only for restrictions of global affine sections. Its
module is `Sheaf.AlgebraicGeometry.IdealPowerAffineDenominatorMap`.

`lem-weil-pbc-affine-section-linear-map-extension` records the independent generic
affine adjunction conversion. Its module is
`Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension`. The scalar-formula
extension on all smaller opens is proved in the main module, not postponed here.

No change record or forced adaptation is required: every existing declaration
retains its signature and visibility.

## Second reading by J1

1. **Visible changes.** Compared each delivered module with the repository version.
   The existing theorem signature is byte-for-byte unchanged; only its proof, imports,
   and author comment differ. The two additional modules and DAG nodes are listed above.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`.
   The main theorem has no `sorry`; the two split statements contain only their named
   `sorry` proofs. No forbidden declarations or hollow definitions were introduced. Scratch-copy
   `#print axioms` checks for all three declarations returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is expected from
   the named split statements. The delivery axiom probe also passed.

3. **Statements and split nodes.** Checked both new statements against their docstrings,
   edge cases, and source lemmas. Each is strictly weaker than the original target and
   independently useful, with a matching node and source, proof, and Lean records.
   Searches found no duplicate declaration in Mathlib or the existing library.

4. **Route and pruning.** The proof follows the unit route through denominator
   construction, quotient descent, affine extension, and basic-open localization. All
   original proof-dependency imports remain used; no realized unit step is bypassed and
   no import or node can be pruned.

5. **DAG agreement.** Compared theorem statements and proof dependencies with all three
   node files. The recorded proof origin and dependencies match the declarations used,
   and both split nodes are marked `status: split`.

Changed only the report: added this second-reader record and enumerated all six
replaced direct proof dependencies under No longer needed. They are retained below
the new split nodes, so this does not claim module pruning.

Repeated searches using “morphism from quasi coherent sheaf determined by module
map on affine open sections” and “clearing denominators yields a map from a power
of a finitely generated ideal into a quotient module” (LeanFinder), “homEquiv”
(Loogle), and annihilator/denominator searches (grep). Results were extensionality,
Nakayama, localization and adjunction ingredients, not either exact new statement.
Read the upstream tilde adjunction and quasi-coherent counit declarations; closing
the generic extension still requires transport to the arbitrary affine-open over
interface. The finite monomial construction remains a substantial separate task.
Independently read [01PM](https://stacks.math.columbia.edu/tag/01PM),
[01I7](https://stacks.math.columbia.edu/tag/01I7), and
[01IB](https://stacks.math.columbia.edu/tag/01IB). These support respectively the
monomial construction, arbitrary-target adjunction, and source identification.
