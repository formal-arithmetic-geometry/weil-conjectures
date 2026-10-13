## What changed

The existing theorem `AlgebraicGeometry.Scheme.affine_open_supported_target_model`
has the same signature and docstring as the repository version. Its proof obtains an
affine preimage and applies the separate torsion theorem to that same preimage.
The two new modules provide precisely those interfaces. The second reader removed
the unused scalar and support hypotheses from the new existence interface, expanded
both new docstring arguments, repaired both nodes and their recorded searches, and
replaced a warned `letI` in the target proof by `let`.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.affine_open_supported_target_model`
(node `lem-sc-affine-open-supported-target-model`).

Holes added and left open:

- `AlgebraicGeometry.Scheme.affine_open_supported_model_exists`
  (node `new-affine-open-supported-model-exists`).
- `AlgebraicGeometry.Scheme.affine_open_supported_model_torsion`
  (node `new-affine-open-supported-model-torsion`).

This is a decomposition, not a completed mathematical proof: one original hole is
replaced by two strictly smaller named holes, so the local hole difference is -1.
The target's proof still depends on `sorryAx`; no claim of positive ledger progress
or of a closed target import closure is made. The final ledger numbers belong to the
maintainer's pinned-baseline calculation. There are no definitions in this delivery
and no arbitrary existence witness is used to define data.

## No longer needed

Removed these four direct proof imports and direct dependencies from the target:

- `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`,
  `lem-pc-open-derived-restriction-comparison`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
  `lem-pc-affine-qcoh-derived-equivalence`.
- `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`,
  `lem-pc-affine-localized-site-derived-transport`.
- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`,
  `new-affine-derived-tilde-homology-comparison`.

These are all four old `proof_deps`. They remain dependencies of the new interfaces:
existence needs restriction, equivalence and transport; torsion also needs the
homology comparison. Thus no module is claimed pruned from the import closure.
The target's direct proof dependencies are now exactly the two new nodes.
Public imports are preserved: they provide its statement's categories and functor.

## Where the brief, the DAG or earlier work was wrong

The first worker's Lean reduction was valid, but the new JSON files copied the full
parent statement instead of stating their individual conclusions; they had empty
proof plans, empty statement dependencies, placeholder `lean.statement` records,
and inherited searches and review fields. The parent node still described the old
proof route. These are repaired. The initial report also called the reduction a
proof without counting the two added holes; the accounting above corrects this.
The underlying interfaces for restriction, affine derived equivalence, transport
and homology comparison do exist; what remains is combining them in Lean for each
new interface, not a missing mathematical premise.

## New nodes

`new-affine-open-supported-model-exists` states only affine preimage existence for
a shifted quasi-coherent target restricted to an affine open. It does not assert
torsion and does not assume support. Its proof plan uses exact restriction, the
affine equivalence, canonical site transport and localization uniqueness.

`new-affine-open-supported-model-torsion` proves elementwise homology torsion for an
already given model with its comparison isomorphism. It asserts no existence of a
model. Its plan transports homology and stalks, identifies the basic open, and uses
the ordinary module localization criterion. No change records are needed: no
existing statement, definition or public import was changed.

## Second reading by H4

1. Compared the delivered target against the repository with `diff -u`; then checked
   the declaration prefix through `:=` byte for byte. Its universe parameters,
   derived-category instances, global scalar, quasi-coherent object, support
   hypothesis, affine open, shift, arbitrary F and comparison, and existential
   conclusion are unchanged. No other existing module is delivered. Verdict: pass.
2. Compiled the three modules in import order with `lcompile.py`, and compiled a
   scratch copy with `#print axioms` for all three declarations. The lists contain
   only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
   The only textual sorries are the two named new theorems, each exactly `by sorry`.
   No axiom, unsafe declaration, opaque, extern, implementation override or hollow
   definition is present. The target's unnecessary `letI` style warning was repaired.
   Verdict: valid reduction with the two explicitly reported holes, not axiom-free
   completion.
3. Read Stacks Tags 06Z0 and 08EJ at
   https://stacks.math.columbia.edu/tag/06Z0 and
   https://stacks.math.columbia.edu/tag/08EJ, including their proofs. The first gives
   affine derived preimages with no support assumption. The second's affine
   paragraph uses elementwise annihilation of the supported target's homology;
   its perfect-source hypothesis is for the later uniform exponent on a map,
   which is not asserted here. Inspected the existing restriction, transport,
   equivalence and tilde-homology modules. Neither new statement restates the
   target: one supplies an object with an isomorphism, the other a property of an
   already supplied object. Tested zero E', arbitrary shifts and unbounded E',
   f=0 (n=1), a unit f (zero homology), and the empty affine open (zero ring).
   No nonempty-open, finite-generation or uniform-exponent assumption is used.
   Searches through `msearch.py` used different wording from the first worker:
   LeanSearch was unavailable; LeanFinder supplied tilde stalk localization,
   Module.notMem_support_iff and LocalizedModule.subsingleton_iff_disjoint;
   Loogle's unqualified liftNatIso query was unknown, confirmed instead by source
   inspection; Mathlib grep and project/upstream grep found components, not either
   exact interface. New node search records now name queries actually run.
   Verdict: true proper substatements, still substantial formalization holes.
4. Read the original planned declarations before assessing the split. They supply
   the mathematical route but no immediate application closes either new theorem:
   existence needs quasi-coherent chart transport and a localization comparison;
   torsion needs the derived homology/stalk comparison before applying the ordinary
   module criterion. Kept that route in both new node plans. The unit record
   `dag/units/sk-thm-picard-duality.json` has empty realized arrays; this item is not
   a unit realization, and no unit or chapter record is changed. Removed all four
   unused direct target proof imports and listed all four old dependencies above;
   they remain under the two new interfaces. Verdict: route retained, direct
   imports pruned, no whole module claimed pruned.
5. Read all three delivered nodes against their declarations and proofs. Replaced
   copied statements with exact separate conclusions, added statement dependencies,
   source-based proof steps and their union as `proof_deps`, exact Lean signatures,
   actual search records and precise blueprint places. Removed inherited review
   fields from new nodes. Rewrote only the parent's proof-owned fields to describe
   its actual two-lemma reduction. Its statement and statement dependencies remain
   unchanged. Verdict: DAG agrees with the delivered Lean and the remaining plans.

Changes from the second reading: warning repair, narrower new existence interface,
complete new docstring proofs, direct proof-import pruning, corrected DAG records
and searches, and explicit decomposition accounting. The existing target statement
was not changed.
