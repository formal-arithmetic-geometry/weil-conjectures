## What changed

Repaired the returned delivery against the current interface. The assigned module and
node are absent on the current local and server bases. Restored the original theorem
signature and its node, documenting this in
coord/changes/module-cohomology-fmap-data-target-naturality-reintroduction.md.
The proof-only import is now Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial.
Independence compares D and E with the canonical choices; canonical target naturality
then proves the equality. All writes are in the sandbox; nothing is pushed.

## Proved and sorry left

Closed the originally assigned hole
AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_target_naturality
(lem-weil-pbc-module-cohomology-fmap-data-target-naturality): 1 of 1 assigned holes.
The current base lacks that declaration, so this restoration is not a net closure of
a current-base hole. Added zero holes; no sorry remains in delivered Lean.
The existing moduleCohomologyFMap_independent still contains sorry upstream; canonical
target naturality also rests on the existing composition and basic-properties holes.
These dependencies are not changed or newly stated in this delivery.

## No longer needed

Removed the previous delivery's proof imports and split-off modules
Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataIndependence and
Sheaf.AlgebraicGeometry.ModuleCohomologyFMapTargetNaturalityCanonical.
Their proposed nodes lem-weil-pbc-module-cohomology-fmap-data-independence and
lem-weil-pbc-module-cohomology-fmap-target-naturality-canonical are no longer delivered
or needed by this proof. This does not claim that unrelated current target branches
are pruned. No current-base imports are removed, since the assigned file is absent.

## Where the brief, the DAG or earlier work was wrong

The return describes a changed file, but the current local and server repositories
have removed that file and its node. The current functoriality interface already states
independence and proves target naturality, making the earlier two new holed statements
unnecessary. This repair changes the actual proof route, rather than just rebasing the
previous delivery. The assigned theorem's signature is retained exactly.

## New nodes

Restored lem-weil-pbc-module-cohomology-fmap-data-target-naturality, absent on the current
base. Its proof uses the existing functoriality node and the map definition. The unit
is sk-thm-p1; no unit statement or step is bypassed. The change record is
coord/changes/module-cohomology-fmap-data-target-naturality-reintroduction.md.

## Second reading by E2

1. Interface: `diff -u` confirms the assigned module is absent on the current
   repository base, rather than an existing declaration with a changed signature.
   Compared the restored theorem signature byte for byte with both the node's
   `lean.statement` and the change record's old signature: identical. There are no
   other delivered modules or definitions. The reintroduction is declared in the
   report and change record; it is not counted as a current-base net hole closure.

2. Proof: compiled the sole delivered module cleanly through `lcompile.py`.
   A scratch copy with `#print axioms` reports exactly propext, Classical.choice,
   Quot.sound and sorryAx for map_target_naturality. The sorryAx is inherited from
   existing dependencies, including independence, composition/basic properties
   and the existence construction's dependencies. No delivered sorry, axiom,
   unsafe, opaque, implemented_by, extern, or hollow definition occurs.
   Read ModuleCohomologyFMapData_nonempty and the map definition: the former
   explicitly constructs resolutions, the comparison complex, lift, sections
   isomorphism and invertibility proof. The two choices in this proof are exactly
   those already used in the canonical map definition, and independence determines
   their downstream maps up to equality. No new data is defined from mere existence.

3. Split statements and truth: zero split-off statements remain. Read the actual
   signatures of moduleCohomologyFMap_independent and
   moduleCohomologyFMap_target_naturality in the existing functoriality module.
   Independence applies separately to D and E, with the same h-map in each pair;
   target naturality has precisely phi followed by pushforward(b) on its right.
   Checked Stacks 01F8 and 01FB at https://stacks.math.columbia.edu/tag/01F8 and
   https://stacks.math.columbia.edu/tag/01FB (the local TeX is unavailable): these
   give functoriality and the resolution formula respectively. The source supports
   arbitrary module morphisms b, not just isomorphisms. The identity-b case reduces
   to independence; b=0, zero modules, p=0 and higher p introduce no extra condition.
   An `rg` search throughout lean/Sheaf and lean/WeilConjectures found the two
   existing ingredients and no other arbitrary-data target-naturality declaration.
   No new holed statement needs further Mathlib searches.

4. Route and pruning: the proof takes the existing functoriality interface directly,
   without restating either ingredient. Its public import provides signature data;
   its plain import provides the proof only. Both are used. The report names both
   discarded split modules and nodes. Since the assigned module/node is absent on
   this base there is no current old proof_deps list to prune. Opened
   dag/units/sk-thm-p1.json: this auxiliary node is not a realized unit statement or
   step; the functoriality dependency belongs to the same unit. The unit's realized
   statement and all four step lists remain untouched; no unit step is bypassed.

5. DAG: the single proof step and proof_deps name exactly the existing functoriality
   node (independence and target naturality) and map-definition node (canonical
   choice and unfolding). The Lean statement matches the node's universal claim
   for schemes X,Y, modules G,F,F', h, phi, b, arbitrary D,E and every natural p.
   Checked source, proof_origin, searches, created, blueprint, chapter, unit and
   lean record of the restored node; the module path and declaration agree.

Changes made by the second reader: added this independent review and the explicit
axiom results. The Lean proof, imports, node and change record needed no repair.
