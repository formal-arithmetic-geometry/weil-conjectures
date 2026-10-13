## What changed

Closed the original vanishing hole by applying the two existing stated dependencies
in its DAG plan. Retained the instance-sharing repair: derived-cohomology helpers use
Etale.ModuleSheaf with locally cached original instances; the free-sheaf constructions
retain their original raw interfaces and implementations. All 35 original declarations
retain their kind and visibility. Changed interfaces and definitions are recorded in
coord/changes/H4-cohomology-presheaf-instance-sharing.md and unfold to the originals.

The second reader repaired downstream instance inference by making Etale.ModuleSheaf
reducible after elaborating this file. No category instance is registered globally.
Removed the redundant direct FullyFaithful import: the retained public
DerivabilityStructureInjectives import already publicly imports it. The two existing
vanishing dependencies are proof-only imports. No target statement, mathematical node
statement, blueprint unit, new module, or downstream source is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists
(node lem-sbc-constant-module-higher-direct-image-local-vanishing).
No holes remain in the delivered module; no holes were added or split off.
This is a reduction using two existing open dependencies, not a claim that the
vanishing theorem is independent of sorryAx:

- AlgebraicGeometry.Etale.isZero_cyclicHigherDirectImage_of_locally_zero
  (node lem-sbc-cyclic-higher-direct-image-local-vanishing).
- AlgebraicGeometry.Etale.isZero_constantModHigherDirectImage_of_cyclic
  (node lem-sbc-constant-module-higher-direct-image-cyclic-reduction).

The independent axiom check of all public declarations found only propext,
Classical.choice and Quot.sound, except the vanishing theorem, which additionally
uses sorryAx through these two existing dependencies. No data is chosen from an
unproved existence theorem. Every alias uses the original construction; the boundary
homotopy and private cycle-boundary helper are fully constructed and proved.

Independent validation uses scratchpad/second-reading, with a fresh compilation of
the delivered module and byte-for-byte copies of unchanged direct importers. The
original 60-second timeout is unchanged. Making the category reducible repaired
RawTransitionToHom (6.2 seconds); unchanged FreeSheaf then compiled (59.9 seconds)
against the freshly rebuilt module (36.1 seconds). The check of all 35 original raw
signatures passed (39.8 seconds). The final import-pruned version is being validated
again in import order before delivery; final results are appended below.

## No longer needed

Removed the redundant direct import
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful; its declarations
remain available through the retained public DerivabilityStructureInjectives import.
No old proof_deps node is unused. Both dependencies of the vanishing theorem are used.
No module is pruned from the target import closure, and no blueprint step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The prior report claimed that removing the final ModuleSheaf reducibility attribute
preserved all raw interfaces. The second reader rebuilt the module into an independent
scratch overlay and found that unchanged HigherDirectImageRawTransitionToHom and the
raw-signature check failed to infer Category, Abelian and HasDerivedCategory instances
for ModuleSheaf. The previous successful checks had not established compatibility
with that freshly rebuilt artifact. Restoring reducibility at the end fixes inference
without exporting the local instances or adapting consumers.

The previous change record also contained contradictory reducibility wording. It is
corrected to describe the actual final attribute. No compiler tool, timeout, importer
source, or check is modified. All validation copies stay outside the delivery.

## Second reading by H4

1. PASS. Diffed the module and existing node against the repository version. The
   vanishing statement and its hypotheses/conclusion are byte-for-byte unchanged.
   All 35 original declarations remain, with their kind and visibility intact.
   The changed derived helper interfaces/definitions are documented in the change
   record and are definitionally equal specializations of the originals. The existing
   node changes only lean.statement to match its ModuleSheaf interface.
2. PASS. Compiled the module, audited the source for forbidden constructs and holes,
   and printed axioms for its public declarations. There is no sorry or hollow
   definition in the module; only the final reduction depends on the two existing
   open theorems. Independently checked original signatures and unchanged consumers
   against a freshly built artifact, discovering and repairing the inference failure.
3. PASS. No new split-off statements or nodes. Read the two existing dependency
   statements and their complete docstring arguments; neither restates the target.
   Tested their use for d=0 (including e=0), d=1, q=0, empty schemes and the zero ring.
   The helpers merely specialize existing constructions or construct the boundary
   homotopy. A fresh msearch grep using nullHomotopy, single/boundary and local-zero
   terminology found Mathlib's nullHomotopy' and nullHomotopicMap', already used here;
   repository/upstream searches found no shorter complete local vanishing theorem.
4. PASS. Read downward from the target through both existing DAG dependencies. The
   canonical comparison still uses derived adjunction, local cycles/boundaries and
   sheafification; the unit record sk-lem-failure-field and its realized fields are
   unchanged. Removed only the redundant direct FullyFaithful import. No proof_deps
   node, unit step, or reachable module is claimed pruned.
5. PASS. Checked the existing node's lean.statement, proof, proof_deps and proof_origin
   against the implementation. Its mathematical statement is unchanged. The vanishing
   node already records exactly the two-step reduction now written in Lean. No new
   node is needed for an alias or for the generic version of the existing homotopy.

Changed during second reading: restored final ModuleSheaf reducibility, removed the
redundant FullyFaithful import, corrected the report/change record, and added this
independent review. No theorem proof or mathematical statement was changed.
