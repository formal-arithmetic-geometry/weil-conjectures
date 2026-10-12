## What changed

Proved `RingHom.isRegular_of_comp_algebraMap_localization` in
`Sheaf.RingTheory.RegularThroughLocalization`, preserving its signature and all universes.
Flatness uses `Module.flat_iff_of_isLocalization`. For each prime of the localization,
Mathlib's surjective-on-stalks residue-field map gives the residue-field isomorphism.
Tensor congruence and compatible scalar actions give the fibre isomorphism, and tensor
induction proves scalar compatibility. Updated the existing DAG proof to match this route.

Added the proved theorem `Algebra.isGeometricallyRegular_of_fieldIso` in
`Sheaf.RingTheory.GeometricRegularityFieldIso`. It transports Noetherianity and the finite
purely inseparable extension tests. `Module.Finite.small` and `Shrink` handle independently
sized universes. The proof uses only Mathlib and the existing GRing definitions.

Both modules compile cleanly through lcompile.py. Edge cases remain covered: zero fibre
rings are allowed; localization at a monoid containing zero leaves no primes to check;
base fields and the two algebras may live in independent universes. No target, definition,
or existing theorem signature changed. The new module has only GRing as a public import.

## Proved and sorry left

Closed the item's sole hole:
`RingHom.isRegular_of_comp_algebraMap_localization`
(node `lem-weil-pbc-regular-through-localization`).

Also proved the new helper `Algebra.isGeometricallyRegular_of_fieldIso`
(node `lem-weil-pbc-geometric-regularity-field-iso`).

No sorry remains in either delivered module. Holes closed: 1. Holes added: 0.
This is a proof, not a decomposition into new unproved statements.

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
The node `lem-weil-pbc-localization-prime-residue-field-iso` and its module
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` are unnecessary for this proof:
Mathlib already proves bijectivity of the induced residue-field map for a map surjective
on stalks. The full prime correspondence, local-ring isomorphism, and ideal transport
clauses are not used. Its subordinate dependencies are no longer needed through this edge;
other callers may still need them.

Also removed the original proof dependency
`lem-weil-pbc-localization-tensor-product`: directly using
`IsLocalization.tensorProduct_compatibleSMul` and
`Algebra.TensorProduct.equivOfCompatibleSMul` replaces the module-localization proof.
The original direct edges to `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-finite-purely-inseparable-extension`, and `def-weil-regular-scheme` now occur
in the proved transport helper instead; their notions remain needed and are not pruned.

No other original imports were removed. A trial import of
`Sheaf.RingTheory.GeometricallyRegularFieldExtension` was removed after directly proving
the universe transport; the proof does not use that module or its dependency tree.
The new helper's redundant proof import `Mathlib.RingTheory.TensorProduct.Maps` was removed.
No unit statement or realized unit step is bypassed (this node is below the unit route).

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan was valid, but its residue-field comparison was already
available in Mathlib through the stronger surjective-on-stalks API. The tensor comparison
also has a direct compatible-scalar equivalence. The original step 5 called universe
transport elementary; the implementation explicitly shrinks each finite field extension
so it fits the universe quantified by `IsGeometricallyRegular`.

LeanSearch returned Internal Server Error and is recorded as unavailable, not as no match.
Loogle and grep searches ran. The local literature checkout contains only indexes; the
source statements were verified from the official Stacks pages for Tags 07PT, 0381, 0382.
No source or project-contract file was changed.

## New nodes

`lem-weil-pbc-geometric-regularity-field-iso` records the proved transport theorem in
`lean/Sheaf/RingTheory/GeometricRegularityFieldIso.lean`. It is strictly the transport
part of the original argument and contains no sorry. Its source is Definition 0382 and
the finite purely inseparable condition of Lemma 0381; the proof is the original node's
step 5 made explicit, including independent universes. No change records are needed:
all existing public interfaces are unchanged.

## Second reading by F3

1. PASS: Compared both delivered modules with the repository. The existing theorem's
   signature, including universes and all instances, is byte for byte unchanged. The
   other module is new. No definition or target statement changed; no change record
   is required. The existing node changes only proof, proof_deps, and proof_origin.
2. PASS: Compiled both modules in import order through lcompile.py without errors or
   warnings. Scratch copies with #print axioms show exactly propext, Classical.choice,
   and Quot.sound for both theorems. No sorry, forbidden declaration, hollow definition,
   or arbitrary witness chosen from an unproved existence theorem occurs.
3. PASS: No unproved statement was split off. Read the new proved transport theorem:
   compatibility builds the pulled-back algebra equivalence; finite purely inseparable
   extensions remain such after restriction along the field isomorphism; Shrink handles
   independent universes; tensor equivalences transport regularity. Zero algebras,
   identity field isomorphisms, and independently sized universes introduce no extra
   assumptions. Repeated searches with leanfinder, loogle, Mathlib grep and local rg.
   Found the analogous proved geometricRegular_of_equiv in RegularRingEquiv and the
   fixed-field helper in QuotientGRing, but both are private and unavailable to imports.
   There is no reusable public duplicate. Corrected the new node's search account.
4. PASS: The route uses proved Mathlib flatness, residue-field and tensor comparisons,
   followed by the proved helper. Each proof import supplies a used API. The report's
   No longer needed section accounts for all removed old proof edges (the three
   definition edges move into the helper). Checked sk-thm-p1.realized: none of these
   removed nodes realizes a unit statement or step; the unit route is preserved.
5. PASS: Read both nodes against the Lean proof. Their proof dependency lists equal
   the unions of step uses, and their proof/proof_origin describe the implemented
   reductions. The new node has the required source, searches, creation, blueprint,
   chapter, unit, status and verbatim Lean statement fields. Its theorem is a strict
   transport component, not a restatement of localization regularity.

Second reading changed only this report and the new node's search documentation to
acknowledge the existing private helpers and record the independent leanfinder search.
The Lean proofs required no repair. Item holes closed: 1 of 1; holes added: 0.
