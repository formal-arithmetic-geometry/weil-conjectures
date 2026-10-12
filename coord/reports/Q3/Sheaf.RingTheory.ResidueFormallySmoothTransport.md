## What changed

Proved `RingHom.residue_formallySmooth_transport` by constructing the ring
equivalence induced by the bijective residue map and applying scalar transport.
Added `Sheaf.RingTheory.FormallySmoothAdicRingEquiv` with the proved theorem
`Algebra.FormallySmoothAdic.of_ringEquiv`. Its proof transports scalar actions,
uses the existing `Algebra.formallySmoothAdic_lift_universe`, and transports the
lift back. Both added proof imports are plain `import`; existing public imports
and the existing theorem signature are unchanged. No definition changed.

## Proved and sorry left

Closed the original hole `RingHom.residue_formallySmooth_transport` (1 of 1).
The second reading also closed the proposed new hole
`Algebra.FormallySmoothAdic.of_ringEquiv`
(node `lem-weil-pbc-formally-smooth-adic-ring-equiv`).
Final delivery: no new holes, no remaining `sorry` in either delivered module,
and no split-off unproved statement. Net holes closed: 1.

## No longer needed

No imports or modules are pruned. The original proof dependency
`def-weil-pbc-formally-smooth-adic` is no longer directly used as a lifting rule
by the residue theorem; its definition remains used in the signature and through
the scalar-transport and universe-lifting proofs. The new direct proof dependency
is `lem-weil-pbc-formally-smooth-adic-ring-equiv`.

## Where the brief, the DAG or earlier work was wrong

The first worker left scalar transport as one more general hole, giving zero net
hole reduction. Its universe adjustment was already available as
`Algebra.formallySmoothAdic_lift_universe`. Reusing that result closes the new
lemma rather than moving the original hole. The node proof is updated to record
this actual route.

## New nodes

`lem-weil-pbc-formally-smooth-adic-ring-equiv` records the proved scalar-ring
transport theorem. No change record is needed: existing interfaces are unchanged.

## Second reading by Q3

1. Compared the existing module against the repository with `diff`: only a plain
   proof import and the proof body changed. The existing signature is byte for
   byte unchanged; no definitions or target statements changed.
2. Compiled both modules in import order with `lcompile.py`. Neither contains
   `sorry`, axioms, unsafe code, opaque declarations or external implementations.
   Explicit axiom probes and the delivery tool's probe check both theorems.
3. There are no unproved split-off statements after repair. Checked scalar
   transport directly: the inverse equivalence makes the algebra compatibility
   equations hold, quotient and power conditions are unchanged. Identity
   equivalences, zero ideals, unit ideals and independent universes require no
   extra assumptions. Repeated searches with LeanFinder, Loogle and local `rg`;
   found and reused the universe-lifting theorem instead of adding another hole.
4. Read the definition, universe-lifting theorem, base-change proof, and the
   private target-algebra equivalence proof. The direct scalar transport is
   shorter than tensor-product base change. Every import serves a statement or
   proof. Read `dag/units/sk-thm-p1.json`: no realized statement or step is
   replaced, and no module on the unit route is removed.
5. Checked both nodes against the Lean. Updated the new node's proof and
   dependencies to the universe-lifting theorem; the residue node records the
   bijective-map equivalence followed by scalar transport. The new node includes
   source, creation, blueprint, Lean signature and search fields.

Changed in this reading: proved `Algebra.FormallySmoothAdic.of_ringEquiv`, added
its plain universe-lifting import, corrected its proof docstring and DAG route,
and corrected the report's hole counts. Kept the original residue proof.
