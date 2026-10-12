## What changed

`ModuleCat.finite_torsion_prime_power_step` now has a genuine induction on the
exponent: the zero case is proved using the subsingleton `ZMod 1` module, and
the successor case is delegated to the new strictly smaller successor-step
statement. `ModuleCat.finite_torsion_property_of_prime` remains proved by
assembling prime powers. The unused finite-abelian-group import was removed.

## Proved and sorry left

Hole closed: `ModuleCat.finite_torsion_prime_power_step`
(node `lem-sbc-finite-torsion-prime-power-step`). This is a decomposition:
the zero case and induction glue are proved, while the successor construction
is split off. Hole added: `ModuleCat.finite_torsion_prime_power_successor`
(node `lem-sbc-finite-torsion-prime-power-successor`). Net holes closed: zero.

Existing hole retained: `ModuleCat.finite_torsion_assemble_prime_powers`
(node `lem-sbc-finite-torsion-assemble-prime-powers`).
`ModuleCat.finite_torsion_property_of_prime` was already proved in the baseline;
its proof is unchanged and is not counted as a newly closed hole. Both upper
proofs still depend on named open statements and hence on `sorryAx`.
There are two original holes, one closed and one retained, plus one new hole.

## No longer needed

Removed `Mathlib.GroupTheory.FiniteAbelian.Basic` from the induction module and
the new successor module does not import it either. The new successor module
uses `ModuleCat.Basic` instead of `ModuleCat.Abelian`, since its signature needs
only the category structure. No existing proof-dependency node is removed: the
old prime-power node had no dependencies and the extension node still uses both
assembly and prime-power induction. No project module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The original prime-power node hid a substantial successor construction. It is
now represented explicitly by the new successor node, while the zero case and
induction glue are proved here.

## New nodes

`lem-sbc-finite-torsion-prime-power-successor` is stated in
`lean/Sheaf/Algebra/FinitePrimePowerSuccessor.lean` and records the canonical
short exact sequence argument needed for the successor case.

## Second reading by N1

1. Compared the complete induction-module diff against the repository. Every
   existing signature and visibility is byte-for-byte unchanged. Only the
   prime-power proof and its plain proof-only import change; the assembly
   statement and proof and the already-proved property theorem are unchanged.
   No existing definition is changed and no change record is needed.
2. Compiled both delivered modules in import order with `lcompile.py`. Checked
   both named remaining holes, absence of forbidden declarations and hollow
   definitions, and printed axioms of all four declarations. Only the standard
   axioms and `sorryAx` from the two reported holes occur; there is no data
   chosen from an unproved existence statement.
3. Read the successor statement and its canonical maps. It is a genuine fixed
   successor reduction with the additional induction hypothesis, strictly a
   part of the original induction, not a renamed copy of its conclusion.
   Checked `e = 0` (zero left term and identity quotient), `e = 1` and `r = 2`
   (inclusion of even classes and reduction modulo two). Primality excludes
   `r = 0, 1`, so cancellation is valid. Repeated LeanFinder, Loogle and focused
   Mathlib/upstream/Sheaf grep searches with new queries: no matching theorem.
4. The Lean proof starts with the zero module and induction and then uses the
   named successor step. No simpler existing theorem was found. The removed
   finite-abelian import is unused. All old proof dependencies remain accounted
   for above. The unit `sk-lem-universal-datum` is preserved: its `realized`
   fields are empty in the baseline, this item is not its key node, and this
   local cyclic-coefficient refinement bypasses no unit step.
5. Read all delivered nodes and the existing assembly node. Their proof steps
   and dependency unions agree with the Lean proof; the new node has its source,
   searches, provenance, chapter/unit, blueprint ancestry and Lean record.
   Corrected literal Unicode escape text in recorded signatures and expanded
   the successor proof into explicit well-definedness, injectivity, surjectivity
   and kernel/image steps.

Second-reading changes: removed the unused `hzero` hypothesis from the new
successor statement and its application (existing signatures unchanged), reduced
that new module's category import to `ModuleCat.Basic`, expanded the new theorem's
proof docstring, repaired node Unicode and search evidence, and corrected the
report to identify the decomposition and zero net hole reduction.
