## What changed

Proved `Polynomial.nonzero_fibre_hypersurface_presentation` in
`Sheaf.RingTheory.PolynomialNonzeroFibreHypersurface`, with its signature and public
imports unchanged. Added proof-only imports of
`Mathlib.RingTheory.LocalRing.ResidueField.Polynomial` and
`Mathlib.FieldTheory.Separable`.

Three fully proved private helpers implement the existing three-step route:
`exists_irreducible_fibre_generator`, `fibre_equiv_of_fraction_generator`, and
`isUnit_derivative_of_separable_fraction`. The generator comes directly from
Mathlib's PID lemma. The fibre equivalence is explicitly constructed from
universal properties, and the unit proof evaluates the fraction-field Bezout
identity. The proof needs no nontriviality hypothesis on S or its localization,
so the zero-algebra edge case is included.

Updated the existing node's proof and proof_origin to describe the actual Lean
argument; proof_deps stays empty. No definitions or existing statements changed.

## Proved and sorry left

Closed the one original hole:
`Polynomial.nonzero_fibre_hypersurface_presentation`
(node `lem-weil-pbc-polynomial-nonzero-fibre-hypersurface`).

Added zero holes; split off zero holes. No sorry remains in the delivered module.
All private helpers are fully proved. The theorem's `#print axioms` output is
exactly `[propext, Classical.choice, Quot.sound]`.

The module compiles with the required local compiler without warnings.

## No longer needed

None. No imports were removed, and the node had no project proof dependencies to
prune. Both added proof-only Mathlib imports are used. The blueprint unit's route
is retained; this node is below its realized statement and steps.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The existing node's three
steps had no named dependency nodes, but each step can be completed from proved
Mathlib declarations and local glue, so no new nodes were necessary.

The Stacks source file is absent from this clone. Read the corresponding source
online at https://stacks.math.columbia.edu/tag/07PU and
https://stacks.math.columbia.edu/tag/07PV. As the existing node already notes,
the general hypersurface packaging is an agent adaptation; 07PU gives the linear
equation case, and 07PV does not state this exact general theorem verbatim.
The completed proof independently verifies the adaptation.

## Second reading by R3

1. **Unchanged interface: pass.** Read the complete repository/sandbox diff of
   the only delivered module. Compared the existing theorem signature as raw
   text: byte-for-byte identical, including universes, typeclasses, hypotheses,
   localization and both conclusions. The three additions are private, fully
   proved helpers. The public imports, definitions and visibility are unchanged;
   the two new imports are proof-only. There is no statement change or adaptation.
2. **Proof and axioms: pass.** Independently compiled the delivered file with
   lcompile.py: exit 0, no warnings (6.2 seconds). Compiled a scratch copy with
   `#print axioms Polynomial.nonzero_fibre_hypersurface_presentation`: exactly
   `propext`, `Classical.choice`, `Quot.sound` (7.9 seconds). Read all three
   helper proofs and both inverse laws. No sorry or forbidden declaration occurs,
   and all data maps are explicit universal-property constructions. The chosen
   polynomial comes from a proved Mathlib theorem, not an unproved existence.
3. **Split statements and edge cases: pass.** No statements or holes were split
   off. The private generator lemma proves primality and nonzeroness before using
   the PID result. The equivalence helper requires no characteristic zero; the
   derivative helper uses precisely separability. Checked the zero-algebra case
   and the case where localization kills S: images of units remain units even in
   the zero ring, and neither inverse construction assumes Q or the fibre is
   nontrivial. For A a characteristic-zero field and r=(X), the construction
   reduces to quotienting S by the image of X, with derivative 1.
4. **Shortest route, imports and pruning: pass.** Independently searched with
   leanfinder (tensor-product/localization formulation), loogle (`Ideal.Fiber,
   RingEquiv`), grep (residue equivalences and fibre quotients), and rg over the
   project and Mathlib sources. The nearby `fiberEquivQuotient` concerns a prime
   of the coefficient ring and a surjective polynomial algebra map;
   `residueFieldMapCAlgEquiv` concerns an extended base prime. Neither directly
   supplies this statement for arbitrary S and nonzero r. The proof already uses
   Mathlib's denominator-cleared generator and `Irreducible.separable`. Both new
   imports are used. The original proof_deps is empty, so “No longer needed” is
   complete. Read dag/units/sk-thm-p1.json: this auxiliary node is not a realized
   unit statement or step; its existing three-step route is retained.
5. **DAG agreement: pass.** Read both node versions and their diff. Only proof
   and proof_origin changed; proof_deps remains empty. The recorded generator,
   explicit fibre equivalence and separability/Bezout steps match the Lean proof.
   The node's statement and Lean signature are unchanged. There are no new nodes
   requiring source, search or statement checks.

Second reading changed only this report by appending the independent review.
No mathematical repair was needed. Confirmed one original hole closed, zero
holes added, zero split off, and no project modules or nodes pruned.
