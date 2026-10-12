## What changed

Proved `Algebra.existsUnique_isIdempotentElem_of_henselianRing` in
`lean/Sheaf/RingTheory/HenselianIntegralIdempotentLifting.lean`, preserving its signature
and all existing public imports. Added proof-only imports of
`Sheaf.RingTheory.EtaleSectionLiftingOfGabberRoots` and
`Sheaf.RingTheory.HenselianOfEtaleSectionLifting`.

Five proved private helpers recover the finite-algebra lifting criterion, record
ideal-membership witnesses in finitely generated subalgebras, enlarge such a subalgebra
by a finite set, establish module finiteness, and map extended-ideal membership along
an inclusion. The final proof applies the finite criterion once for existence and
once for uniqueness. Updated the item's node proof, proof_deps and proof_origin to
record the finite-criterion bridge and the implemented finite-subalgebra argument.
The item is not among the unit's realized statement or proof-step nodes; the unit's
route is preserved.

The full module compiled cleanly through lcompile.py. Edge cases need no nontriviality
hypothesis: the derivative at 1 reduces to 1 even in the zero quotient, empty witness
sets use the bottom subalgebra, and no structure map is assumed injective.

## Proved and sorry left

Proved the item's only formerly sorry declaration:
`Algebra.existsUnique_isIdempotentElem_of_henselianRing`
(node `lem-weil-pbc-henselian-pair-integral-idempotent-lifting`).
All five private helpers are proved. No sorry remains in the delivered module;
no new sorry or module is added.

The proof intentionally uses these existing sorry-bearing declarations:
- `Algebra.exists_etale_section_lift_of_gabber_roots`
  (`lem-weil-pbc-gabber-root-criterion-etale-section-lifting`).
- `henselianRing_of_etale_section_lifting`
  (`lem-weil-pbc-etale-section-lifting-henselian-pair`).
They become the next work below this theorem, as required by stage 3.

## No longer needed

No original import or planned dependency was pruned. Both
`lem-weil-pbc-finite-of-integral-generators` and
`def-weil-pbc-henselian-terminology` remain used. Explicit imports of
`Mathlib.RingTheory.Adjoin.FG` and
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` were tested and removed as
redundant: their proved declarations are already available through the required
imports. No other node or module is claimed to be unreachable.

## Where the brief, the DAG or earlier work was wrong

The original proof plan invokes the finite-algebra idempotent criterion as though it
were directly a field of the predicate realizing the terminology node. Mathlib's
`HenselianRing` instead supplies simple-root lifting and a Jacobson-radical condition.
The proof closes this gap using two existing nodes: apply simple-root lifting to
Gabber's polynomial at 1, then use the existing section-lifting implications to
recover the finite criterion. The signature and mathematical statement are unchanged.

The referenced local literature .tex files and unit _section.md are absent on this
machine; the supplied node source descriptions, proof steps, and unit record were
used. No new sourced assertion or sorry was introduced.

## Second reading by F2

1. **Visible changes.** Compared the delivered module and node with the repository
version. The public theorem statement is byte for byte unchanged; only proof imports,
private proof helpers, the theorem proof, and the node's proof metadata differ.
Verdict: pass.
2. **Proof checks.** Compiled the module with `lcompile.py`; it has no local `sorry`,
axiom, unsafe, opaque, extern, implemented-by, or kernel-skip declarations. The target
axiom report contains only the permitted axioms plus `sorryAx` inherited from the two
open proof dependencies. Verdict: pass.
3. **Split statements.** No statement was split off and no new node or declaration was
added. The private helpers are fully proved and are not alternate formulations of the
target. Verdict: pass.
4. **Route and pruning.** The proof uses the finite-algebra criterion bridge, then the
finite-subalgebra reduction, while retaining the unit's realized route. The two added
imports are proof-only; the report records the two redundant Mathlib imports tested and
removed. Verdict: pass.
5. **DAG agreement.** The node proof steps, dependencies, origin, and Lean declaration
match the delivered proof and its imports. Verdict: pass.

No repairs were needed in the second reading.
