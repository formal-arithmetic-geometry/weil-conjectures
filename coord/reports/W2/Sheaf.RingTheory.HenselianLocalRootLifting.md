## What changed

Proved `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting` in
`lean/Sheaf/RingTheory/HenselianLocalRootLifting.lean`, without changing its signature,
universes, public imports, definitions, or target statements.

Two private, fully proved helpers implement the argument:
`lift_idempotent_small` handles the hypothesis's `Type (max u v)` quantification using
`ULift` and the induced quotient equivalence;
`factorization_of_lifting` constructs the CRT idempotent explicitly from Bezout
coefficients, lifts it in `AdjoinRoot f`, computes its two images, and invokes
`Polynomial.exists_monic_factorization_of_idempotent`.
The main forward implication splits the reduced polynomial at its simple root,
lifts that coprime monic factorization, and extracts the root from the degree-one
factor by comparing constant coefficients. The reverse implication constructs
`HenselianLocalRing R` with Mathlib's TFAE, obtains the maximal-ideal henselian pair,
and applies integral-algebra idempotent lifting to the finite algebra.

Added proof-only imports `Sheaf.RingTheory.MonicFactorizationOfIdempotent` and
`Sheaf.RingTheory.HenselianIntegralIdempotentLifting`. Both import directions were
checked and neither module reaches this item. Updated the existing node's `proof`,
`proof_deps`, and `proof_origin` to match this route. This is below the unit level;
no statement or step in `dag/units/sk-thm-p1.json` is bypassed.

Validation: repeated single-file compilation with the required `lcompile.py`;
final compilation has no errors or warnings. All lines are at most 100 characters.
The statement parser confirms no signature changed, the sole original sorry is
closed, and no new sorry was added. A DFS through the overlaid DAG visited 92
nodes and found no cycle. The proof handles a constant complementary factor (including degree-one f), and
no nonzero-algebra assumption is introduced. Only the existing local-ring
hypothesis supplies nontriviality of R. No new statements with postponed proofs
were created.

## Proved and sorry left

Proved the module's sole former sorry:
`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`
(node `lem-weil-pbc-henselian-local-root-lifting`). Both private helpers are proved.
There are no sorries left in this module and none added by this delivery.

The proof deliberately uses the existing named statements
`Polynomial.exists_monic_factorization_of_idempotent`
(node `lem-weil-pbc-idempotent-splitting-monic-factorization`) and
`Algebra.existsUnique_isIdempotentElem_of_henselianRing`
(node `lem-weil-pbc-henselian-pair-integral-idempotent-lifting`), whose source modules
still contain sorry. Thus this delivery reduces the target's closure to those
existing proof tasks; it does not assert axiom-free completion of the closure.

## No longer needed

Removed imports:
- `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`.
- `Sheaf.RingTheory.RootLiftingEtaleRetraction`.

Removed direct proof dependencies of this item:
- `lem-weil-pbc-root-lifting-etale-retraction`
  (`Sheaf.RingTheory.RootLiftingEtaleRetraction`).
- `lem-weil-pbc-etale-retraction-finite-product-local`
  (`Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`).
- `lem-weil-pbc-finite-algebra-local-radical`: uniqueness and lifting now come
  from the existing integral-algebra theorem.
- `lem-weil-pbc-finite-flat-local-free`: the rank-one-module argument is replaced
  by the monic-factorization theorem and an elementary degree-one calculation.
- `def-weil-pbc-henselian-terminology` as a separate proof dependency; it remains
  the unchanged statement dependency and occurs in the integral theorem's own DAG.

`lem-weil-pbc-monic-quotient-free` remains needed for the finite algebra
`AdjoinRoot f` and coefficient reduction. The pruned nodes may remain reachable
through other items or the imported statements' own dependencies; this report
claims only that this item's proof no longer uses them directly.

Temporary explicit imports of Mathlib's Finiteness.Basic, Polynomial.FieldDivision,
and Polynomial.Degree.SmallDegree were tested and removed: their declarations are
already available through the retained imports. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or mathematical error was found in the item's statement.
The old five-step plan is a valid route, but existing declarations allow a shorter
one. The unchanged original docstring records that older route; the delivered DAG
and proof implement the factorization/integral-algebra route described above.

The integral-lifting module's Lean hypothesis is `HenselianRing A I` (Mathlib's
root-lifting predicate), although its prose proof invokes the finite-idempotent
criterion as equivalent terminology. This delivery uses its actual recorded Lean
signature, not an unproved equivalence inferred from its prose. Its future proof
worker must justify that bridge; this item creates no cyclic import or DAG edge.

## Second reading by W2

1. Interface: PASS. Read the full repository/sandbox diff. The sole existing
   theorem's signature is byte-for-byte identical, including both universe levels
   and the finite-algebra quantifier. No definitions or public imports changed;
   the two replacement imports are proof-only. No change record is needed.
2. Proof: PASS as a reduction to existing open dependencies. Recompiled the
   delivered module with lcompile.py: no errors or warnings. A scratch copy with
   explicit #print axioms for all three declarations reports only propext,
   Classical.choice, Quot.sound, and sorryAx. The ULift helper has no sorryAx;
   the factorization helper and main theorem inherit it from the existing imported
   open theorems. There is no local sorry, axiom, unsafe, opaque, implemented_by,
   extern, or hollow definition. This is not an axiom-free proof of the closure.
3. Split statements: PASS (none added). Both new private helpers are fully proved.
   Read both imported open theorem signatures and their proofs in words. They
   supply genuine intermediate steps, not a renamed copy of this equivalence.
   The CRT calculation works when either factor is 1; the root calculation works
   for degree-one f, with complementary factor 1. Constant monic f has no residue
   root, so its forward case is vacuous. The reverse argument allows the zero
   finite algebra. ULift handles v larger than u without restricting the original
   hypothesis. The integral theorem's prose still needs the root/idempotent bridge
   already identified above; this delivery relies on its actual Lean signature.
4. Route and pruning: PASS. Independently searched LeanFinder for the finite-algebra
   idempotent characterization, Loogle for IsIdempotentElem and HenselianRing, and
   rg through both library roots, and read Mathlib's HenselianLocalRing.TFAE.
   Nilpotent-kernel lifting does not apply to a general extended maximal ideal;
   no direct replacement was found. Both retained proof-only imports are used.
   Every removed old proof_dep is listed under No longer needed. Read
   dag/units/sk-thm-p1.json, including realized: this node is below its realized
   unit steps, and the changed local argument bypasses none of them.
5. DAG: PASS. Only proof, proof_deps, and proof_origin differ in the existing node.
   Read each new proof step against the corresponding Lean code. The three
   proof_deps are exactly the union of the steps' uses. Independently traversed
   the overlaid proof-dependency closure (31 nodes): no cycle. No new nodes exist.

Changes by the second reader: appended this independent review and its axiom and
edge-case evidence to report.md. No Lean or DAG repair was necessary. The original
public docstring describes the older valid route; the actual shorter route is
recorded in the revised DAG and this report.
