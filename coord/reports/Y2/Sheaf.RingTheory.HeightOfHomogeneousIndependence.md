## What changed

Proved `AlgHom.height_ker_eq_card_of_homogeneous_independence` without changing its
signature or existing docstring. The proof localizes at the rational maximal ideal,
renames the variables to `Fin n`, and computes local dimension by induction on `n`.
The zero-variable case is a field. For the successor case, quotienting by the first
variable preserves the hypotheses and Mathlib's nonzerodivisor dimension-drop theorem
supplies the induction step. Mathlib identifies the resulting dimension with height.

Added two proved supporting modules, both imported only for proofs:

- `Sheaf.RingTheory.HomogeneousIndependenceLocalization`: proves rational residue
  representatives, generation of the localized maximal ideal by Nakayama, and
  homogeneous independence by clearing denominators and primary powers of a maximal ideal.
- `Sheaf.RingTheory.HomogeneousIndependenceQuotient`: constructs homogeneous
  representatives by induction on ideal powers, proves strictness of multiplication
  by the first variable, proves it is a nonzerodivisor by local Krull intersection,
  and proves homogeneous independence after killing it.

The local dimension induction and homogeneous-representative construction are proved
private helpers. Neither constructs data from an unproved existence assertion.
Updated the original node's proof route and added nodes for the two proved statements.
Repaired the earlier attempt's missing public imports in the new quotient module:
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs` exposes its maximal ideal and
`Mathlib.RingTheory.Ideal.Quotient.Operations` exposes its quotient algebra structure.
All three modules compile in dependency order with no warnings. The proof includes
empty index sets, zero-degree polynomials, and the one-variable quotient case; it
requires neither characteristic zero nor finite type over the field.

## Proved and sorry left

Closed the original hole:
`AlgHom.height_ker_eq_card_of_homogeneous_independence`
(node `lem-wf-height-of-homogeneous-independence`).

The following new public theorems are also fully proved:
`AlgHom.homogeneous_independence_localization`
(node `lem-wf-homogeneous-independence-localization`) and
`IsLocalRing.homogeneous_independence_quotient`
(node `lem-wf-homogeneous-independence-quotient`).

Original holes closed: 1 of 1. New holes added: 0. No `sorry` remains in any delivered
module. This is a complete proof, not a decomposition into unproved statements.
The required delivery dry run additionally checks declaration axioms.

## No longer needed

Removed the proof import `Sheaf.RingTheory.KrullIntersectionLocalization` and the
original route's dependency `lem-weil-pbc-krull-intersection-localization`.
The local separation step uses the already-proved Mathlib theorem
`Ideal.iInf_pow_eq_bot_of_isLocalRing`, the local specialization of
`lem-weil-pbc-krull-intersection-jacobson`. Thus the generic localization-intersection
statement and its `Sheaf.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule`
proof subtree are unnecessary for this item; other users may still need them.

Nakayama remains necessary inside the proved localization lemma, and localization
height and nonzerodivisor dimension drop remain necessary in the main proof.
No unit statement or realized unit proof step was bypassed.

Avoided importing `WeilConjectures.RingTheory.HopfAlgebra.Cartier` (which would create
an import cycle) and the much larger
`WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous` module. Polynomial
ideal-power evaluation follows directly from Mathlib's homogeneous representation
lemma. The small, already-proved adic-order lemma in
`WeilConjectures.Mathlib.RingTheory.Ideal.Operations` is used.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt did not compile because two notions in the new quotient
statement were only privately imported. The public imports above repair this.
No existing statement was changed or disputed. The original generic
Krull-intersection-localization dependency was stronger than necessary: Mathlib
already proves separation of a Noetherian local ring by any proper ideal.
The new local statements explicitly retain surjectivity of residue representatives
from `k`; homogeneous independence over a smaller coefficient field alone would
not justify the polynomial graded-ring argument. This condition follows from the
original rational-point hypothesis and descends to the quotient.

The cited blueprint and Waterhouse files are not installed in this clone. The full
expanded proof in the existing item's node and the source library's Cartier module
were read; the new nodes cite that available expanded argument and mark the
formalization details as written by an agent. Waterhouse is already in the project's
Wanted literature table. LeanSearch was unavailable (Internal Server Error); the
attempt is recorded along with successful LeanFinder/Loogle and source searches.

## New nodes

`lem-wf-homogeneous-independence-localization` records the localization part of the
original plan, including residue representatives and Nakayama generation. Its
statement is proved in `lean/Sheaf/RingTheory/HomogeneousIndependenceLocalization.lean`.

`lem-wf-homogeneous-independence-quotient` records the strictness and quotient step
of the original plan. Its statement contains no height or dimension assertion and
is proved in `lean/Sheaf/RingTheory/HomogeneousIndependenceQuotient.lean`.

Both inherit chapter `sec-algebraic-groups-lie-algebras` and unit `sk-i-cartier`.
No definition or existing interface changed; no change record or forced adaptation
is needed.

## Second reading by Y2

1. **Existing interfaces: pass.** Compared the item's module with the repository by
   `diff -u`. The existing theorem signature and docstring are byte-for-byte unchanged.
   Its two public imports stay unchanged; new imports are proof-only. The other two
   modules are new, with their public imports needed by their signatures. There are
   no changed definitions, target statements, forced adaptations, or change records.

2. **Proof and axioms: pass.** Independently compiled all three files in import order
   through `lcompile.py --all`: no errors or warnings. Read every proof, including
   the private homogeneous representative and dimension induction helpers. Scanned
   all delivered Lean for `sorry`, forbidden declarations, and kernel-check bypasses;
   none occur. A scratch module printed the axioms of
   `AlgHom.height_ker_eq_card_of_homogeneous_independence`,
   `AlgHom.homogeneous_independence_localization`, and
   `IsLocalRing.homogeneous_independence_quotient`: each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Residue representatives
   and homogeneous representatives are chosen only inside proofs of propositions;
   no public data is constructed from an unproved existence assertion.

3. **Supporting statements: pass.** There are no split-off unproved statements.
   The localization lemma proves residue surjectivity, ideal generation and
   preservation of independence; it contains no height conclusion. The quotient
   lemma proves the nonzerodivisor and independence after removing a variable;
   it contains no dimension conclusion. Both are true, strictly intermediate
   parts of the original argument, fully proved, documented, and represented by
   new nodes. Checked empty generating families, degree zero, and `n=0` in the
   quotient lemma: Nakayama gives a zero maximal ideal in the empty case, and
   the quotient proof explicitly treats degree zero without a negative degree.
   Multiplication strictness is proved before using Krull separation, so it
   does not assume finite order for an element in the intersection of all powers.

4. **Route, search and pruning: pass.** Repeated independent searches with different
   wording via `msearch.py` LeanFinder, Loogle, and grep, and searched both Lean roots.
   LeanFinder found the regular-sequence dimension theorem and the singleton
   dimension-drop theorem; neither removes the need to prove regularity and quotient
   independence. Loogle confirmed the exact dimension-drop theorem already used.
   No duplicate or direct associated-graded criterion was found. The proof uses
   Mathlib directly for Nakayama, local Krull intersection, dimension drop and
   localization height. The removed old dependency is
   `lem-weil-pbc-krull-intersection-localization`; its module is the only removed
   import. `lem-weil-pbc-nakayama-local-generators` moved to the localization
   node's dependencies and remains used transitively, rather than being pruned.
   Both other old dependencies remain in the main node. Read `sk-i-cartier.json`:
   all realized entries are empty, and this delivery changes none. The proof
   retains the original local-dimension route below the unit level.

5. **DAG agreement: pass.** Compared the old and delivered main nodes and read both
   new nodes against their modules. Main-node localization, variable renaming,
   quotient induction, dimension drop and height steps agree with the Lean proof.
   New-node proof dependencies record Nakayama and the local specialization of
   Jacobson Krull intersection, respectively. The new nodes have their creation,
   source, proof origin, blueprint ancestry, chapter, unit, search and Lean records;
   their recorded signatures agree with the public theorems. The existing node's
   statement and statement dependencies have not changed.

Second-reading changes: appended this independent review and clarified that the
Nakayama dependency is retained transitively. No Lean or node repair was needed;
all proofs and their interfaces are retained. Original holes closed remain 1 of 1;
new holes added remain 0, and no unproved statements are split off.
