## What changed

Proved `Algebra.relativeGlobalCompleteIntersection_conormal_free` with its existing signature
and all three conclusions unchanged. The equation classes span by ideal-span induction. A
relation modulo the square forces each lifted coefficient into the ideal at every maximal
localization: at primes containing the ideal this follows from the local regular-sequence
and regular-sequence conormal-basis declarations, and elsewhere the localized ideal is the
unit ideal. Mathlib's `Ideal.mem_of_localization_maximal` makes each coefficient globally
zero in the quotient. `Module.Basis.mk` then supplies the prescribed basis;
`Module.Free.of_basis` and `Basis.equivFun` supply the other conclusions.

Added the proof-only import `Mathlib.RingTheory.LocalProperties.Basic`. Both existing Sheaf
proof imports remain necessary. Four private helpers contain complete proofs:
`span_conormal_generators`, `conormal_sum`, `coefficients_mem_of_conormal_basis`, and
`coefficients_mem_of_locally_regular`. The span helper follows the already proved private
helper in `Sheaf.RingTheory.SectionDifferentialBasisQuotient`; importing that module would
not expose its private helper and would introduce unrelated dependencies.

Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to the coefficient
argument, and its theorem docstring to describe that argument. No public signature,
definition, visibility, target, or public import changed. The item is not a realization of
a statement or proof step in `dag/units/sk-thm-p1.json`; the unit route stays intact.

Validation: the module compiles locally without warnings through the prescribed
`lcompile.py`. The proof uses the actual existing dependency signatures, including the
specified basis vectors, and introduces no assumptions. Checked the empty equation family,
the unit ideal/zero quotient, and the zero base ring: the span and linear-independence
arguments cover them without a nontriviality assumption. Every maximal ideal containing
I gives a prime in P/I; maximal ideals not containing I are handled separately.

## Proved and sorry left

Closed 1 original hole:
`Algebra.relativeGlobalCompleteIntersection_conormal_free`
(node `lem-weil-pbc-relative-global-complete-intersection-conormal-free`).

No `sorry` remains in the delivered module. Added 0 holes and split off 0 statements.
The new node records an already proved Mathlib declaration, not a new Lean hole.
The proof still uses the existing statements
`Algebra.isRegular_localization_of_relativeGlobalCompleteIntersection` and
`RingTheory.Sequence.regularSequence_conormal_free`; their existing holes are unchanged
and remain the next stage-3 items. This delivery proves the assembly from these declared
lemmas, not the entire transitive dependency closure.

## No longer needed

Removed these four nodes from the item's proof dependencies:

- `lem-weil-pbc-localization-at-prime-of-quotient`;
- `def-weil-pbc-module-localization`;
- `lem-weil-pbc-localization-module-exact`;
- `lem-weil-pbc-linear-map-bijective-at-maximal-localizations`.

Their original roles were the quotient-localization isomorphism, conormal localization via
exactness, localization of finite direct sums, and bijectivity of the localized basis map.
The proof now maps a coefficient relation into the polynomial local ring itself and tests
ideal membership. It never constructs or applies those isomorphisms or module-localization
maps. Their candidate Mathlib proof imports would have included
`Mathlib.Algebra.Module.LocalizedModule.Exact` and
`Mathlib.RingTheory.LocalProperties.Exactness`; no direct imports of them are needed here.
Other Mathlib localization infrastructure can remain transitively imported, so this does
not claim global removal of those Mathlib modules or removal from other nodes' routes.

No existing direct import was removed: the original statement imports and the two existing
Sheaf proof imports are used. The local regularity and regular-sequence conormal nodes,
as well as the definitions of regular sequences, localization at primes, and free modules,
remain in `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

No false or unusable dependency statement was found. The planned localization-isomorphism
route is mathematically valid but unnecessary: its coefficient form proves the same basis
statement with considerably less formal infrastructure. Source read at
https://stacks.math.columbia.edu/tag/00SV, proof of (3), and
https://stacks.math.columbia.edu/tag/00HN, statement and proof of (1). The named local
literature files and blueprint `_section.md` are absent in this read-only clone; the DAG
unit record and the primary Stacks pages were available and read.

LeanSearch was unavailable with an Internal Server Error. LeanFinder, Loogle and grep
worked. The theorem's existing Mathlib search candidates concern regular sequences and
standard smooth presentations; none closes this relative complete-intersection statement.
Loogle and source inspection identify the exact ideal-membership leaf used instead.

## New nodes

`lem-weil-pbc-ideal-membership-at-maximal-localizations` records the exact Mathlib theorem
`Ideal.mem_of_localization_maximal` in `Mathlib.RingTheory.LocalProperties.Basic` (line 539).
It applies to an arbitrary ideal and element of a commutative ring, including the zero ring.
Its source is 00HN (1), applied to the element's class in the quotient. The node includes the
annihilator proof, all three kinds of search (LeanSearch unavailable, Loogle exact match,
grep exact match), and the existing Mathlib Lean record. Whole-DAG grep and
`tools/blueprint_refs.py search 'ideal membership localization'` found no existing node
with that exact statement; the free-prime-membership nodes concern one prime and its own
prime ideal, which is a different assertion. No new Lean module or change record is needed.

## Second reading by S3

1. Interface: PASS. Read the whole module and its diff against the repository.
   The existing theorem signature is byte-for-byte identical, including the specified
   basis vectors and both further conclusions. No definition, visibility, existing public
   import, or other module is changed. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`; there are no undeclared interface changes.
2. Proof: PASS. Independently compiled the delivered file with `lcompile.py`, without
   errors or warnings. A scratch copy with `#print axioms` for all four private helpers
   and the main theorem compiled. The first three helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`; the local-regularity helper and main theorem also
   use `sorryAx` from the existing imported conormal/local-regularity holes. There is no
   direct `sorry`, forbidden axiom/implementation declaration, or hollow definition.
   Quotient coefficient lifts come from proved surjectivity. The locally selected basis
   from the open conormal theorem is determined by its prescribed vectors `hb`, so no
   arbitrary witness of an unproved mere-existence statement is used as data.
3. Split statements: PASS. There are no split-off Lean statements or new holes. The new
   node records the already proved Mathlib ideal-membership theorem, whose signature and
   implementation were read. Its annihilator/maximal-ideal proof is correct. Checked
   zero ring, unit ideal, zero ideal, and, concretely, the ideal `(2)` in `Z`: maximal
   localization at `(2)` detects a coefficient outside that ideal. The finite conormal
   arguments cover `c = 0` and the zero quotient without nontriviality assumptions.
   Independent LeanFinder search for locally regular ideal generators and Loogle search
   `Ideal.Cotangent, LinearIndependent` found no replacement theorem. Whole-DAG and
   library searches found existing uses of the Mathlib leaf but no duplicate node with
   its statement. Other conormal-basis lemmas have different hypotheses.
4. Route and pruning: PASS. Read both imported Sheaf theorem signatures and the Stacks
   proofs at https://stacks.math.columbia.edu/tag/00SV and
   https://stacks.math.columbia.edu/tag/00HN. The proof genuinely assembles local regularity,
   the prescribed local conormal basis, and Mathlib's ideal-membership criterion; it does
   not restate the original hole. Ideal-span induction supplies generation independently.
   All direct imports are needed either for the public statement or this proof, and the
   added Mathlib import is proof-only. The report lists exactly the four old proof
   dependencies absent from the new proof. Checked `realized` across all unit records:
   neither this item nor those four pruned dependencies is a protected realization;
   the unit route remains unchanged. No global module removal is claimed.
5. DAG: PASS. The new five-step proof follows the Lean calculation. `proof_deps` is exactly
   the union of the steps' `uses`; `proof_origin` identifies the coefficient variant.
   The new Mathlib node has its self-contained statement, source, proof, dependency lists,
   search records, creation/blueprint metadata, chapter/unit, and existing Lean match.

Second reading changed only this report, adding the independent review and axiom-check
results. No Lean or node repair was necessary. Closed 1 original hole, added 0 holes,
split off 0 statements; the existing imported holes remain open.
