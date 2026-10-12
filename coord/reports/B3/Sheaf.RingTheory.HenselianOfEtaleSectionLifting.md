## What changed

Proved both remaining sorries in `Sheaf.RingTheory.HenselianOfEtaleSectionLifting`,
without changing any existing declaration signature or any public import.

`etale_section_lifting_radical_and_henselian` uses principal localization for the
Jacobson radical and constructs the simple-root lift directly from the standard
etale pair `(f, f.derivative)`. A proved private helper transports the hypothesis
from universe `max u v` to universe `u` using `ULift.algEquiv`.

`etale_section_lifting_idempotents` uses the existing theorem
`AlgebraicGeometry.exists_etale_lift_isIdempotentElem`. The inverse quotient
isomorphism supplies its section modulo I, which the hypothesis lifts. The
resulting tensor map descends the idempotent: its induced quotient map is a left
inverse to the canonical equivalence beta, verified on quotient representatives.
For uniqueness, finite algebras are integral, maximal ideals contract to maximal
ideals, and `IsIdempotentElem.eq_of_sub_mem_of_le_jacobson` applies.

Added proof imports `Mathlib.RingTheory.Etale.StandardEtale` and
`Mathlib.RingTheory.Ideal.GoingUp`. Updated the proof, proof_deps and proof_origin
of all three nodes of the module, including the final assembly node's missing
idempotent dependency. No new modules or nodes.

Validation: local single-file compilation completes without warnings. The
required delivery dry run provides the server compile and delivery checks.
Sources checked: [Stacks 09XI](https://stacks.math.columbia.edu/tag/09XI) and
[Stacks 00UC](https://stacks.math.columbia.edu/tag/00UC), plus the existing Mathlib
leaf records and the Lean signatures and proofs of both Sheaf dependencies.

## Proved and sorry left

- `etale_section_lifting_radical_and_henselian`
  (`lem-weil-pbc-etale-section-lifting-radical-and-henselian`): proved without sorry.
- `etale_section_lifting_idempotents`
  (`lem-weil-pbc-etale-section-lifting-idempotents`): proved without sorry.
- `henselianRing_of_etale_section_lifting`
  (`lem-weil-pbc-etale-section-lifting-henselian-pair`): existing complete assembly
  retained, now applied to the two proved component theorems.
- No sorry remains in this module, and this delivery adds none elsewhere.
  Imported dependencies retain their own proof obligations, if any.

## No longer needed

Removed the unused proof import `WeilConjectures.Mathlib.RingTheory.Henselian`.
Its local-ring retraction results are not needed. No entire DAG dependency node
or Sheaf dependency module is pruned: `LiftIdempotentUpstairs` and
`IdempotentsDeterminedModuloRadical` remain necessary for the idempotent clause.
For the radical/root component alone, the route through finite-algebra idempotent
lifting and an idempotent-to-HenselianRing characterization is unnecessary;
the direct standard-etale root argument replaces it. This does not bypass any
realized statement or step of unit `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

The component nodes had no proof_deps despite the useful existing dependencies.
Their records now describe the actual proofs. The final assembly node listed only
the radical/root component although the Lean proof also uses the idempotent
component; this missing dependency is now recorded.

The radical/root theorem's inherited docstring sketches finite-algebra
idempotent descent, but its actual proof now constructs a simple root directly
using a standard etale algebra, as detailed in its node and inline comment.
The statement is unchanged. No statement was disputed or weakened.

Edge cases are included without nontriviality assumptions: I = bottom, the zero
ring, zero finite algebras, and idempotents 0 and 1 all use the same construction.
The universe lift is necessary for unequal u and v and is handled explicitly.

## Second reading by B3

1. Compared the delivered module with the repository version using `diff -u`.
   All three existing theorem signatures, docstrings, universes, and public
   imports are byte-for-byte unchanged. Only proof bodies, a proved private
   universe-transport helper, and proof-only imports differ. No definition or
   statement changed; no change record is needed. Verdict: pass.
2. Compiled the module locally without errors or warnings, and compiled a
   scratch copy with `#print axioms` for the private helper and all three public
   theorems. The helper and `etale_section_lifting_radical_and_henselian` use only
   `propext`, `Classical.choice`, and `Quot.sound`. The idempotent component and
   final assembly additionally use `sorryAx` through imported proof obligations;
   this delivery closes their local proof bodies, not those imported obligations.
   There is no `sorry` or forbidden declaration in the delivered module and no
   hollow definition. Verdict: pass with this explicit dependency limitation.
3. No statements were split off and no new nodes were added. Checked the private
   helper by composing the ULift equivalence and its inverse. Checked the radical
   criterion for `xy+1`, the derivative-unit requirement in `HenselianRing`, and
   tensor descent on quotient representatives. These arguments require neither
   a nonzero ring nor a proper ideal; bottom ideals and zero algebras introduce
   no exceptional step. The `max u v` hypothesis transports to Type u correctly.
   Verdict: pass.
4. Independently searched the library for section-to-henselian and unique
   idempotent-lifting results and queried Loogle for `HenselianRing`. The upstream
   section criterion is for local rings only. The apparently shorter
   `Algebra.existsUnique_isIdempotentElem_of_henselianRing` in
   `HenselianIntegralIdempotentLifting` depends on this module, so using it here
   would be circular. The two Sheaf proof dependencies remain used; new Mathlib
   imports are proof-only. The old proof_deps are empty for the two component
   nodes and the assembly's old dependency is retained: no old node is pruned.
   Read `dag/units/sk-thm-p1.json`, including every realized step; this local
   algebra argument bypasses none of them. Verdict: pass.
5. Compared all three node files field by field. Only `proof`, `proof_deps`, and
   `proof_origin` change. Their proof steps describe the Lean argument, their
   dependency lists equal the unions of step uses, and their Lean records still
   name the unchanged declarations. In particular the final assembly now records
   both component dependencies. Verdict: pass.

Changes by the second reader: added this review and made the residual imported
`sorryAx` dependence explicit. The Lean proofs and node changes needed no repair.
