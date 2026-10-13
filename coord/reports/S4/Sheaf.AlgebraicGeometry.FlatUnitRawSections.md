## What changed

Proved `AlgebraicGeometry.Scheme.Modules.flatUnit_raw_sections` in
`Sheaf.AlgebraicGeometry.FlatUnitRawSections`, without changing its signature or imports.
The proof follows the node's existing three-step cycle argument. Three private, fully proved
comparison helpers reproduce the generic cycle calculation used in
`ShortComplexSectionComparison`; a fourth specializes it to the section comparison theta. A fifth proves the full cycle identity
for an arbitrary exact functor adjoint to pushforward, before specialization to tensor pullback.
The proof cancels the raw homology projection, compares cycle inclusions using unit naturality,
and compares homology quotients using the adjunction and exact pullback's homology isomorphism.
The private generic proof keeps the concrete tensor-pullback construction out of the long
calculation. Declaration-scoped options support elaboration of the equivalent section functor
presentations; no new top-level attribute commands are needed.
No definition, public interface, or unit route changed. No new proof dependency was imported.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.flatUnit_raw_sections`
(node `lem-weil-pbc-flat-unit-raw-sections`).

No holes remain in the item. No holes were added elsewhere. All five private helper theorems
are proved. This is a proof, not a decomposition into new holed statements.
The single-file compile succeeded; the delivery dry run performs the final compilation and
axiom checks. The construction uses the existing flat exactness and tensor adjunction results,
with Mathlib's kernel, cycle, and homology comparisons.

## No longer needed

None. The sole original import is needed for the statement's section comparison, exact
pullback instances, and induced adjunction on complexes. The proof uses all three existing
DAG dependencies; no module or node is pruned. No new imports were added.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The existing DAG route suffices without new
statements. Lean needs the sheaf-module presentation explicitly in the private specialization
and a normalized short complex `T.map F` to compare mapped complexes efficiently. An initial top-level local-attribute approach was rejected by the interface check; extracting
the fully proved generic argument removed those commands and preserves the original interface.

## Second reading by S4

1. Interface: compared the whole delivered module with the repository version and
   mechanically compared the existing theorem signature byte for byte. The only public
   theorem, its docstring, universes, hypotheses and conclusion are unchanged. The sole
   public import is unchanged and is needed for the statement. The five new declarations
   are private proved helpers; there are no definition or statement changes to record. Pass.
2. Proof: independently compiled the delivered file through lcompile.py with no errors
   or warnings. Read all five helper proofs and the final specialization. No sorry, axiom,
   unsafe, opaque, implemented_by, extern or hollow definition is present. A scratch copy
   prints the final theorem's axioms, and deliver3.py checks every declaration's axioms.
   The chosen tensor adjunction is the existing pinned adjunction; this delivery introduces
   no data chosen from a new existence hole. Pass: the scratch axiom check reports only propext, Classical.choice and Quot.sound.
3. Split statements: none. All five helpers are proved, including the exact-functor
   specialization that contains the cycle argument; the final theorem is not delegated to
   an unproved restatement. Degree zero and the empty open require no extra assumption: the
   argument only uses the short complex's kernel and epimorphic homology projection. Pass.
4. Route and pruning: read ShortComplexSectionComparison and searched Mathlib's homology
   files and both local library roots for comparison/quotient identities. A fresh LeanFinder
   search for counit homology comparison on cycle quotients returned derived/localization
   adjunction facts, not a replacement. The matching generic comparison helpers elsewhere
   are private, so cannot be reused through an ordinary import. The proof uses Mathlib's
   canonical comparison and naturality lemmas directly. The sole original import is needed;
   none of the three old proof dependencies is unused. Read sk-thm-p1's realized record: this
   node lies below its fixed route, which is unchanged. Pass.
5. DAG: read lem-weil-pbc-flat-unit-raw-sections and its three dependency Lean records.
   The schemes, flat morphism, arbitrary complex, degree and open match its statement.
   hs/ht establish theta on cycles by the sheafification counit, hc is unit naturality for
   the cycle inclusion, and hh/hh' identify the homology quotient via exact pullback.
   Cancellation of homologyπ closes the equality. This is exactly the existing three-step
   proof with the same proof_deps and source; no node edit or new node is required. Pass.

Changes by the second reader: appended this independent review and added a search record.
No Lean repair was needed. One original hole closed, zero holes added; no nodes or imports
pruned. The independent scratch axiom result and delivery preflight are recorded below.

Independent scratch compile: clean; #print axioms flatUnit_raw_sections reports exactly
`propext`, `Classical.choice`, `Quot.sound` (47.7 seconds).

Second-reader delivery dry run: OK; compilation and preflight passed, review class AUTO.
