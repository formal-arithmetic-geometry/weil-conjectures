## What changed

Proved `AlgebraicGeometry.Etale.derivedPulledGlobalGerm_fac` in
`lean/Sheaf/AlgebraicGeometry/DerivedPulledGlobalGermFac.lean`, preserving its
original signature text, visibility, docstring, and imports. The proof expands the
inverse Leray comparison, uses the derived natural-transformation unit formula and
exact-functor comparison, applies `derivedBaseChangeMapPlus_fac_app`, and moves the
stalk factorization using naturality. Functoriality identifies the resulting termwise
composite with the specified `a`. All intermediate identities are proved locally.

The local heartbeat allowance covers definitional equality checks between canonical
homotopy comparison endpoints. The local unused-variable linter setting preserves
its original unused abbreviation `R`. A declaration-local transparency setting
reduces repeated unfolding; the exact comparison identity and final transport
block retain the library setting where their endpoints require it. The proof
compiled in 44.8 seconds; the heartbeat-comment placement was then corrected
to satisfy the style linter.

The saved DAG node was stale. It has been restored from the supplied repository:
the current statement, source, and dependency records are retained. Its existing
proof plan describes the proof delivered here, so no route change is needed.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.derivedPulledGlobalGerm_fac`
(node `lem-weil-pbc-derived-pulled-global-germ-fac`): the sole original hole.
Holes closed: 1. Holes added: 0. Sorries left in the item: none.
No new modules, definitions, or axioms were added.

## No longer needed

None. Both public imports are needed by the statement and its canonical constructions.
The proof follows the current node plan using `DerivedGlobalGerm` and
`WeilConjectures.SixFunctors.BaseChange.Derived`; no import or planned dependency
module is removed and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved node came from a different baseline: it changed the natural-language
statement, source, creation metadata, and dependency records. The initial retry
compiled the proof but was refused because that saved statement differed from the
fetched baseline without a statement-change record. Restoring the current node
resolves that mismatch without changing the mathematical statement or fabricating
an interface change. The explicit `(A := B)` in the saved theorem signature was also
removed to preserve the original signature text; it remains only in a proof-local let.

The dry run is run as a persistent process and polled so that the tool-call timeout
which ended the previous worker does not interrupt delivery validation. Nothing is
pushed; the designated second reader supplies the second reading and delivers.

## Second reading by Q2

1. **Interface unchanged — pass.** Diffed the sole delivered module against the
   repository. A separate text comparison confirms the complete existing theorem
   signature is byte for byte identical. Its docstring, visibility, local instances,
   and imports are unchanged. Only its proof and declaration-local elaboration,
   heartbeat, and unused-variable linter options differ. There are no definition or
   statement changes and no change records are required.
2. **Kernel proof — pass.** Independently compiled the delivered file with
   `lcompile.py`: no errors or warnings (45.6 seconds). Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Etale.derivedPulledGlobalGerm_fac`: exactly
   `propext`, `Classical.choice`, and `Quot.sound` (47.0 seconds), with no `sorryAx`.
   The file contains no remaining `sorry` or forbidden declaration mechanism.
   Read each local identity: `he` is Leray unit compatibility, `hβ` is the derived
   natural-transformation formula followed by exact-comparison cancellation,
   `hnat` and `hs` are naturality, and `ha` removes identity associators. The final
   transport uses the existing derived-exchange replacement formula and combines
   termwise maps by functoriality. No arbitrary existence witness is introduced.
3. **Split statements — pass, none.** There are no new declarations or split-off
   holes. All intermediate identities are proved inside the existing proof, so no
   new nodes or searches for split-off statements are required. The signature still
   works for arbitrary bounded-below complexes and commutative squares; it adds no
   cartesian, properness, or injectivity hypothesis on the complex.
4. **Route and pruning — pass.** Read `DerivedGlobalGerm`, the derived-exchange
   replacement theorem, the generic derived-unit and exact-composition formulas,
   and `dag/units/sk-thm-p1.json`, including `realized`. Searched the library for
   germ factorization and Leray-unit alternatives, and queried Loogle for the
   composition comparison (not indexed there). The related target-side germ
   factorization is a different statement and remains open; it does not shorten
   this source-side proof. This proof already uses proved generic comparison
   formulas directly. Both public imports occur in the original statement:
   `derivedPulledGlobalGerm` and `pulledGlobalGerm` need `DerivedGlobalGerm`, and
   `derivedBaseChangeMapPlus` needs `BaseChange.Derived`. Both old proof dependencies
   are used, hence `No longer needed: None` is complete. No unit step is bypassed.
5. **DAG agrees — pass.** The sandbox node is identical to the repository node.
   Its proof step describes the actual local identities and exchange replacement;
   its `proof_deps` are exactly the two modules' node dependencies used here, and
   its `proof_origin` describes this categorical expansion. No new nodes exist.

Second reading changed only this report: added the independent checks above.
No repair to the correct Lean proof or node was needed. Confirmed holes closed: 1;
holes added: 0; split off: 0; modules pruned: none.
