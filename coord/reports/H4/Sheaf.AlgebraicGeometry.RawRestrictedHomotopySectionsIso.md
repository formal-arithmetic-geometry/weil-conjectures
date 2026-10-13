## What changed

Completed the existing sandbox proof of
`AlgebraicGeometry.Etale.RawRestrictedComparison.exists_rawRestrictedHomotopySectionsIso`
in `Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso`.
All existing public signatures, definitions, visibility and docstrings are unchanged.
The proof follows the existing node's two-step route without introducing new nodes.

The private `representedEquiv` composes inverse-image/direct-image, sheafification,
free-abelian and Yoneda adjunction equivalences. Its generator formula proves that
this is the explicit evaluation map. `evaluationEquiv` makes it additive, and
`sectionsComplexIso` uses Mathlib's from-single cochain equivalence and its
compatibility with the differential. `homClassIso` identifies degree-zero Hom-complex
cohomology classes with unshifted homotopy-category morphisms. Finally,
`sectionsComplexIso_evaluation` compares cycle representatives and homology projections
with the existing `chainEvaluation`, giving the required evaluation formula.

The earlier attempt's final compatibility calculation did not compile: rewriting the
cycle representative unfolded the single-complex comparison before its component
formula could be used. The repaired calculation rewrites the component formula first.
The only added proof import is
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle`.
All helpers are private and proved. No definition chooses an arbitrary witness.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.exists_rawRestrictedHomotopySectionsIso`
(node `lem-sbc-raw-restricted-homotopy-sections-iso`).
One of one original sorries proved; zero split off; zero new holes.
No sorry remains in the delivered module.

This is a direct construction from the existing sheaf adjunctions and Mathlib's
Hom-complex/homology API, rather than a decomposition into unproved intermediate
statements. The argument works for arbitrary unbounded complexes. It uses no
injectivity, boundedness, or nonemptiness assumption, including for the zero complex
and an empty pullback. The unit record's realized statement and step lists are empty;
the node's original route is retained in any event.

## No longer needed

No original repository import, DAG dependency, or module is pruned. Both original
proof steps and all three named proof dependencies are used.
The earlier sandbox attempt's redundant explicit import of
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology` was removed:
`HomComplexSingle` already publicly imports it, and its results remain used.
This removes a redundant import, not a module from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical route and unchanged statement are usable. The earlier
sandbox attempt contained the complete construction but failed at the order of
rewrites in the single-complex evaluation compatibility calculation; this is repaired.
No interface changes, forced adaptations, disputed statements, or new nodes are needed.


## Second reading by H4

1. **Interface: PASS.** Read the complete repository/sandbox diff and checked all
   four existing declarations with the declaration parser. Their statements,
   visibility and docstrings are unchanged; all three original definitions are
   unchanged. The only new import is proof-only. No change record is necessary.
2. **Proof: PASS.** Independently compiled the delivered module with `lcompile.py`
   without errors or warnings (48.6 seconds). Compiled a scratch copy with explicit
   `#print axioms` for all 13 declarations, including every private helper: each
   uses only `propext`, `Classical.choice` and `Quot.sound`, without `sorryAx`.
   The source contains no sorry or forbidden declaration/attribute. All new data
   are constructed from proved equivalences and isomorphisms; no arbitrary
   witness is selected from an unproved existence theorem.
3. **Split statements: PASS (none).** No new public statement, node or hole is
   introduced. Read each private helper: the adjunction composite identifies
   represented maps with sections, its generator formula gives evaluation,
   naturality gives compatibility with differentials, and the cycle projection
   calculations establish the exact required homology formula. The degree-zero
   shift is explicitly undone. No boundedness, injectivity or nonemptiness is
   used, so zero complexes and empty pullbacks remain covered.
4. **Route and pruning: PASS.** Searched Mathlib with an independent `msearch.py`
   grep query and searched both Lean source roots. Compared the nearby
   `EtaleFreeSheafDerivedSections` and `EtaleOpenCohomologyComparison` constructions.
   The former concerns module coefficients and derived sections, with private
   complex comparisons; the latter supplies only the free-sheaf adjunction part.
   Neither replaces this pulled-back abelian-sheaf chain evaluation theorem or
   its cycle compatibility calculation with a shorter complete proof. The proof
   already uses Mathlib's from-single equivalence and homotopy-class equivalence.
   Both imports are needed, all three original proof dependencies are used, and
   `## No longer needed` is complete. Read the unit record: its realized statement
   and step lists are empty; the original two-step route is retained.
5. **DAG: PASS.** Read the item node and the declarations of its three proof
   dependencies. Its two proof steps and proof_deps match the Lean construction.
   No statement or dependency changes are necessary. The original proof_origin
   correctly credits the Q1 route followed here; it is retained unchanged.

Second reading changed no Lean code or DAG node. Added this independent review.
The sole original hole is closed, with zero added holes;
this is a proof, not a decomposition.
