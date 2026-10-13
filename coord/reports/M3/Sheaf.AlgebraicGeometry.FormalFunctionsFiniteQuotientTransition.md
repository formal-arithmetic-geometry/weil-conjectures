## What changed

Proved `AlgebraicGeometry.formalFunctions_finite_quotient_transition` in
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition`, preserving its
signature, visibility, docstring, and imports. Added only proved private helpers:
`finiteι_transition` proves the triangle by the pullback universal property;
`pushforward_pasting` checks the canonical direct-image identifications;
`adjoint_triangle` proves compatibility of adjoints using their unit equations;
`finiteFMap_transition` specializes it to the finite fibre maps; and
`cohomology_triangle` combines source naturality with composition.

The main proof cancels the epimorphic sheaf quotient projection, using the defining
cokernel equation for the transition and the given factorizations. It then applies
`moduleCohomologyFMap_source_naturality` and `moduleCohomologyFMap_comp`, and evaluates
the resulting equality on the cohomology class. It never cancels a cohomology map.
The original DAG plan and the unit route are followed, so no node update is needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.formalFunctions_finite_quotient_transition`
(node `lem-weil-pbc-formal-functions-finite-quotient-transition`).
No sorries remain in the item, and no holes or modules were added. All five private
helpers are proved. Existing dependencies may still rest on their own named sorries;
this delivery makes no claim to close those. This is a proof, not a decomposition.

Validation: the complete module compiled cleanly through `lcompile.py` (40 seconds),
with the default heartbeat limit. The delivery dry run performs the declaration and
axiom checks. The arguments apply uniformly to n = 0, p = 0, all higher degrees,
and zero modules; no invertibility or extra finiteness hypotheses were used.

## No longer needed

None. No imports were removed, and every dependency of the original three-step
proof plan remains used. No node or module is proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

None. The sheaf quotient projection is epi, as required by the plan. The
pushforward coherence calculation was proved for arbitrary scheme triangles before
specializing to the concrete fibres, avoiding expensive elaboration of the fibre
constructions. No definition, statement, or public interface was changed.

## Second reading by M3

1. **Public interface — pass.** Compared the only delivered Lean module with the
   repository using `diff -u`, and separately checked byte equality of the existing
   theorem signature and module header. The theorem's hypotheses, conclusion,
   visibility, and docstring are unchanged. All additions are proved private helpers;
   no definitions, public declarations, or other modules changed.
2. **Proof and axioms — pass.** Independently compiled the module with `lcompile.py`
   (32.5 seconds, no warnings or errors). Scanned for forbidden declarations and
   kernel-check bypasses: none; no `sorry` remains in the delivered source. Compiled
   a scratch copy with `#print axioms` for the theorem and all five helpers (43.6
   seconds). The first four helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; `cohomology_triangle` and the main theorem additionally depend on
   `sorryAx` through existing imported cohomology results. Thus this closes the
   item's one local hole, but does not certify its transitive dependencies as proved.
   Read the pullback triangle, direct-image pasting, adjunction naturality, quotient
   cokernel equation, and final evaluation on `x`. Only the sheaf cokernel projection
   is cancelled, never a cohomology map. The chosen adjunctions are those specified
   by the existing canonical unit formula; no arbitrary data witness is introduced.
3. **Split statements — pass, none.** No new holes or split-off statements exist.
   Each private helper is proved and is strictly part of the argument. The triangle
   and quotient arguments are uniform at `n = 0`, `p = 0`, higher degrees, and zero
   modules, and require neither invertibility of `e` nor a new finiteness assumption.
4. **Route, searches, and pruning — pass.** Searched with the alternate phrases
   "Compatibility of adjoint morphisms with composition and canonical pushforward
   identifications for sheaves of modules" (Lean Finder),
   `CategoryTheory.Adjunction.homEquiv_unit` (Loogle), and local searches for finite
   transition, adjoint triangle, and pushforward associativity. The results provide
   generic adjunction/direct-image facts, not an existing finite quotient transition
   theorem or a shorter replacement for these concrete identifications. The proof
   already uses the library's cohomology naturality and composition declarations.
   Read the finite FMap and transition FMap definitions and the canonical adjunction
   unit specification. The public imports supply notions in the statement (finite
   pullback, formal quotients, ideal comap); the cohomology functoriality import is
   correctly private to the proof. No dependency is unused, so `No longer needed`
   remains complete with none. Read `dag/units/sk-thm-p1.json` and its `realized`
   route; no unit statement or step is bypassed or changed.
5. **DAG agreement — pass.** Read node
   `lem-weil-pbc-formal-functions-finite-quotient-transition`: its three proof steps
   match, respectively, `finiteι_transition`/`finiteFMap_transition`, the epi
   cancellation establishing `hs`, and `cohomology_triangle` with evaluation on
   `x`. All six original `proof_deps` remain used; the recorded `proof_origin`
   describes this same canonical-map/adjunction argument. No new node is needed.

Changes by the second reader: this review section and its explicit axiom accounting
only. No Lean repair, node edit, added hole, or pruning was necessary.
