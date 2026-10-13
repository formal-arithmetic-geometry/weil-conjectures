## What changed

Proved `AlgebraicGeometry.globalSections_unit_isIso_of_point_unit` in
`Sheaf.AlgebraicGeometry.GlobalSectionsPointUnitTransport`, with its signature and
visibility unchanged. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`.
The existing public imports stay unchanged.

Three proved private helpers implement the transport: `point_sections_comparison`
constructs the underived comparison using restriction of scalars along the identity;
`unit_isIso_comp_of_exact` uses right-derived uniqueness to transport invertibility
through exact postcomposition; `unit_isIso_of_natIso` proves the unit compatibility
for naturally isomorphic additive functors. The main proof extracts exactness of
point evaluation from the existing
`AlgebraicGeometry.schemeDerivedGlobalSections_point_comparison` theorem, applies
these two categorical transports, and obtains the requested unit. It does not choose
any new public data from an unproved existence theorem.

Updated the proof steps and proof origin of
`new-global-sections-point-unit-transport` to describe the actual Lean proof; its
proof dependencies remain `def-pc-global-derived-rhom`. No new module, statement,
node, or interface change is needed. The unit record has no realized entries for
this auxiliary node; no unit statement or proof step is bypassed.

Searches: LeanFinder through msearch found generic right-derived uniqueness and
natural-isomorphism lemmas; Loogle returned no match for the shorthand query;
msearch grep found no exact unit transport theorem. Local rg searches found the
proved exact-postcomposition pattern in GlobalSectionsDirectImageKInjectiveAcyclic
and the supporting proved upstream derived-functor declarations. That upper module
is not imported, since its dependency route passes through this item.

Validation: lcompile.py compiled the delivered module cleanly in 4.7 seconds.
The import-direction check accepts the added upstream import. The proof is generic
in the homotopy object: empty schemes, the zero ring, and zero complexes require no
extra assumptions or cases. No existing signature or target has changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.globalSections_unit_isIso_of_point_unit`
(node `new-global-sections-point-unit-transport`).
Added 0 holes; 0 holes remain in the delivered module; 0 statements split off.
All three private helpers are proved. This is a proof from an existing stated
lower dependency, not a new decomposition.

The existing dependency
`AlgebraicGeometry.schemeDerivedGlobalSections_point_comparison`
(node `def-pc-global-derived-rhom`, module
`Sheaf.AlgebraicGeometry.GlobalDerivedHom`) remains unproved in the library and is
used only to obtain exactness of point evaluation. It is not changed or delivered.
The result therefore still depends on that existing lower hole, as intended by
stage 3.

## No longer needed

None. No existing imports were removed and no node or module was pruned. Both
existing public imports and the one added proof-only import are retained.
The existential derived comparison in schemeDerivedGlobalSections_point_comparison
is unused: only its point equivalence and identification with evaluation are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG described unit compatibility but did
not provide it as a separate theorem. It is proved here, using the existing generic
right-derived naturality and uniqueness API, rather than assumed from a bare
existential derived-functor isomorphism. The node now records these explicit steps.


## Second reading by J4

1. Interface: PASS. Read the complete module and its diff against the repository.
   The original public theorem signature is byte-for-byte identical, including all
   universes, instances, hypotheses and its conclusion. Existing public imports,
   visibility and definitions are unchanged. The only added import is proof-only;
   the three helpers are private. No change record or forced adaptation is needed.
2. Proof: PASS. Independently compiled the delivered file with lcompile.py without
   errors or warnings (6.2 seconds). A scratch copy with explicit #print axioms for
   all four declarations compiled successfully. Each private helper uses only
   propext, Classical.choice and Quot.sound; the public theorem additionally uses
   sorryAx through the existing point-comparison dependency. No textual sorry,
   axiom, unsafe, opaque, implemented_by, extern or kernel-check bypass occurs in
   the delivered module. The comparison definition constructs its components from
   restrictScalarsId. The existential point equivalence is eliminated only within
   the proof of the proposition IsIso to transfer exactness to the already defined
   evaluation functor; no arbitrary witness is used to define public data.
3. Split statements: PASS, none. No holes or public statements were added. Read
   the exact-postcomposition and natural-isomorphism helper proofs, including their
   factorization equations and cancellation directions. They apply to arbitrary
   homotopy objects, so the zero complex, zero ring and empty scheme create no
   missing case. There is no restatement passed to a new unproved theorem.
4. Route and pruning: PASS. Read the upstream Comp and MapDerivedCategory APIs and
   searched the local library for unit-invertibility and homotopy-isomorphism
   alternatives; an additional msearch grep query found no exact transport result.
   The existing exact-postcomposition helper in the upper acyclicity module is
   private and that module depends on this item, so importing it would be cyclic.
   The proof uses the shortest available generic uniqueness/naturality route found.
   Both public imports provide signature vocabulary, and MapDerivedCategory
   supplies the exact-postcomposition theorem and exact-unit instance used in the
   proof. The original proof_deps consists only of def-pc-global-derived-rhom, which
   is still used; No longer needed is complete. Read sk-thm-picard-duality.json:
   its realized statement and step lists are empty, and no unit route is bypassed.
5. DAG: PASS. Compared the delivered node with the repository node: only proof
   and proof_origin changed. The three proof steps describe exactly the concrete
   comparison, exactness transport, right-derived uniqueness and unit naturality
   implemented in Lean. proof_deps remains the union of their cited node uses and
   names the unchanged GlobalDerivedHom dependency. The stored Lean signature
   agrees with the unchanged declaration. No new-node metadata is required.

Second reading changed only this report, adding the independent checks and axiom
results. No mathematical or Lean repair was necessary. Closed 1 original hole,
added 0 holes, left 0 holes in this module, and split off 0 statements; the existing
lower point-comparison hole remains, so this is not an axiom-free target proof.
