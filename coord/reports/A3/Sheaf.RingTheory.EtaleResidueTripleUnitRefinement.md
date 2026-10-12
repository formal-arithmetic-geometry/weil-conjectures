## What changed

Repair for the returned delivery: correct the DAG proof metadata and the
second-reading note for the kernel calculation. No further Lean change is required for the return repair.

Proved `AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement` in
`Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`, with its signature unchanged.
The proof constructs `Localization.Away f`, extends the map to K by the localization
universal property, defines the new prime as its kernel, and constructs the residue-field
embedding with `Ideal.ResidueField.lift`. It verifies the prime over p, compatibility with
chi, etaleness, and the morphism of triples explicitly. Mathlib proves that the image of f
is a unit. The node now records the residue-field identification as the source of the kernel
calculation, marks that step elementary, and removes the incorrect simple-root-stage
proof dependency. The Lean proof and imports are unchanged.

Sources read: Stacks Algebra Tag 04GN, specifically the paragraph constructing the
morphism `(S,q) -> (S_f,qS_f)` for f outside q; Tag 04GP, which applies the same proof to
triples; and Tag 00U2(1),(2), principal-localization etaleness and composition. The local
Stacks copy is `/home/ubuntu/c1-stacks-review/algebra.tex`. The unit record `sk-thm-p1`
was read; this node does not itself realize a unit step and the unit route is preserved.

Searches: LeanFinder for extension of a field-valued ring map to principal localization;
Loogle for `IsLocalization.Away.lift`; and grep for principal-localization etaleness.
These found `IsLocalization.Away.lift`, `lift_eq`, `algebraMap_isUnit`, and
`Algebra.Etale.of_isLocalizationAway`. Library searches found the existing private kernel
and residue-field constructions, but no public theorem already stating this refinement.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement`
(node `lem-weil-pbc-etale-triple-unit-refinement`).
No holes added or split off. No sorry remains in the delivered module. The existing helper
`triple_map_eq_zero` is reused. This is a proof, not a decomposition.
Single-file compilation succeeds without warnings under the normal project options.
The axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

The construction applies to arbitrary fields K; it does not use separable closedness.
If f is already a unit the same localization argument applies. A nilpotent f or f = 0
cannot satisfy the stated outside-prime hypothesis, and a zero ring has no prime p.
The prime and residue embedding are constructed directly, not selected from an unproved
existence theorem.

## No longer needed

None of the original imports or proof-dependency nodes are pruned. The only original
import, `Sheaf.AlgebraicGeometry.EtaleResidueTriples`, is needed for the statement.
A tentative explicit `Mathlib.RingTheory.Localization.Away.Basic` import was removed
because the existing import already supplies the API. The simple-roots construction
module is now needed solely for its proved kernel
helper; none of its simple-root or colimit theorems is used by this proof. No original
node or module is pruned. The duplicate local helper is removed.

## Where the brief, the DAG or earlier work was wrong

The returned version attributed the kernel calculation to the simple-root-stage
statement. This repair records the residue-field identification and injectivity
argument requested by the reviewer. No Lean proof or interface change is needed.
No mathematical error found. The DAG's localization construction is valid.
The proof uses the ring-level localization-etaleness theorem directly instead of first
constructing its open-immersion structure; the planned composition dependency is retained.
An initial elaboration timeout was resolved by specifying the localization type in
`lift_eq` and changing to the explicit ring-map equality. No heartbeat increase or
transparency override remains.


## Earlier second reading (a previous round; superseded)

1. Compared the refinement module with the repository using `diff -u`. Its
   complete signature, docstring, proof, and imports are unchanged; this repair
   changes only DAG metadata and this report. No target changes. PASS.
2. Compiled both files in import order using `lcompile.py --all`: clean, without
   warnings (3.4 s and 3.0 s). Source scanning found no `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, or `extern` in either delivered file. A scratch
   copy with `#print axioms` checked both `etaleResidueTriple_unit_refinement`
   and `triple_map_eq_zero`: only `propext`, `Classical.choice`, and `Quot.sound`.
   The localization, its field map, prime kernel, and residue-field lift are
   explicit constructions; no arbitrary witness is selected from an unproved
   existence theorem. PASS.
3. No statements or holes are split off and no new nodes are introduced.
   Read the reused kernel helper: injectivity of the two field maps and
   `Ideal.algebraMap_residueField_eq_zero` prove precisely the needed kernel
   equality. For f a unit the localization construction remains valid;
   zero and nilpotent f cannot meet the outside-prime hypothesis. A zero base
   ring has no prime p. The proof needs no separable-closure hypothesis. Searched
   the library by kernel, residue-field lift, and localization concepts and
   searched Mathlib with `msearch.py ... grep 'ker.*residue|residue.*ker|Away.lift'`;
   the existing helper is correctly reused, with no duplicate introduced. PASS.
4. Read the proof from the refinement down: extend the field map to the
   principal localization, lift through its kernel residue field, verify all
   triple fields and the induced morphism, then apply the Mathlib unit lemma.
   Both imports are needed; the helper import is correctly proof-only. No old
   proof dependency is dropped, so `No longer needed` is complete. Checked the
   unit `sk-thm-p1` and its `realized` fields: this refinement is below the unit
   level and bypasses none of its steps. Verified the localization paragraph
   and its extension to triples in the local Stacks algebra source,
   `lemma-henselization` and `lemma-strict-henselization`. PASS.
5. Compared the node JSON to the original and read both dependency nodes.
   The kernel calculation follows from the residue-field identification and
   injectivity of the subsequent field maps; the existing `triple_map_eq_zero`
   helper implements this calculation. The updated proof describes that
   calculation, localization APIs, residue-field lift, and etale composition.
   `proof_deps` is the union of the steps' `uses`, and `proof_origin` states this
   route. No mathematical statement or Lean signature record changes. Ran
   `tools/downstream.py ... --uses triple_map_eq_zero`: its only existing user
   module is the construction module. The metadata now attributes the kernel
   calculation to the residue-field identification and injectivity, as requested.
   PASS.

Second reading changed only this report and the DAG metadata to record the independent checks.
No Lean proof, statement, definition, or import required repair.
Closed holes: `AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement` (one).
Added holes: none. Split-off statements: none. Pruned original modules/nodes: none.


## Second reading by A3

1. PASS. Independently compared every delivered Lean file with the repository
   using `diff -u`. There is one delivered module. The theorem signature and
   existing docstring are byte for byte unchanged; the changes are its proof,
   author credit, and one proof-only import. No definition or target changes.
   Corrected the node's recorded Lean signature, which contained literal Unicode
   escape strings rather than the actual signature. This is a recording repair,
   not a mathematical statement change.
2. PASS. Ran `lcompile.py --all` on the sandbox: clean compilation. Compiled a
   scratch copy with `#print axioms` for the refinement theorem and reused
   `triple_map_eq_zero`: only `propext`, `Classical.choice`, and `Quot.sound`.
   No sorry or forbidden declaration occurs in the delivered module. The
   localization, extended ring map, kernel prime, and residue lift are explicit;
   no data is selected from an unproved existence theorem.
3. PASS. No split-off statements, new holes, or new nodes. Read the kernel
   helper's proof: the canonical residue-field identification followed by
   injective field maps reduces vanishing to
   `Ideal.algebraMap_residueField_eq_zero`. Independently searched Mathlib with
   `msearch.py ... grep 'ker_algebraMap_residueField|algebraMap_residueField_eq_zero'`
   and searched the library for residue kernels and refinements. The existing
   helper is reused; no duplicate theorem is added. If f is already a unit the
   construction works; zero or nilpotent f cannot be outside the prime, and the
   argument needs no separable-closedness hypothesis on K.
4. PASS. Read the proof top downward: localization universal property, kernel
   prime and residue lift, compatibility and etale composition, then the unit
   conclusion. Both imports are used; the helper import is proof-only. The sole
   old proof dependency (etale composition) remains, so no original dependency
   or module is pruned. Read `sk-thm-p1.realized`: this node realizes none of its
   prescribed steps and the unit route is preserved.
5. PASS. Read the delivered node and both proof-dependency records. The kernel
   step correctly cites the residue-field identification and is elementary;
   the simple-root-stage statement is not used to justify it. The second step
   describes exactly the residue lift and Mathlib etale composition in Lean.
   `proof_deps` equals the union of the steps' `uses`. The proof origin agrees.
   The return's requested metadata repair is present.

Second reading changed the node's recorded Lean signature and this report.
No Lean proof repair was needed. Closed holes:
`AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement` (one).
Added holes: none. Split off: none. Pruned: none.
