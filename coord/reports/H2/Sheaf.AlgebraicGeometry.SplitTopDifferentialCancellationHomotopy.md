## What changed

Proved `AlgebraicGeometry.Scheme.Modules.split_top_differential_cancellation_homotopy`
without changing its signature, visibility, or imports. The contracting family is the chosen
section from degree m+1 to m, zero elsewhere. Mathlib constructs its boundary as a chain map.
The projection id minus that boundary fixes the truncation inclusion and vanishes above m.
Its abelian image is supported below m; truncating the image therefore gives an isomorphism,
and truncation naturality provides the reverse chain map. Mono cancellation proves the first
inverse identity, and the explicit null homotopy proves the second.

Updated the existing DAG node's proof and proof_origin to record this factorization route.
No definitions, interfaces, other modules, or unit statements were changed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Modules.split_top_differential_cancellation_homotopy`
(node `lem-pc-split-top-differential-cancellation-homotopy`). Added 0 holes. No sorry remains
in the delivery. Single-file compilation passes without warnings. The argument treats m=0,
zero complexes and empty schemes without exceptions; no lower support bound is used.

## No longer needed

None. Both existing public imports are needed for the statement. No new proof dependency
module is imported. No existing node or module is pruned. The degreewise kernel inverse and
canonical term-isomorphism calculations of the original plan are replaced by the abelian
image factorization and truncation naturality.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or tool failure found. The DAG's construction is valid, but Mathlib's
nullHomotopicMap automatically supplies its chain-map equations, and the image factorization
avoids constructing the reverse map component by component. The unchanged unit route is
canonical split cancellation. Searches in the source library and Mathlib found no ready-made
truncation homotopy equivalence; the existing split-identity lemma applies only to module
chain complexes with a rank-one complementary summand and is not needed here.

## Second reading by H2

1. **Interfaces unchanged — pass.** Compared the sole delivered Lean module with
   the repository by `diff -u`: only the body replacing `:= by sorry` differs.
   The theorem signature, visibility, imports, docstring and all definitions are
   byte-for-byte unchanged. No change record or forced adaptation is needed.
2. **Proof and trust — pass.** Compiled the module with `lcompile.py` without
   errors or warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.split_top_differential_cancellation_homotopy`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the delivered Lean for sorry and forbidden trust mechanisms: none.
   The section is obtained from the supplied split-epimorphism hypothesis, and
   the image and inverse use proved categorical constructions; no data is chosen
   from an unproved existence theorem.
3. **Split statements — pass, none.** No new declaration or split-off hole is
   introduced. Checked the degree cases: at m the inclusion kills the differential;
   at m+1 the section equation kills the projection; above m+1 the support
   hypothesis applies. The same equations cover m=0, zero terms, empty schemes,
   and arbitrarily negative degrees without a lower support hypothesis.
4. **Shortest route and pruning — pass.** Independently searched Mathlib for
   `HomotopyEquiv.*trunc|trunc.*HomotopyEquiv`, and searched the repository with
   split-cancellation and homotopy/truncation terminology. No ready-made result
   with this statement was found. The existing module-complex split-identity
   cancellation requires extra summand data and does not shorten this proof.
   Both public imports provide statement-level material (homotopy equivalence
   and scheme-module complexes). The old proof_deps consists solely of
   `def-pc-cochain-complex-modules`, which remains used: nothing is pruned.
   Inspected `dag/units/sk-thm-picard-coherence.json`: its realized fields are
   unchanged, and shortening by split cancellation remains the unit's route.
5. **DAG agrees — pass.** Compared the node versions: only proof and proof_origin
   changed. Its four steps match the boundary map, fixed inclusion, image
   factorization, and inverse homotopies in Lean. proof_deps is the union of
   the recorded uses; the node's statement and Lean record are unchanged.

Changes made by the second reading: this review section only. No Lean or DAG
repair was needed. Closed 1 of 1 original holes and added 0 holes; this is a
proof, not a decomposition.
