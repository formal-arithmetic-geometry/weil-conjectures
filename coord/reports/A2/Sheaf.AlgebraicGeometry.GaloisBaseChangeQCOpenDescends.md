## What changed

Proved `AlgebraicGeometry.galois_baseChange_qc_open_descends` in
`Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends`, preserving its statement and
all existing public imports. Two proved private helpers establish multiplication and
identity for `specAlgEquivOver`; base-change composition then supplies the action and
its inverse.

The proof applies the existing `descend_qc_open_fg_subalgebra`, makes its finitely
generated subalgebra finite-dimensional using
`Algebra.finite_adjoin_of_finite_of_isIntegral`, and turns it into an intermediate
field using `fieldOfFiniteDimensional` and `Subalgebra.toIntermediateField'`.
These constructions preserve the underlying subalgebra definitionally, so the open
and its canonical projection are used directly. Pointwise fixing gives the projection
identity by `Spec.map_comp`; inverse-image invariance and surjectivity of the scheme
isomorphism give image invariance.

No definitions or existing signatures changed. No new modules, nodes, or imports.
The original five-step DAG plan and its proof dependencies remain accurate.

## Proved and sorry left

Closed one of one holes in the item:
`AlgebraicGeometry.galois_baseChange_qc_open_descends`
(node `lem-weil-pbc-galois-base-change-qc-open-descends`).

No holes remain in the delivered module. No holes added or split off.
The existing imported theorem `AlgebraicGeometry.descend_qc_open_fg_subalgebra`
(node `lem-weil-pbc-descend-qc-open-fg-subalgebra`) remains an unproved dependency;
this delivery proves the item from it, as stage 3 requires. This is not a claim that
the transitive proof is sorry-free.

Validation: the complete module compiles through the prescribed `lcompile.py` without
errors or warnings. The delivery dry run performs the final checks.

## No longer needed

None. All original imports and DAG proof dependencies are retained. Two experimental
Mathlib proof imports were removed after confirming the original imports already
provide the needed finite-dimensional and integral-generation declarations. No
library modules or nodes are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

None. The finite-dimensional subalgebra can be turned into an intermediate field
without transporting the descended open across a separately chosen isomorphism:
`Subalgebra.toIntermediateField'` preserves its underlying subalgebra definitionally.
This is an implementation simplification within the original route.


## Second reading by A2

1. **Interface: pass.** Read the complete repository/sandbox diff. The existing
   theorem signature, including its embedded proof of the canonical projection's
   commutativity, is byte-for-byte identical. Its docstring, visibility, and all
   imports are unchanged. The only additions are two private proved helpers and
   the replacement of the item's `sorry`. No definition or change record is added.
2. **Proof: pass.** Compiled the delivered file through `lcompile.py` without
   errors or warnings. A scratch copy with `#print axioms` checks the main theorem
   and both private helpers. Helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; the main theorem additionally uses `sorryAx`, as expected from
   the existing `descend_qc_open_fg_subalgebra` dependency. No forbidden declaration,
   new `sorry`, or hollow definition occurs. Existential descent witnesses are
   eliminated inside a theorem proving an existential conclusion; no definition
   selects arbitrary data from an unproved existence theorem. The conversion to
   an intermediate field keeps the subalgebra's carrier and algebra structure.
3. **Split statements: pass (none).** No statements were split off. Both private
   helpers are proved directly by functoriality of `Spec`; their multiplication
   order matches the contravariant action. Checked identity, trivial extension,
   empty open, and empty generating set cases: the argument requires no nonempty
   open, positive extension degree, or nonempty generator set. Read Mathlib's
   finite-adjoin, finite-dimensional-field, and subalgebra-to-intermediate-field
   constructions, and independently confirmed the finite-adjoin declaration with
   the prescribed Loogle search. No unsupported replacement lemma is introduced.
4. **Route and pruning: pass.** The proof follows all five original DAG steps:
   action and inverse, finitely generated descent, finite field construction,
   projection commutation, and image invariance. Searched the library and upstream
   for the target and action helpers; found no shorter existing theorem closing
   the descent result. Public imports supply the existing statement's Galois,
   scheme/open, base-change, and `specAlgEquivOver` vocabulary; the descent theorem
   is correctly imported privately. No proof dependency is abandoned, so
   `## No longer needed` is complete. Read `dag/units/sk-thm-p1.json`: its statement
   and realized steps are retained, with no change to the unit's route.
5. **Nodes: pass.** Read the item's node, its descent dependency, and the two
   Mathlib leaf nodes. The current `proof`, seven `proof_deps`, and documentary
   `proof_origin` describe the Lean proof accurately; no node edit is needed.
   No new nodes or change records are required.

Second reading changed only this review report. Lean code and DAG records passed
unchanged. One original hole closed, zero added, zero split off; the imported
open descent theorem remains an explicitly reported dependency.
