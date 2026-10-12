## What changed

Proved `AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_component_epi` in
`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComponentEpi` with its signature and
visibility unchanged. The proof calculates the image of the concrete inclusion:
each retained summand map is an isomorphism, and the finite supremum of their
images is the filtered step. The existing factorization supplies the other image
containment, and the upstream image-factorization lemma gives epimorphicity.
Updated the node's proof, proof dependencies and proof origin to describe this
argument. No definitions, statements, public imports or other modules changed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_component_epi`
(node `lem-weil-pbc-etale-restricted-sections-component-epi`).
No `sorry` remains in the delivered module; no holes or new declarations were added.
This is a proof, not a decomposition. The module compiles without warnings through
`lcompile.py`. The delivery dry run printed OK (compilation and preflight; second reading pending),
with nothing pushed. An explicit `#print axioms` check reports `propext`,
`Classical.choice`, `Quot.sound`, and inherited `sorryAx`: the delivery closes
this module's named hole, but does not claim the transitive dependencies are
already completely proved. The axiom-check command was removed after inspection.
The finite-supremum proof also covers empty diagonals (`n < q`), negative indices,
and zero summands without additional assumptions.

## No longer needed

None of the original imports, nodes or modules is removed. The proof still needs
both original definition dependencies and the already proved factorization lemma.
An experimentally added proof import of
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` was removed because its
proved image lemmas are already available through the existing public import;
the final module compiles with exactly its original imports.
No new monicity lemma or retraction construction is required: retained summand
isomorphisms suffice for this epimorphism argument.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or interface was found. The original node proof did not
list the existing restricted-sections factorization among its proof dependencies.
This proof explicitly uses it for the upper image containment and adds its node to
`proof_deps`. The expanded finite-coproduct construction suggested by the plan is
unnecessary: the total-map coprojection identity and the existing filtration
formula supply the finite-supremum argument directly. The unit record has no
realized nodes, and no unit statement or proof step was bypassed.

## Second reading by U3

1. Compared the delivered module with the repository version. The theorem signature, declaration visibility, and all existing declarations are byte-for-byte unchanged; only the target proof body differs. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the permitted categorical and arithmetic lemmas; inherited dependencies may still expose `sorryAx`. Verdict: pass.
3. Checked the target node and searched the library for duplicate statements. The target statement is unchanged, the proof dependencies now include the factorization theorem actually used, and no new split-off statement was introduced. Verdict: pass.
4. Reviewed the proof route and imports. The image-subobject calculation is shorter than an explicit finite-coproduct construction, and the original public imports remain minimal; no proof-only import remains. Verdict: pass.
5. Checked the node's proof, proof dependencies, proof origin, and the unit record. They describe the implemented image equality and epimorphism transport, and no unit route is bypassed. Verdict: pass.

No code or node changes were needed during this second reading.
