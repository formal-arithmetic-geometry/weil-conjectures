## What changed

Proved `AlgebraicGeometry.etaleSetInverseImageConstantSheaf_exists` using the constant-sheaf
adjunction and uniqueness of left adjoints. Replaced the unused composition-units public import with the definition module
`Sheaf.AlgebraicGeometry.EtaleSheaves`. Updated the node proof and
proof dependencies to record this route.

## Proved and sorry left

The declaration `etaleSetInverseImageConstantSheaf_exists` is fully proved; no `sorry` remains.

## No longer needed

Removed the unused proof imports `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`, and
`Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`.

Also removed `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`: neither its
composition theorem nor its helpers occur in the signatures or proof. The signatures instead
need `Sheaf.AlgebraicGeometry.EtaleSheaves`, now the sole direct public import. The initially
added proof import `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf` was redundant
through `EtaleSheaves` and was removed during second reading.

The planned representability, inverse-image-representable, and indexed-coproduct base-change
nodes are not used by this proof: `lem-galois-constant-sheaf-sets-representable`,
`lem-galois-inverse-image-representable`, and
`lem-weil-pbc-sets-etale-inverse-image-constant-base-change`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was unnecessarily long. The existing Mathlib constant-sheaf adjunction,
together with the continuous étale base-change functor and uniqueness of left adjoints, directly
constructs the required isomorphism and its canonical-section equation.


## Second reading by S1

1. Compared the sole delivered Lean module with the repository using `diff`. Both existing
   definitions, their bodies, and the theorem signature are byte-for-byte unchanged. No new
   declarations or changed statements. The public-import change is recorded in
   `coord/changes/EtaleSetInverseImageConstantSheafExists-imports.md`. Verdict: pass.
2. Compiled the original worker proof and the repaired module with `lcompile.py`, without errors
   or warnings. A scratch copy with `#print axioms` for all three declarations reports only
   `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, hollow definition, or forbidden
   declaration mechanism remains. Verdict: pass.
3. No split-off statements or new nodes. The construction applies to arbitrary schemes and
   arbitrary E, including empty E and empty schemes: it uses only terminal objects, adjunctions,
   and their unit equations, with no nonemptiness or inhabitedness assumption. Verdict: pass.
4. Read the upstream constant-sheaf pullback isomorphism and Mathlib's left-adjoint uniqueness
   and unit equation, and searched Lean for those declarations and related proofs. The worker
   uses the same shortest adjunction route, specialized to the explicit inverse-image functor
   required by this signature; the section equation still needs its displayed unit computation.
   All three old proof-dependency nodes are listed under No longer needed. Read
   `dag/units/sk-thm-iff.json`: its statement and step are realized by
   `lemma-weil-pbc-property-iff-acyclicity`, not any pruned node. This reduction only changes the
   helper below that unit and retains inverse-image constancy in the underived exchange route.
   Verdict: pass after import repair.
5. Read the item node and every cited dependency. Added the existing Mathlib-leaf node for the
   continuous-functor sheaf pullback adjunction, which the worker's metadata had omitted. Split
   the proof description into terminal-object, composite-adjunction, and unit-equation steps;
   made `proof_deps` their exact union and recorded the actual declarations in `proof_origin`.
   The conjugate-isomorphism node is used in its identity-right-adjoint specialization, supplied
   by Mathlib's `unit_leftAdjointUniq_hom_app`. Verdict: pass after metadata repair.

Changed only imports and proof metadata; the Lean proof body was already correct and is kept.
Removed the unused composition-units public import and the redundant newly added constant-sheaf
proof import. Replaced the public import with the module that defines `Scheme.etaleSetPullback`.
No statements, definition bodies, unit records, or target meanings changed.

Public-import change record: `coord/changes/EtaleSetInverseImageConstantSheafExists-imports.md`.
It lists all 217 downstream modules; neither direct importer needs adaptation.
