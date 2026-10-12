## What changed

Proved `AlgebraicGeometry.completion_internal_hom_quotient_annihilation` in
`Sheaf.AlgebraicGeometry.CompletionInternalHomQuotientAnnihilation`, with its original
signature and docstring unchanged. Added the proof-only import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.

Five proved private helpers implement image-factor cancellation, multiplication
naturality, the scalar/evaluation identity, quotient annihilation and internal-Hom
annihilation. The proof uses the cokernel relation and preservation of epimorphisms by
tensoring, then injectivity of uncurrying. It does not assume surjectivity on open sections.
The node's proof, proof_deps and proof_origin now describe this categorical argument.
The tensor-closed node `lem-pc-sheaf-modules-tensor-closed` is used as a generic tool;
its already-proved source implementation supplies `SheafOfModules.monoidalClosed`.
No unit statement or realized unit step is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.completion_internal_hom_quotient_annihilation`
(node `lem-weil-pbc-completion-internal-hom-quotient-annihilation`).
All five private helpers are proved. No sorry remains and no holes were added.
This is a complete proof, not a decomposition into new statements.

The argument allows n = 0, zero F or G, the zero ideal, the unit ideal and the empty scheme.
The private quotient argument even works for an arbitrary map J → O_X, without monicity.
Local compilation passed without warnings before the final import cleanup;
the delivery dry run recompiles the final file and probes its axioms.

## No longer needed

No original import, node or module is pruned. Both original public imports remain necessary
for the unchanged statement. The temporary experimental import
`Mathlib.Tactic.CategoryTheory.Monoidal.Basic` was removed: no tactic from it is used.
No local-lift or stalk lemma is needed beyond the existing definition imports.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The local-section proof plan can be implemented more
directly with the existing monoidal closed structure: tensoring preserves the cokernel
epimorphism, and scalar evaluation compatibility follows from categorical naturality.
The quotient-annihilation argument in CoherentFormalModule is private, so it cannot be
called by this module; the short image-cancellation argument is proved privately here.

## Second reading by M1

1. Compared the delivered module with the repository version. The public theorem signature and
all existing declarations are unchanged; only the proof and a proof-only import were added.
Verdict: pass.

2. Compiled the module with `lcompile.py` and checked the target's axioms. Compilation is clean,
and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no
`sorry`s, forbidden declarations, or hollow definitions. Verdict: pass.

3. Checked the private categorical helpers and the updated DAG proof steps. The helpers are
strictly intermediate facts, and the existing target statement is unchanged and true in the
zero, unit, and empty cases. No new public theorem or split-off node was added. Verdict: pass.

4. Reviewed the route for a shorter existing Mathlib or library result and checked imports.
The monoidal-closed tensor-Hom route is the shortest available route; the added import is proof
only, while both public imports remain required by the statement. Verdict: pass.

5. Checked the DAG node's proof, proof dependencies, origin, and unit route against the Lean
proof. The node records the tensor-closed dependency and preserves the realized unit path.
Verdict: pass.

Changed: added this second-reading record; no proof or statement changes were needed.
