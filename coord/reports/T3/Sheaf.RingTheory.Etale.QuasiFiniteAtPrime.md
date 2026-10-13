## What changed

Proved `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale` with its signature
unchanged. Converted the affine scheme hypothesis to `Algebra.Etale` using
Mathlib's `HasRingHomProperty.Spec_iff` and `RingHom.etale_algebraMap`.
Mathlib instances supply finite type, quasi-finiteness and Artinian fibre rings.
Unfolding `IsQuasiFiniteAtPrime` makes `isOpen_discrete` finish the proof.
Replaced the private import of `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
with `Mathlib.RingTheory.Unramified.LocalStructure`; public imports are unchanged.
Updated the existing node's proof, proof_deps and proof_origin to this route.
No unit statement or realized unit step is bypassed: this is a shorter proof of
one tool node below the unit level. No new statements or definitions were added.

## Proved and sorry left

Closed the sole hole: `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale`
(node `lem-weil-pbc-etale-ring-map-quasi-finite`). Holes closed: 1; holes added: 0.
No sorry remains in the module, and no intermediate theorem was split off.
The local single-file compile passes. A scratch copy with `#print axioms` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
The proof handles zero rings and empty fibres through the same Mathlib instances.

## No longer needed

Removed import/module `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
(node `lem-weil-pbc-spec-finite-product-fields`). The proof also no longer needs
these planned dependencies: `def-weil-pbc-mv-polynomial-ring`,
`lem-weil-pbc-etale-ring-base-change`,
`lem-weil-pbc-etale-algebra-over-field-product`, `def-pc-field-extension`,
`def-weil-pbc-separable-algebraic-extension`, and `def-weil-affine-spectrum`.
These are pruned from this node's proof_deps only; the affine spectrum notion
remains in its unchanged stmt_deps. There were no separate imports of these
Mathlib leaves in the original module. The finite-product decomposition and
tensor-swap arguments are unnecessary. This report makes no claim that other
callers no longer need the pruned nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error. The DAG's Mathlib candidate unnecessarily anticipated a
conversion through `quasiFiniteAt_iff_isOpen_singleton_fiber`. The project defines
its fibre point directly in the spectrum of `p.Fiber S`, whose discrete topology
is inferred from Mathlib quasi-finiteness; there is no additional agreement lemma
to prove. The earlier four-step plan is valid but longer than necessary.
The existing declaration docstring retains that source proof; the node records
the actual shorter Lean implementation.

## Second reading by T3

1. **Unchanged interface — pass.** Compared the delivered Lean module with the
   repository using `diff -u`: the sole declaration's signature, universe,
   namespace, visibility, docstring, and both public imports are byte for byte
   unchanged. Only the proof and one private import differ. No definitions,
   hypotheses or conclusions were changed; no change record is required.
2. **Proof and axioms — pass.** Independently compiled the delivered file with
   `lcompile.py` (exit 0, no warnings). Compiled a scratch copy containing
   `#print axioms Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale`:
   only `propext`, `Classical.choice`, `Quot.sound`. The module contains no
   `sorry`, axiom, unsafe/opaque declaration or implementation override.
   `Spec_iff` converts precisely the hypothesis on the algebra map; the inferred
   finite-type witness supplies the conclusion's instance, and
   `isOpen_discrete` proves the singleton of the canonical fibre prime open.
3. **Split statements — pass, none.** No helper statement, definition, module,
   node or hole was added. Checked the Mathlib instance at
   `Unramified/LocalStructure.lean:330–333` and the finite-fibre/Artinian
   instances at `QuasiFinite/Basic.lean:67–78`. They impose no extra nonzero-ring
   or inhabited-spectrum assumption. Zero rings and empty spectra are allowed;
   a quantifier over an empty spectrum is vacuous.
4. **Shortest route, imports and pruning — pass.** Read
   `Algebra.IsQuasiFiniteAtPrime`: its point is already in the spectrum of
   `p.asIdeal.Fiber S`, so no comparison with `Algebra.QuasiFiniteAt` is needed.
   Library searches for `IsQuasiFiniteAtPrime` and the target's name reveal no
   shorter applicable proved theorem needed here. The private Mathlib import
   supplies the unramified-to-quasi-finite instance, and each public import is
   needed by the signature. The seven old proof dependencies removed from the
   node are all listed under `## No longer needed`; only the product-of-fields
   module had a separate private import to remove. Inspected
   `dag/units/sk-thm-p1.json` `realized`: neither this tool node nor any removed
   dependency realizes a unit statement or step. The unit route is unchanged.
5. **DAG — pass.** The node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Checked the retained dependencies' Lean/Mathlib records:
   affine étaleness uses `HasRingHomProperty.Spec_iff`, fibre rings use
   `Ideal.Fiber`, and the definition uses the canonical fibre correspondence.
   The three recorded steps describe the compiled proof and its instance chain;
   their `uses` union equals `proof_deps`. The statement, statement dependencies,
   source and unit are unchanged.

Second-reading changes: this review and the explicit axiom-check evidence in
`## Proved and sorry left`. No repair of the Lean proof or node was necessary.
