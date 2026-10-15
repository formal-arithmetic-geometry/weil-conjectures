## What changed

Proved `CategoryTheory.cartanEilenberg_comparison_homotopy` in
`Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy` without changing its signature.
Constructed the transported augmentation using Mathlib's canonical single-complex
isomorphism, proved preservation of the cycle, boundary and homology resolution
quasi-isomorphisms by the exact functor, subtracted the augmentation squares, and
applied `CategoryTheory.cartanEilenberg_doubleComplex_homotopy`. Converted its total
null-homotopy to the required comparison homotopy with the same components and
filtration factorization. Added a proof-only import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images`.

The existing theorem has redundant assumptions because the supplied double-complex
lemma needs fewer fields; its complete signature is retained. The unused-variable
linter is disabled only for this declaration. No definitions, public imports or
other modules are changed. Updated the existing node's proof and proof dependencies
to match the Lean argument.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.cartanEilenberg_comparison_homotopy`
(node `lem-sp-cartan-eilenberg-comparison-homotopy`).

No `sorry` remains in the item, and no holes or new declarations were added.
This is a proof from the existing stated dependency
`CategoryTheory.cartanEilenberg_doubleComplex_homotopy`, whose own `sorry` remains
in its existing module and is not part of this delivery.

## No longer needed

Removed the redundant direct proof imports:

- `Sheaf.CategoryTheory.CartanEilenbergExists`;
- `Sheaf.CategoryTheory.DoubleComplexTotal`;
- `Sheaf.CategoryTheory.Filtration`;
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

These modules remain available transitively through the unchanged public import
`Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`; this delivery does not
remove them from the targets' import closure. In particular, no globally pruned
module is claimed. The proof no longer directly needs
`lem-sp-cartan-eilenberg-exists`: the resolutions and all fields are supplied as
hypotheses. It does not separately invoke `def-sp-filtration`; the factorization
is supplied by the double-complex lemma. The total-complex definition node remains
a proof dependency for the coprojection calculation. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool fault was found. The existing double-complex lemma
already includes totalization and the filtration factorization, so the item's
last two planned steps do not require a second construction of the horizontal
and vertical components. The source resolution transport is ordinary Mathlib
naturality and preservation of quasi-isomorphisms; it needs no new lemma or node.

## Second reading by P4

1. **Signatures and accidental changes.** Compared the delivered module and node with the repository versions. The theorem signature is byte-for-byte unchanged; only proof imports, proof text, and the existing node's proof metadata changed. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no warnings and no local `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. A scratch `#print axioms` reports only the permitted base axioms plus `sorryAx` inherited from the imported open double-complex theorem. Verdict: pass.

3. **Statements and split-offs.** No statements were split off and no new nodes were added. The existing target theorem is proved directly from the supplied double-complex homotopy theorem, exact-functor transport, and totalization additivity. No duplicate library or Mathlib result was introduced. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing double-complex theorem and Mathlib image-preservation/naturality lemmas. Direct proof-only imports for Cartan--Eilenberg existence, filtration, and totalization were removed; totalization remains in the node because the proof uses its coprojection formula. The unit route is retained. Verdict: pass.

5. **DAG agreement.** The node's proof steps, `proof_deps`, and `proof_origin` describe the transported augmentation, subtraction, double-complex application, and totalization conversion used by the Lean proof. Verdict: pass.

Changed during second reading: appended this review only; no Lean declarations or node statements were altered.
