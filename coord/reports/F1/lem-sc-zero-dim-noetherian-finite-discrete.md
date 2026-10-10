1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-zero-dim-noetherian-finite-discrete.json` — item, split into three proof steps.
   - `dag/nodes/sec-curve-estimates/lem-sc-zero-dim-noetherian-closed-finite.json` — statement node matching the sorry-free slopmaster2 topological theorem; Mathlib itself has no matching declaration.

2. Attachments:
   - `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero` belongs to `lem-sc-zero-dim-noetherian-closed-finite`.

3. WANTED:
   - None.

4. Problems and corrections:
   - The imported item had no proof. I checked the Stacks Properties Lemma 0AAX route and supplied the missing setup, zero-dimensional application, and finite-T1 discreteness argument. The setup cites the existing Noetherian closed-subset minimal-condition node, the existing locally-Noetherian quasi-separated node, and the existing qcqs spectral-space node; this makes the Noetherian and T0 hypotheses of the attached theorem explicit.
   - I checked the imported `lem-sc-dim0-finite` blueprint node and retained it as `same_as` on the new topological child, since it is the finite-type scheme specialization of the same zero-dimensional finiteness fact. The assigned item's blueprint ancestor and zero-dimensional component place are preserved.

## Review by F1

I read the assigned item and the affine citer, then read Stacks `properties.tex`, Lemma 0AAX, including its empty-space case and its conclusion that a zero-dimensional Noetherian space is finite with closed points. For step 1 I read the statements of `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, `lem-weil-pbc-locally-noetherian-quasi-separated`, and `lem-weil-pbc-qcqs-scheme-spectral`; each says exactly the condition used: Noetherian underlying space, quasi-separatedness, and spectral/T0 structure. For step 2 I read the full slopmaster2 declaration and docstring at `WeilConjectures/Mathlib/Topology/KrullDimension.lean:241-279`; it states the finite closed-subset result used, is sorry-free, and is recorded as the new node's closed audit. Step 3 is the elementary finite-union-of-closed-singletons argument, with the empty space checked separately. I searched the DAG and blueprint for duplicate statements, ran the three required Mathlib search kinds for the new node, and recorded verbatim quotes for every citation in `citations.json`. I also tested the edge cases conceptually: the empty scheme, a one-point spectrum, and a finite disjoint union of zero-dimensional local pieces all satisfy the conclusion.
