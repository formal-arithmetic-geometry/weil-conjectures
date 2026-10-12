## What changed

Proved `AlgebraicGeometry.Scheme.exists_idealSheafData_support_eq` in
`Sheaf.AlgebraicGeometry.ClosedSubsetQcIdeal` directly from Mathlib. The witness is
`IdealSheafData.vanishingIdeal ⟨Z, hZ⟩`; its support equality is
`IdealSheafData.coe_support_vanishingIdeal ⟨Z, hZ⟩`. The signature and visibility are
unchanged. Updated the node's proof, proof_deps and proof_origin to this route.
The single-file compile passes with no warnings.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.exists_idealSheafData_support_eq`
(node `lem-sc-closed-subset-qc-ideal`). No holes remain and no holes were added.
This is a proof from Mathlib, not a decomposition into new statements.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
and the dependency `lem-weil-pbc-reduced-induced-closed-subscheme` from this node.
Its reducedness, closed-immersion and uniqueness conclusions are unnecessary for
this proof. No other imports were removed; Mathlib.AlgebraicGeometry.IdealSheaf.Basic
supplies both the statement's notions and the proof. The removed module can still
be needed by other routes; this report makes no claim that it is globally unreachable.
The unit `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and has
no recorded proof steps: this change bypasses no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The old search record already identified Mathlib's vanishingIdeal and
coe_support_vanishingIdeal, but rejected them because IdealSheafData was not a
literal subsheaf. The subsequently accepted Lean statement explicitly represents
quasi-coherent ideal sheaves by IdealSheafData, so those declarations now give the
entire result. The stronger reduced-induced-closed-subscheme theorem is unnecessary.
The existing declaration docstring describes a valid longer argument and is retained.
Empty and full closed sets, including an empty ambient scheme, need no exceptions:
Mathlib's support equality applies to every element of Closeds Y. The witness is a
concrete Mathlib construction, not data chosen from an unproved existence theorem.

## Second reading by N1

1. PASS: Compared every delivered Lean module (one) with the repository by `diff -u`.
   The existing theorem signature, visibility, namespace, universes and docstrings are
   byte-for-byte unchanged. Only its proof and the unused plain proof import changed.
   No definitions, new declarations or change records are present.
2. PASS: Independently compiled the module with `lcompile.py`: exit 0, no warnings.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.exists_idealSheafData_support_eq`: exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. Inspected the entire file:
   no holes or forbidden declarations. Read Mathlib's `vanishingIdeal` construction:
   its data are affine prime-spectrum vanishing ideals, not an arbitrary witness of
   an unproved existence theorem.
3. PASS: No split-off statements or new nodes. The direct construction works for
   every closed subset, including empty and full subsets and the empty scheme.
   Mathlib identifies the support of the constructed ideal with the supplied closed
   set; no extra scheme hypothesis is required.
4. PASS: Independently searched Mathlib's ideal-sheaf API and the upstream and Sheaf
   sources for vanishing ideals and support identities. The two-term witness proof
   already takes the direct Mathlib route. The remaining public import supplies the
   signature's notions and the proof. The report lists the sole removed old
   proof dependency and its module completely. Checked `sk-thm-curveestimate`:
   its realized statement is `thm-sc-proper-cohomology`, with no realized steps;
   this tool-lemma simplification bypasses no unit statement or step.
5. PASS: Compared the delivered node with the repository. Only `proof`,
   `proof_deps` and `proof_origin` changed. The proof text names exactly the
   construction and equality used by Lean; no project proof dependency remains,
   and `proof_deps` equals the empty union of its step's `uses`. The Lean record
   still matches the unchanged theorem. No new node obligations arise.

Second reading changed only this report, adding the independent review and axiom
check results. The Lean proof and node needed no repairs.
