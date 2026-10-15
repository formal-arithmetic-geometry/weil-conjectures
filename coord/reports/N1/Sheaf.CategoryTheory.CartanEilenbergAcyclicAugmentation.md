## What changed

Proved `CategoryTheory.exists_cartanEilenberg_acyclic_augmentation` in
`Sheaf.CategoryTheory.CartanEilenbergAcyclicAugmentation`, preserving its complete signature.
The augmentation is an explicit chain map, built from the mapped common augmentation and
the total inclusions. Seven proved private helpers construct the augmentation maps and handle
the cochain equation, the degree-zero component, naturality, the flipped total quasi-isomorphism
criterion, and the extension comparison component.

The quasi-isomorphism proof uses the source library's
`Functor.quasiIso_map_of_rightAcyclic_nat` on the existing column quasi-isomorphisms, then
`Functor.cartanEilenberg_augmentation_quasiIso`, transported through `totalFlipIso`.
Naturality follows directly from `Comparison.comm_e` and the extension comparison square.
The construction works in every integer degree, including negative degrees and zero columns.

Added proof imports `Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso`,
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`, and
`Mathlib.Algebra.Homology.TotalComplexSymmetry`. Updated the existing node's proof,
proof dependencies, and proof origin to follow this route. No public definitions,
interfaces, or other modules were changed. The second reader also removed the unused
public import `Mathlib.Algebra.Homology.Embedding.ExtendHomology`; all public signatures
still elaborate through the existing public presentation import.

Searches: LeanFinder for first-quadrant augmentation quasi-isomorphisms returned injective
resolution and extension lemmas; Loogle for `HomologicalComplex₂.total` returned the total
construction API; the launcher grep query for total quasi-isomorphism lemmas returned no
match. Direct searches of the source library found the acyclic quasi-isomorphism lemma and
the existing augmented-column total theorem used in the proof.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.exists_cartanEilenberg_acyclic_augmentation`
(node `lem-sp-ce-acyclic-augmentation`). One of one holes closed; zero holes added.
No `sorry` remains in the item module or in any helper. No new modules or split-offs.
Existing imported theorems retain their existing dependencies; this delivery does not claim
that the entire transitive axiom closure is sorry-free.

## No longer needed

Removed imports:
- `Mathlib.Algebra.Homology.Embedding.ExtendHomology` (second reading: unused direct
  public import; the presentation already exposes the extension and quasi-isomorphism API).
- `Sheaf.CategoryTheory.DoubleComplexTotal` (its required total API already comes through
  the public presentation import; its filtration constructions are unused here).
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` (its natural-indexed total and
  spectral-sequence support are unused here).

Removed direct proof dependencies:
- `thm-sp-double-complex-spectral-sequences`: the existing exact augmented-column total
  theorem supplies the cone/finite-filtration argument.
- `lem-sp-derived-well-defined`: no explicit right-derived-object/cohomology comparison
  is needed in this proof; acyclic quasi-isomorphism preservation supplies the mapped columns.

These are removals from this item's direct proof route, not claims that the nodes or their
modules are globally unreachable. No modules are withdrawn. The presentation and
composite-acyclicity definitions remain needed. The unit record has no realized statement
or proof-step nodes, and the construction follows the existing acyclic-column route.

## Where the brief, the DAG or earlier work was wrong

The DAG's spectral-sequence and derived-object computation steps were unnecessarily broad
for the existing library API. Both are replaced by already stated theorems, with no new
unproved intermediate statement. No mathematical error or interface correction was needed.

Validation: the inherited sandbox proof was read against the current presentation,
acyclicity, and augmented-total interfaces. A fresh `lcompile.py` compilation was clean
(10.2 seconds, exit code 0). The required
`deliver3.py N1 Sheaf.CategoryTheory.CartanEilenbergAcyclicAugmentation --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the independent second reading,
which the second reader writes. Nothing was pushed. No new axioms were reported by the
delivery probe.


## Second reading by N1

1. **Interface and scope: pass.** I compared the complete module and node with the
   read-only repository versions. The original theorem signature, including all hypotheses,
   universes, prescribed components, quasi-isomorphism clause and comparison equation, is
   byte-for-byte identical. No existing definition or docstring was changed. The seven new
   helpers are private and fully implemented; no other module is delivered. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and axioms: pass.** Fresh local single-file compilation succeeded without errors
   or warnings (11.4 seconds). A scratch copy with `#print axioms` for the public theorem
   and the three constructed maps compiled (10.6 seconds): every printed axiom set was
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. I also scanned
   the entire delivered module for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   `extern`, and kernel-check bypasses; none occurs. The augmentation is an explicit
   chain map, not a choice from an unproved existence theorem. I checked the total
   differential signs, the zero vertical composite, the inverse extension isomorphism,
   the mapped column acyclicity proof, the total flip component, and both naturality
   squares. Negative integer degrees and zero columns are covered by the same construction;
   the right-acyclic source proof treats vertical degree zero separately from zero terms.
3. **Split-offs and duplication: pass.** There are no split-off statements or new holes,
   hence no new node or docstring proof obligation. I independently searched Mathlib's
   total-complex and augmentation API through launcher grep (`augmentation|totalFlipIso`)
   and searched the upstream acyclicity and project Cartan--Eilenberg modules. No existing
   declaration supplies the entire construction and naturality conclusion. The proof uses
   the existing Leray preservation and augmented-total theorems rather than duplicating
   their arguments. I read their actual statements and the presentation's fields.
4. **Route and pruning: pass, one import repaired.** The column quasi-isomorphisms follow
   from `quasiIso_map_of_rightAcyclic_nat`; the existing augmented-column total theorem
   then applies after the total flip. This is a real reduction, not a renamed copy of the
   target. Both former direct proof dependencies absent from the proof are listed above.
   The unit `dag/units/sk-prop-av-pqf-finite.json` has empty realized statement/step lists;
   no realized unit step is bypassed. All three newly added imports are proof-only plain
   imports. I removed the unused public `Embedding.ExtendHomology` import after a scratch
   compilation without it succeeded (10.3 seconds). The other public imports are used by
   the unchanged signature. No global unreachability or whole-library pruning is claimed.
5. **DAG agreement: pass.** The node's four proof steps describe the explicit construction,
   mapped acyclic columns, total-flip reduction, and naturality as written. Its
   `proof_deps` is exactly the union of the steps' `uses`; all cited nodes exist, and
   `proof_origin` identifies the same source route. The retained total-complex definition
   dependency is still used through the public presentation module.

Second-reading changes: removed the unused public extension-homology import, documented
its removal in `coord/changes/N1-acyclic-augmentation-public-import.md`, and updated this report. No mathematical proof, statement, definition, or node repair was necessary.
One original hole closed, zero holes added, zero split-offs; this is a proof, not a decomposition.


The second-reader preflight required a change record for the removed public import.
The record lists every user from a fresh downstream audit and proves that the public
transitive import closure is preserved through the presentation import. The unchanged
direct importer also compiled against the revised module in an isolated scratch overlay.
No downstream file is adapted. The full-source-scan setting
`WEIL_DELIVERY_CACHE_DISABLE=1` was used because the optional shared cache caused a long
lock wait; all delivery checks remain enabled.
