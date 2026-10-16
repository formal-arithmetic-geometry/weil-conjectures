## What changed

Proved `AlgebraicGeometry.Etale.exists_covering_supportedIn` from a new lower-level
section-vanishing theorem. The target now applies the existing kernel-lift lemma
`AlgebraicGeometry.Etale.exists_kernel_ι_app_eq` to the vanishing unit map. Added the
new split theorem `exists_covering_section_zero_off_closed` with its DAG node and imported
`WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` for the kernel-lift lemma.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.exists_covering_supportedIn`.

Sorry left: `AlgebraicGeometry.Etale.exists_covering_section_zero_off_closed`, node
`new-lem-sc-support-dimension-zero-off-closed`.

## No longer needed

The prior `new-lem-sc-support-dimension-closed-witness` split was withdrawn because it
restated the target. No imports were removed from the original module.

## Where the brief, the DAG or earlier work was wrong

The earlier split converted a closed witness directly into the target-shaped open witness,
so it was equivalent to the target and circular. The replacement split states only the
strictly simpler geometric vanishing assertion; the target's remaining step is a genuine
kernel universal-property application.

## New nodes

`new-lem-sc-support-dimension-zero-off-closed` records the geometric finite-type argument
for vanishing on the complement of a bounded-dimensional closed subset.

## Second reading by G2

1. **Signatures:** Compared the delivered module with the repository version. Existing
   declarations, including the target, are byte-for-byte unchanged; only the proof, its
   proof-only import, and the new split declaration were added.
2. **Proof:** Compiled the module with `lcompile.py`. The target has no `sorry`; the sole
   remaining `sorry` is the named lower theorem, with its source, proof description, and
   matching node. No forbidden declarations or hollow definitions were introduced.
3. **Statements:** Checked the lower theorem on empty-support and zero-section cases. Its
   conclusion is strictly weaker than the target: it gives only vanishing of the unit
   restriction, while the target additionally gives a section of the kernel. The theorem
   is not a restatement of the target, and its declaration agrees with its node.
4. **Pruning:** Searched the existing library and Mathlib for the geometric vanishing result
   and a shorter kernel argument. No duplicate vanishing theorem exists. The only new
   import is the plain proof import of `HighDegreeVanishing`, which supplies the existing
   kernel-lifting lemma; no removable imports or old proof dependencies were found.
5. **DAG and route:** The new node records source, proof route, dependencies, Lean
   declaration, and unit/chapter fields. The target applies the existing kernel universal
   property after the lower vanishing result, so the unit route is preserved.

**Changed:** accepted the target proof and the strictly simpler split theorem; added its
matching DAG node and proof-only import. No target statement or existing signature changed.
