## What changed

The existing declaration `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange`
has its signature byte for byte unchanged. Its proof obtains ordinary derived
base change from `proper_flat_rightAdjoint_baseChange_hβ`, then applies
`proper_flat_rightAdjoint_baseChange_global`, explicitly supplying the existing
`proper_flat_rightAdjoint_affine_baseChange` as the affine-case hypothesis.
The two new modules separate ordinary base change from restriction/descent.
The latter uses the existing restriction-open dependency. All new imports used
only for proofs are plain imports. No definitions or existing signatures change.

## Proved and sorry left

Closed: `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange` (1 original hole).
Added, still sorry:
- `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_hβ`, node
  `lem-sc-proper-flat-right-adjoint-basechange-hbeta` (ordinary derived base change).
- `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_global`, node
  `lem-sc-proper-flat-right-adjoint-basechange-global` (restriction/descent,
  with the affine-case theorem an explicit hypothesis).

This is a decomposition, not a complete proof: one hole closed, two added,
net minus one hole closed. The target still depends on sorryAx. No split-off
statement was closed during second reading. No data is chosen from a mere
existence theorem; hβ is a proposition-valued isomorphism certificate.

## No longer needed

Removed the direct proof-only import
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` from the item;
it is needed by the new restriction/descent module and remains imported there.
The old dependency `lem-sc-proper-flat-right-adjoint-restriction-open` is now
indirect through that module, while the old affine dependency is used explicitly.
No old proof dependency is unused in the overall argument; no module is pruned.
The item's direct proof_deps now name the two intermediate nodes and the affine node.
The fixed unit `sk-thm-picard-duality` and its realized record are unchanged.

## Where the brief, the DAG or earlier work was wrong

The initial intermediate nodes cited their parent as a statement dependency,
were not self-contained, and both claimed the affine right-adjoint theorem
proved their result. That theorem does not supply ordinary derived base change.
The parent node still described its old proof, rather than the delivered one.
The earlier global helper concealed the affine step; it now takes that theorem
explicitly, leaving only restriction and descent. The hβ helper had an
unnecessary existential/True wrapper, now removed.
The ordinary base-change argument is the specialization of
[Stacks Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D) to O_X[0], also
covered by [Tag 08IB](https://stacks.math.columbia.edu/tag/08IB).
The restriction/descent route follows
[Tag 0AAB](https://stacks.math.columbia.edu/tag/0AAB).

## New nodes

`lem-sc-proper-flat-right-adjoint-basechange-hbeta`, in
`lean/Sheaf/AlgebraicGeometry/ProperFlatRightAdjointBaseChangeHbeta.lean`:
ordinary derived base change, without right adjoints; its proof plan uses
`lem-pc-rf-base-change-complex` with the tensor unit and cancels invertible
comparisons. The docstring gives this full natural-language proof.

`lem-sc-proper-flat-right-adjoint-basechange-global`, in
`lean/Sheaf/AlgebraicGeometry/ProperFlatRightAdjointBaseChangeGlobal.lean`:
restriction/descent from the explicitly quantified affine-case hypothesis,
using `lem-sc-proper-flat-right-adjoint-restriction-open`. Its docstring explains
chart covers, compatibility of the canonical mate, and cohomology locality.
No change records are needed: both edited signatures are new declarations.

## Second reading by E2

1. Compared the delivered existing module with the read-only repository using
   diff. The sole existing declaration has exactly the original signature,
   visibility and mathematical conclusion. Only its proof and plain imports
   changed; no existing definition or target statement changed.
2. Compiled all three modules in import order with lcompile.py, without errors
   or warnings. Text inspection found precisely the two named theorem sorries
   listed above and no forbidden declarations or hollow definitions.
   A scratch copy with #print axioms for all three declarations compiled:
   each uses only propext, Classical.choice, Quot.sound and sorryAx.
3. Read the split statements and their cited sources. Ordinary base change
   follows from flatness/Tor independence for all quasi-coherent complexes,
   including unbounded E; properness supplies qcqs. Restriction/descent follows
   from Tag 0E4J and Remark 48.6.1, applying the explicit affine-case assumption.
   Identity base change, empty schemes, zero K and unbounded E introduce no
   extra conditions. The ordinary step has no right adjoints; the descent step
   does not prove the affine case, so neither restates the complete item.
   Ran fresh LeanFinder, Loogle and grep searches, and searched the current
   Lean library/upstream with Tor-independent, tensor and canonical-map terms.
   Existing perfect-tensor base change is affine with extra hypotheses; the
   relatively flat complex theorem still requires representative and tensor
   comparison data. Neither is a direct replacement for these two steps.
4. The item now actually applies the existing affine theorem. The restriction
   dependency is retained in the descent module. The ordinary step imports the
   relatively flat complex theorem. No further direct shortcut was found.
   All imports support signatures or the recorded proof route. No unit-level
   route is bypassed; no module is reported as pruned.
5. Checked and repaired each node's proof, proof_deps and proof_origin, the
   new nodes' self-contained statements, stmt_deps, source, search records and
   verbatim Lean signature records. Removed parent statement dependencies,
   avoiding a cycle, and verified the new proof-dependency unions.

Second reading changed the global helper to assume the affine theorem explicitly,
simplified the ordinary helper's conclusion, corrected both docstring proofs,
minimized/moved proof imports, repaired the three node records and replaced the
report's proof claim with explicit decomposition accounting.
