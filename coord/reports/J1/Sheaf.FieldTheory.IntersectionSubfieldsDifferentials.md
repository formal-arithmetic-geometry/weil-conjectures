## What changed
Repaired the earlier attempt's node signature records: `lean.statement` now matches the complete theorem signature, including the declaration name,
as preflight expects. The unchanged
main statement is reduced by conjunction introduction to its two proper clauses. Added
complete source proof docstrings and copied the original numbered proof steps into each
new node. Updated the parent node to match the conjunction proof.

## Proved and sorry left
Closed `FieldTheory.intersection_subfields_differentials` (one original hole) by decomposition,
not a completed mathematical proof. Added two holes:
- `FieldTheory.intersection_subfields_differentials_kernel`, node
  `lem-weil-pbc-intersection-subfields-differentials-kernel` (original steps 1–2).
- `FieldTheory.intersection_subfields_differentials_powers`, node
  `lem-weil-pbc-intersection-subfields-differentials-powers` (original steps 3–5).
The original universes, hypotheses and conjunction remain unchanged. No definitions contain holes.

## No longer needed
Removed the main module's proof imports `Sheaf.FieldTheory.ExistsPBasis`,
`Sheaf.FieldTheory.IntersectionSubfieldsSubspace`, `Sheaf.FieldTheory.PBasisDifferentialsBasis`
and `Sheaf.FieldTheory.PIndependentDifferentialsIndependent`: conjunction introduction uses
only the two new modules. Their underlying nodes remain needed in the kernel clause's plan;
no mathematical branch is pruned globally. The second reading restored those four imports
as plain proof-plan imports in the open kernel module. The powers module now imports
Mathlib.FieldTheory.IntermediateField.Adjoin.Basic and Mathlib.LinearAlgebra.Dimension.Free
for its power-basis and tower-degree plan; its public finite-dimensional import is reduced
to Mathlib.LinearAlgebra.FiniteDimensional.Defs. All old proof dependencies remain in the
new clauses' source plans; none is globally pruned.

## Where the brief, the DAG or earlier work was wrong
The retained report contradicted itself about whether `lean.statement` includes the theorem
name. The current records include the full declaration signature and pass preflight.
Removed obsolete second-reading text: the independent second reader must write that section.
The previous import-source validation failure has been repaired externally. In this retry,
all three modules compile with `lcompile.py --all` (exit code 0), and `deliver3.py --no-push`
prints OK, passing preflight except for the independent second reading. No tool was edited
and nothing was pushed.

## New nodes
`lem-weil-pbc-intersection-subfields-differentials-kernel` isolates the first clause with
original steps 1–2. `lem-weil-pbc-intersection-subfields-differentials-powers` isolates the
second clause with original steps 3–5. Both are strictly proper parts of the conjunction,
retain the unit route, and use the existing source and search records. For an empty index
family the intersection hypothesis makes K perfect; the source proofs include this case
(the kernel argument derives nonemptiness only after assuming a nonzero differential).

## Second reading by J1

1. **Visible interface: pass.** Read the diff against the repository module. The entire
   existing theorem signature, including universes, all three hypotheses, and both
   conclusions, is byte-identical. The local prime-field instance and all existing
   docstrings are unchanged. Only proof imports and the conjunction proof changed in
   the existing module; no change record is needed. The new clauses introduce no data
   definitions and select no witnesses from unproved existence assertions.
2. **Kernel check: pass as a decomposition.** All three modules compile locally using
   lcompile.py in dependency order. Only the two reported public, named clause theorems
   have sorry; each proof is exactly `by sorry`. There are no forbidden declarations or
   implementation escapes. Scratch copies with `#print axioms` for each theorem show
   only propext, Classical.choice, Quot.sound and sorryAx in all three declarations. Thus this is not a completed
   proof: one original hole is closed syntactically and two simpler holes are added,
   net minus one. Neither clause could be closed in a few minutes from existing APIs.
3. **Split clauses: pass after metadata repair.** Read both clause modules and every
   new node in full; compared their hypotheses and conclusions with
   [Stacks Tag 07P4](https://stacks.math.columbia.edu/tag/07P4), label
   `lemma-intersection-subfields`. Each is exactly one proper clause, with the same
   prime characteristic, arbitrary index type, Frobenius containment, intersection,
   and downward directedness hypotheses. Neither restates the entire item. Made both
   natural-language node statements self-contained instead of referring to the parent.
   Kernel steps use Field.exists_p_basis, the differential basis theorem, the
   p-independent differential theorem (contrapositive), and the subspace-intersection
   theorem after rebasing to the Frobenius subfield. Nonemptiness follows under the
   nonzero-differential contradiction, as the docstring explains. Powers steps use
   tower-degree induction and the simple-extension power basis. Checked the coefficient
   argument when t belongs to some Kα: the span need not be direct; a directed refinement
   inside the distinguished Kα₀ gives coefficient uniqueness, which is valid.

   Edge cases: an empty family forces K=K^p; its differentials vanish since every
   element is a p-th power. A finite extension of a perfect field is perfect, so the
   empty intersection in L is L=L^p. For a singleton the sole field is K^p and both
   clauses reduce to the expected Frobenius-field statements. Degree-one extensions
   give h₂. Checked p=2 and the example K=F₂(s,u), t=s: adjoining t to a field already
   containing t gives a one-dimensional span, precisely why the retained directedness
   correction is needed. No additional nonemptiness assumption is inserted.

   Searched both lean/ and the upstream WeilConjectures sources with intersection,
   power, perfectness and differential keywords; no duplicate of either clause.
   Independently ran msearch leanfinder, loogle, and grep with different queries.
   LeanFinder's differential-field hits assume characteristic zero and its perfect-
   closure intersection concerns different objects. Loogle and the targeted grep
   searches returned no hits. LeanSearch was unavailable (HTTP 500), recorded as such.
   Replaced inherited searches in both new nodes with these actual logged searches.
4. **Route and pruning: pass after imports repair.** The proof introduces the conjunction
   directly. The four former Sheaf imports are unnecessary in that outer module but
   remain needed by the kernel plan, so they now appear as plain imports there.
   Restored the Mathlib power-basis/tower-degree proof imports in the powers module;
   narrowed its public finite-dimensional import to the definitions its signature needs.
   There are no proof-only public imports. No original dependency is claimed globally
   unnecessary, and no module is globally pruned. Read dag/units/sk-thm-p1.json:
   the item lies below its realized nodes, and the five original source-plan steps
   remain assigned to kernel (1–2) and powers (3–5); no unit step is bypassed.
5. **DAG consistency: pass after metadata repair.** Verified all three recorded Lean
   signatures against the files, and each proof_deps equals the union of its step uses.
   Parent proof/origin describe conjunction introduction; clause proofs/origins retain
   the source argument. New nodes have source, status, provenance, chapter/unit,
   blueprint.from, statement dependencies and complete Lean records. Removed the
   powers node's irrelevant differential statement dependency and the kernel node's
   irrelevant finite-extension statement dependency. Existing node edits are confined
   to lean, proof, proof_deps and proof_origin. No definition or existing statement changed.

Changes by this second reader: self-contained new-node statements; real search records;
precise statement dependencies; restored clause proof-plan imports; narrower public
finite-dimensional import; module-docstring blueprint markers; this review and corrected
pruning account. The mathematical conjunction proof and all theorem signatures were retained.
