## What changed

Completed `AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section` in
`WeilConjectures.AlgebraicGeometry.Morphisms.Slicing`. The proof constructs the exact component
locus, proves its fibres connected using the fibre embedding and its image, restricts and
base-changes the section, and derives geometric irreducibility from geometric connectedness
and regular stalks. Added the proof-only import
`Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen` for the unresolved openness theorem.
The existing pointwise slicing and covering proofs remain in use.

## Proved and sorry left

Proved the original one remaining sorry,
`AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section`, from a strictly smaller
openness statement. Its node is
`lem-sbc-smooth-section-component-geometrically-irreducible`.
The item's module now has no direct sorry.

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.Smooth.isOpen_section_component`, node
`lem-sbc-smooth-section-component-open`, module
`Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen`.
This only asserts openness of the explicit component set: it does not assume or assert
geometric irreducibility, the containing open, or the original existential conclusion.

Both modules compile locally without warnings. The delivery tool also runs its axiom probe
and the server compilation. This is a reduction, not an axiom-free closure: the original
theorem still depends transitively on the new openness theorem and existing library inputs.

## No longer needed

None. No imports or existing proof nodes were removed. The unit's slicing and relative
connectedness route is preserved. The new openness module needs only Mathlib's smooth
morphism module; no extra Sheaf dependencies were imported.

## Where the brief, the DAG or earlier work was wrong

No node recorded this module or its remaining theorem: the blueprint slicing node had no
Lean attachment and an empty proof plan. Attached the existing covering declaration to
`sbc-lem-slicing` and recorded its actual relative-component dependency. The imported unit's
`realized` arrays are empty; this delivery does not change unit files.

LeanSearch returned HTTP Internal Server Error on both queries. The searches are recorded
as unavailable, not as evidence of absence. LeanFinder and source grep found no exact match.
Blueprint searches for connected component section and 055R returned no existing node.

The remaining openness statement agrees with Stacks 055R: smoothness supplies flatness and
geometrically reduced fibres, and quasi-compactness and quasi-separatedness supply finite
presentation. Edge cases checked: an empty base gives the empty open; an identity morphism
with its identity section gives the whole source; a disjoint union of smooth components
selects the component meeting the section fibrewise. No nonemptiness or connectedness of
the base is required. The section ensures nonempty selected fibres when a base point exists.

## New nodes

`lem-sbc-smooth-section-component-open`: the strictly smaller unresolved openness result,
stated alone in a new module, with source and natural-language proof in its docstring.
Its noetherian-descent and trait argument follows Stacks 055Q and 055R.

`lem-sbc-smooth-section-component-geometrically-irreducible`: records the existing theorem
whose proof this delivery completes. Its Lean proof supplies fibre connectedness, the
restricted section, geometric connectedness, and geometric irreducibility from openness.
It sits between `sbc-lem-slicing` and the openness node. No change record is needed because
all existing signatures and public imports are unchanged.

## Second reading by B3

1. Compared the complete Slicing module with the repository using `diff -u`.
   Every existing declaration signature, definition, docstring and public import is
   byte-for-byte unchanged. The only Lean differences are the original sorry's proof
   and the plain proof-only import of SmoothSectionComponentOpen. No change record
   is required; no target statement changes. Verdict: pass.
2. Compiled both delivered modules in import order with lcompile.py --all: no errors
   or warnings. Read every declaration and scanned the delivered Lean: the only sorry
   is the named public Smooth.isOpen_section_component, with no hollow definition or
   forbidden declaration mechanism. A temporary scratch copy with #print axioms for
   both the completed theorem and the openness theorem compiled; each printed exactly
   propext, Classical.choice, Quot.sound and sorryAx. Removed the scratch copy.
   This is a valid conditional reduction, not an axiom-free completion. Verdict: pass.
3. Read the openness statement, its node, and Stacks 055R and 055Q directly
   (https://stacks.math.columbia.edu/tag/055R and /055Q). Smoothness supplies flatness,
   local finite presentation and geometrically reduced fibres; quasi-compactness and
   quasi-separatedness supply finite presentation. The exact component locus is open
   under those hypotheses. Its docstring follows 055Q's noetherian descent, trait,
   special-fibre deletion and connected-generic-fibre argument. Checked empty base,
   identity section, and a disjoint union of smooth components: respectively empty,
   whole source, and precisely the components meeting the section. The lemma asks
   only openness, strictly less than the original existential geometric irreducibility
   result, and the real fibre/section/regular-stalk argument remains in Slicing.
   Repeated LeanFinder with different words (flat finitely presented geometrically
   reduced fibres connected components section open subset), and searched lean/Sheaf,
   lean/WeilConjectures and Mathlib's algebraic geometry sources. Found the affine
   variant AlgebraicGeometry.isOpen_setOf_mem_connectedComponentIn_preimage_singleton
   in WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat: it requires IsAffine
   source and base, and that module imports Slicing. Thus it neither directly proves
   the arbitrary-scheme statement nor can it be imported here without a cycle.
   No usable duplicate or quick closure was found. Verdict: pass.
4. Read the proof from its conclusion downward. U is the exact component set; the
   section identity puts its range in U and lets it lift. The fibre-image equality
   and embedding identify each fibre with the nonempty connected component. The
   base-changed lifted section proves geometric connectedness. Smooth field base
   changes are locally noetherian with regular local stalks, hence domain stalks;
   the existing irreducibility criterion completes the argument. Every new import
   is needed. The old sbc-lem-slicing proof_deps were empty, so No longer needed =
   none is complete. Read dag/units/sk-prop-normal-form.json: its realized arrays
   are empty upstream, but its normal-form and slicing/relative-connectedness route
   is preserved, with existing pointwise and covering proofs left untouched.
   No unit record is changed. Verdict: pass, with the upstream realized gap reported.
5. Read all three delivered JSON nodes against the Lean. The slicing node attaches
   the covering declaration and points to the relative-component step; that step
   points to openness and describes the actual fibre homeomorphism, section and
   regular-stalk proof. The openness node states exactly the Lean predicate and
   assumptions and provides the source proof, searches, provenance, chapter, unit
   and declaration record. No old dependency is silently pruned. Verdict: pass.

Changes by this second reading: added this substantive review and the repeated search
record. No Lean proof, signature, import or DAG node needed repair. The affine openness
variant and its import-cycle obstacle correct the first reader's search assessment;
the one unresolved general openness lemma remains explicitly listed above.
