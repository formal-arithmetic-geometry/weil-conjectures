## What changed

Replaced the whole proof of `AlgebraicGeometry.Smooth.isOpen_section_component` by a
complete Lean combination of two strictly separate algebraic facts: local constructibility
and stability under generalization. On an affine chart, local constructibility becomes
constructibility; Mathlib's spectrum criterion makes the pullback open. The chart's open
immersion maps it to an open neighbourhood contained in the component locus. The original
signature and docstring are unchanged. Added two proof-only imports and the proof-only
Mathlib spectrum criterion import; updated the item's DAG proof and dependencies.

All three modules compile with `lcompile.py --all`. No definitions or existing statements
were changed. The original unit's relative-component step is preserved.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Smooth.isOpen_section_component`
(node `lem-sbc-smooth-section-component-open`). This is a decomposition, not a complete
axiom-free proof of the underlying algebraic geometry: two new holes remain, each in its
own module, with an entire named theorem proof and a source/proof docstring:

- `AlgebraicGeometry.isLocallyConstructible_section_component`, node
  `lem-sbc-section-component-locally-constructible`, module
  `Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible` (Stacks 055P).
- `AlgebraicGeometry.Smooth.stableUnderGeneralization_section_component`, node
  `lem-sbc-smooth-section-component-generalization`, module
  `Sheaf.AlgebraicGeometry.SmoothSectionComponentGeneralization` (the generic-point
  argument in Stacks 055Q).

The first theorem allows arbitrary locally finitely presented qcqs morphisms, with no
smoothness or flatness requirement. The second only asserts generalization stability.
Neither is the original openness theorem under a new name. Their combination is the
nontrivial affine-chart and neighbourhood proof in the original module.

Edge cases checked mathematically against the sources: for an identity morphism the
locus is the whole scheme; for the empty scheme it is empty; for a disjoint union of two
copies of the base and the section into one copy it is that clopen copy. The base need
not be quasi-compact or quasi-separated: both conclusions and the final proof are local,
and only the morphism has the qcqs hypotheses. Generalization stability alone does not
imply openness, nor does local constructibility alone. Both parts are needed.

## No longer needed

Removed the redundant explicit `Mathlib.Topology.Constructible` import from the new
local-constructibility module; `FinitePresentation` already exposes its declarations.
No original import, node or module is pruned: the original file imported only
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, needed by its unchanged statement, and its
node had no proof dependencies. During proof development an explicit
`Mathlib.AlgebraicGeometry.Cover.Open` import was tested and removed as redundant.
The new generalization module does not import `Mathlib.Topology.Constructible`.
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` is not imported: its theorem is
for affine source and target only and importing it here would create a cycle. The source
ring-theoretic relative-component modules are not used in this combination; no claim is
made that they are globally pruned, since the two algebraic subitems may need them later.

## Where the brief, the DAG or earlier work was wrong

The original DAG has two substantial non-elementary proof steps with empty `uses` and
no proof dependencies. Thus there are no stated plan dependencies to apply directly.
The source library's affine relative-component openness result cannot fill the original
global statement directly, and `import_direction.py may` explicitly rejects its import
because SlicingFlat reaches this item through Slicing. The delivery makes the missing
algebraic steps into separate parallel items instead of using a circular import.
LeanSearch was attempted for both new statements and returned Internal Server Error;
Lean Finder/Loogle and direct library/DAG/Mathlib searches were available.

## New nodes

`lem-sbc-section-component-locally-constructible` states Stacks 055P in a new module
`lean/Sheaf/AlgebraicGeometry/SectionComponentLocallyConstructible.lean`, with the
noetherian descent and constructibility proof in its docstring and node.

`lem-sbc-smooth-section-component-generalization` states the generic-point step of
Stacks 055Q in a new module
`lean/Sheaf/AlgebraicGeometry/SmoothSectionComponentGeneralization.lean`, with its trait
and connectedness proof in the docstring and node. Whole-DAG and blueprint searches
found no matching global statements. No change record is needed: no existing interface
changed, and the added imports in the original module are proof-only.


## Second reading by Q3

1. **Interfaces unchanged — pass.** Diffed the existing Lean module against the repository:
   the signature and existing docstring are byte-for-byte unchanged. The only changes are
   its proof and three proof-only imports. Both additional modules are new; no definition,
   target statement, or existing interface changes, and no change record is required.
2. **Proof and axioms — pass as a decomposition.** Recompiled all three modules locally
   without errors or warnings. Scratch `#print axioms` checks found only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. There are exactly two
   remaining holes, the two named new theorems listed above; no prohibited declarations
   or hollow definitions occur. The existing theorem's affine neighbourhood argument is
   a genuine combination of two separate facts, not a renamed application of openness.
3. **Split statements — pass.** Read Stacks 055P, 055Q and 055J directly. Finite
   presentation is supplied by the local finite presentation and qcqs assumptions;
   smoothness supplies flatness and geometrically reduced fibres. The fibre subspace
   matches the underlying topological scheme fibre, and the rational section component
   commutes with base change (055M). Tested identity, empty, and two-copy cases and
   arbitrary non-qcqs bases. Additional Lean Finder, Loogle and Mathlib grep searches
   with different queries found no matching global result. Read the source library's
   affine generalization/openness proofs: they require affine source and target and
   importing their module here would cycle through Slicing. Neither new algebraic
   statement can be closed in a few minutes from the available global declarations.
4. **Route and pruning — pass.** Read the entire target proof and the original DAG plan.
   Mathlib supplies the affine constructible/generalization criterion, and the proof
   maps its open preimages to neighbourhoods by the affine-cover open immersions.
   Each proof-only import is used. Removed one redundant explicit public import from
   the new constructibility module and recompiled. The old proof_deps list is empty,
   so there are no old nodes to mark unused. Read dag/units/sk-prop-normal-form.json:
   its second step still uses the open relative component in slicing; its currently
   empty realized arrays are unchanged, and no unit step is bypassed.
5. **DAG alignment — pass.** Compared the existing node: only proof, proof_deps and
   proof_origin change. The two dependencies are precisely the named new theorems;
   their nodes record their exact statements, source, complete informal proof, searches,
   split status, creation metadata, blueprint origin, chapter, unit, and Lean records.
   No change to the existing node's statement or statement dependencies occurs.

Second reading changed the new local-constructibility docstring and its matching node
proof: for a nonempty open W of an irreducible Z, the locus meets W in either nothing
or all of W; its intersection with Z need only be non-dense in the first case, not empty.
This repairs the informal argument without changing either new theorem's signature.
Removed the redundant explicit topology import. The net hole change remains one closed
and two added (net minus one); this delivery is a decomposition, not an axiom-free proof.
