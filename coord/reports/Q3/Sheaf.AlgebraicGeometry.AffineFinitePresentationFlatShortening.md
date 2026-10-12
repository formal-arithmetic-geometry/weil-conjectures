## What changed
The existing theorem `AlgebraicGeometry.Scheme.Modules.exists_affine_finitePresentation_flat_shortening`
keeps its signature and public imports byte for byte. Its proof now combines two strictly
smaller mathematical steps and derives universal pullback comparison directly from Mathlib.
Two new modules state the cancellation construction and bounded-above affine pseudo-coherence.
The first worker's unrestricted comparison module and node were removed before delivery.
No existing definition or statement changed; no change record or forced adaptation is needed.

## Proved and sorry left
Closed the body hole in `AlgebraicGeometry.Scheme.Modules.exists_affine_finitePresentation_flat_shortening`.
It remains dependent on the following two named open theorems added by this delivery:
- `AlgebraicGeometry.Scheme.Modules.affine_finitePresentation_flat_shortening_construction`
  (`lem-pc-affine-finite-presentation-flat-shortening-construction`).
- `AlgebraicGeometry.Scheme.Modules.affine_finitePresentation_flat_pseudoCoherent`
  (`lem-pc-affine-finite-presentation-flat-pseudo-coherent`).
This is a decomposition: one upper hole closed and two lower holes added, net -1 before
any pruning; it is not an unconditional proof of the item. No definition chooses data
from either open existence theorem. The existential witness is eliminated only inside
a proof of a proposition. Universal pullback comparison is proved with
`Functor.mapHomotopyEquiv` and `HomotopyEquiv.toHomologyIso`, with no additional hole.

## No longer needed
No repository module or original dependency is pruned. The original direct proof dependency
`lem-weil-pbc-affine-tilde-gamma-adjunction` is now used in the plans of the two lower lemmas;
it remains a transitive dependency. The never-delivered comparison module
`Sheaf.AlgebraicGeometry.AffineFinitePresentationFlatShorteningComparison` and its node
`lem-pc-affine-finite-presentation-flat-shortening-comparison` were discarded because
Mathlib proves the correct comparison from a homotopy equivalence. These are not counted
as pruned repository modules. All added imports in the item are plain proof imports.
The new lemmas privately import the affine tilde equivalence for their recorded proof plans.
Their public scheme/module import is only DirectImage.Basic; DirectImage.Sections is
unnecessary for their signatures and was removed from the proposed new modules.

## Where the brief, the DAG or earlier work was wrong
The first worker's `affine_finitePresentation_flat_shortening_comparison`
asserted identical homology for arbitrary B and D with no relationship between them.
For S = Spec(k), g = id, q = 0, B the complex k concentrated in degree zero and D the
zero complex, it would give 0 ≅ k. This is false for any nonzero field k.
The structural existence conclusion alone cannot link its witness D to B (zero D would
satisfy every structural conclusion). The repair carries a chain homotopy equivalence
out of the cancellation theorem, retains finite presentation, and proves pseudo-coherence
separately. The earlier docstrings had citations but lacked complete proofs in words;
the replacement docstrings give both arguments. The original item node also had not
been updated to describe the attempted reduction; its proof and dependencies now agree.
The affine equivalence dependency is available in Mathlib; the prior report's claim
that no compiled dependency was available was too broad.

## New nodes
`lem-pc-affine-finite-presentation-flat-shortening-construction` formalizes just the descending
split cancellation step, preserving finite presentation and a homotopy equivalence. It does
not assert pseudo-coherence or universal pullback comparisons.

`lem-pc-affine-finite-presentation-flat-pseudo-coherent` formalizes the separate finite
projective to bounded-above finite free representative argument (Stacks Tag 064U). It needs
neither residue-field vanishing nor a lower degree bound. Both inherit the item's unit and chapter. The repaired plans cite
`lem-weil-pbc-quasi-coherent-finite-type-affine` for affine section finite presentation and
`lem-weil-pbc-finitely-presented-flat-module-projective`, with the exact Mathlib match
`Module.Flat.projective_of_finitePresentation`, for finite projectivity. The construction plan
also records exact Mathlib declarations for Nakayama, localization detection, projective
splitting, and retract projectivity. Search logs are in the sandbox. No change records are required.

## Earlier second reading (a previous round; superseded)
1. Compared the complete item against the repository with diff. Its only changes are
   private proof imports and the proof body; the existing signature, visibility, definition
   dependencies and docstring are unchanged. There are no other existing delivered modules.
2. All three delivered modules compile locally without errors or warnings. Each of the two
   remaining sorries is the entire proof of a named public theorem with a complete source
   and natural-language proof docstring. There is no axiom, unsafe, opaque, implemented_by,
   extern or hollow definition. Scratch `#print axioms` checks record only propext,
   Classical.choice, Quot.sound and the two permitted outstanding holes via sorryAx.
3. Rejected the unrestricted comparison with the explicit field counterexample above.
   Checked the corrected lower statements: when b≤d the construction takes B itself;
   d=0 keeps a finite projective degree-zero term; the zero ring gives zero modules.
   Pseudo-coherence allows an unbounded negative tail, essential because projective
   complements need not be globally free. Cancellation preserves residue homology at
   each step via tensor preservation of homotopies. The exact finite-projectivity result was
   found and recorded as `Module.Flat.projective_of_finitePresentation` (node
   `lem-weil-pbc-finitely-presented-flat-module-projective`), and affine section finite
   presentation is recorded as `lem-weil-pbc-quasi-coherent-finite-type-affine`. The
   construction node also cites Mathlib’s exact Nakayama, localization-detection,
   projective-splitting, and retract-projective declarations; no single declaration supplies
   the entire cancellation argument.
4. Used the shortest comparison route: the existing Mathlib homotopy equivalence API.
   Construction and pseudo-coherence retain the original node's cancellation/complement
   route. Read dag/units/sk-thm-picard-coherence.json: realized is already empty; this
   item is a tool below the unit, not the unit's key theorem. No unit step or chapter
   route changed. No existing proof dependency became transitively unnecessary.
5. The item node now records the two applications followed by Mathlib comparison.
   The new nodes state exactly their Lean signatures, with genuine search records,
   source places, complete arguments, creation metadata and blueprint ancestry.
   The cancellation and complement steps remain non-elementary mathematical work;
   their Lean holes are explicitly reported, not presented as progress by hole count.

Changed on second reading: removed the false comparison; repaired construction to
return finite presentation and a homotopy equivalence; split pseudo-coherence separately;
proved comparison directly; replaced the new nodes' inaccurate descriptions and search
records; updated the item node and this report. This delivery remains a decomposition.

## Second reading by Q3
1. Diffed the item module against the repository: the existing theorem signature and
   visibility are byte-for-byte unchanged; only proof imports and its proof body differ.
   Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; no errors or warnings.
   The two remaining `sorry`s are named public theorem bodies, each with a source and
   complete natural-language proof docstring. No forbidden declarations or hollow
   definitions occur. Verdict: pass.
3. Checked both split statements against edge cases (b ≤ d, d = 0, zero ring) and the
   counterexample to the discarded unrestricted comparison. They are true and strictly
   narrower than the item, with matching DAG nodes and proof dependencies. Verdict: pass.
4. The item uses the shortest available comparison route, `Functor.mapHomotopyEquiv` and
   `HomotopyEquiv.toHomologyIso`; construction and pseudo-coherence retain the planned
   affine cancellation/complement route. The unit's `realized` route is unchanged.
   Verdict: pass.
5. Checked node proof steps, dependencies, origins, Lean records, and imports against
   the source. The item node matches the repaired proof and the two new nodes match their
   declarations. Verdict: pass.

No further changes were required by this second reading.
