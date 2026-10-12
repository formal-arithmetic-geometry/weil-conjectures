## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_enough_globallyGenerated`
without changing its signature, public imports, or any target. The proof follows
Stacks Tag 09NC (https://stacks.math.columbia.edu/tag/09NC), checked against its
statement and proof. Compactness gives a finite affine subcover. For nonempty X
one extra input factor makes the family positive; this avoids a separate empty
finite-family API. FiniteSectionsCover supplies nonvanishing choices in every
factor. At each point the distinguished section is used in one affine-cover
factor; TensorSectionAffineOpen then supplies its affine tensor locus. The
inverse right unitor transports its section to tensor power one. The empty
scheme uses the structure module and a vacuous pointwise condition.

Kept fully proved private helpers for restriction of top sections and finite
tensor invertibility. Repair of the dd0079fe1 return: removed the duplicate
`stalk_map_smul` and `nonvanishingLocus_iso` helpers. Added the proof-only
`import all Sheaf.AlgebraicGeometry.AmpleIso` and use its existing private
`nonvanishingLocus_iso` directly. Lean module imports support access to private
declarations with `import all`; no dependency module or visibility was changed.
Updated the item's proof docstring and DAG proof, proof dependencies and proof origin.
No new nodes.

Validation after repair: local single-file compilation is clean, and
`tools/import_prune_check.py` accepts the repaired module. All lines are at most 100
characters. The public interface comparison is unchanged. LeanFinder and Loogle
found no exact replacement; library and Mathlib text searches found no shorter
ample-existence theorem. The source's proved IsInvertible.tensorObj instance
replaces the unnecessary tensor-global-generation conclusion.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_enough_globallyGenerated`
(node `lem-sc-enough-globally-generated-ample`). No sorry remains in this module,
none is added elsewhere, and zero statements are split off.

This is a proof from existing stated dependencies, not a claim that its entire
axiom closure is finished. The proof uses
`AlgebraicGeometry.Scheme.Modules.finite_sections_cover_of_globally_generated`
(node `lem-sc-finite-sections-cover-qc`) and
`AlgebraicGeometry.Scheme.Modules.tensor_section_affine_open`
(node `lem-sc-tensor-section-affine-open`), which are existing downstream items.
The tensor-section construction also retains its existing naturality theorem
in PositiveTensorFamily. No arbitrary object is defined from an unproved
existence theorem: the module and tensor sections are genuine tensor
constructions, and existential choices occur only inside the theorem proof.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.TensorGloballyGenerated`: its node
  `lem-sc-tensor-globally-generated` is no longer a dependency of this proof.
  Product global generation and finite generating families are unnecessary;
  invertibility follows by induction using the proved tensorObj instance.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: tensor construction
  remains available through PositiveTensorFamily, so this direct import is redundant.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: available through the
  public Ample import; replaced its direct import by the proof-only
  `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` for tensor invertibility.

Removed duplicate local helper declarations `stalk_map_smul` and
`nonvanishingLocus_iso`; the AmpleIso versions are now reused.

Retained FiniteSectionsCover and TensorSectionAffineOpen. TensorProduct's
underlying definition node remains required through PositiveTensorFamily;
no claim is made that this entire module leaves the target closure. No other
planned node is bypassed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's stronger tensor global
generation lemma was more than this proof needed. The tensor-power-one
convention is not definitionally the original module: it is N tensor the unit.
The proof explicitly uses the right-unitor isomorphism and imports the existing
proof of preservation of the nonvanishing locus from AmpleIso. The earlier
delivery incorrectly assumed private helpers could not be imported; `import all`
provides the required access and avoids proving the same statements twice. The repository copy does not contain the ignored
Stacks TeX source, so Tag 09NC was read at the official Stacks page above.

The finite subcover may have zero factors only on an empty space; the proof
handles empty X separately and appends one genuine input factor for nonempty X.
The cases of an empty generating index, a one-factor cover, and a point in
only one distinguished affine locus are covered by the same argument.

## Second reading by J1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports, private helpers, the proof, and the matching DAG proof metadata differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is clean, has no `sorry`, and introduces no forbidden declarations. Scratch-copy `#print axioms` checks give only `propext`, `Classical.choice`, and `Quot.sound` for all three private helpers; the main theorem additionally has `sorryAx` from existing open dependencies, as reported above. Verdict: pass.
3. Checked the proof route and edge cases, including empty schemes, a one-factor cover, and an empty generating family. No new statements or split-off holes were added, and no duplicate theorem was introduced. Verdict: pass.
4. Checked pruning: the removed direct imports are proof-only redundancies, while the retained imports cover the declarations actually used. The DAG proof dependencies and origin match the implementation, and the unit route remains the finite-cover/tensor-section/affine-locus route. Verdict: pass.
5. Checked the node against the Lean theorem and the report against the implementation. The sole hole is closed, no holes are added, and the proof dependency update records the AmpleIso reuse and tensor invertibility route. Verdict: pass.

Changed during second reading: no further code or DAG changes; recorded the review above.
