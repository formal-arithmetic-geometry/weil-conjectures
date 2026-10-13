## What changed

Proved `AlgebraicGeometry.projective_class_reduced_splitting` in
`lean/Sheaf/AlgebraicGeometry/ProjectiveClassReducedSplitting.lean` without changing
its signature or public imports. Added proof-only imports of
`Mathlib.Algebra.Category.ModuleCat.Biproducts`,
`Mathlib.LinearAlgebra.TensorProduct.Quotient`, and
`Mathlib.CategoryTheory.Adjunction.Additive`; each is used.

Three proved private helpers establish surjectivity of the reduction unit, lifting
of reduced morphisms from projective modules, and reflection of isomorphisms for
class members. The main proof lifts the reduced retraction, corrects it by an
invertible endomorphism, then applies Mathlib's exact-sequence splitting API and
the class's summand condition. Updated the existing node's proof and proof_origin
to match this route. No other module, definition, or statement changed.

## Proved and sorry left

Closed the sole hole, `AlgebraicGeometry.projective_class_reduced_splitting`
(node `lem-sc-projective-class-reduced-splitting`). No holes remain, and none were
added. This is a complete proof, not a decomposition. All three private helpers
are proved; there are no new public declarations or new dependencies on project
statements with sorry. The single-file compilation passes without warnings.
`#print axioms AlgebraicGeometry.projective_class_reduced_splitting` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports were removed; all existing imports support the unchanged statement,
and all new imports are used in the proof. No existing node or module is pruned:
the old proof_deps were empty and the new proof_deps remain empty.

The plan's lifting of the reduced projection to the chosen last-object lift T,
its splitting, and its first intermediate kernel U are unnecessary. The shorter
argument lifts the reduced retraction to S.X1 instead, so only the kernel of an
endomorphism of S.X1 is needed. No separate modules for the discarded steps were
present. The isomorphism in hlast is not needed; its class-member witness is used
only to establish that zero is in the class. In fact hfirst alone also gives this,
so hlast is logically redundant, but its binder and type remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The DAG's route was longer
than necessary; its kernel-vanishing argument applies directly to an endomorphism
obtained by lifting the reduced retraction. The unit's fixed route is preserved:
this is a lower-level auxiliary node, and the unit's realized statement and steps
are untouched. The original theorem docstring still records the valid source
plan; the delivered node and proof-body comment record the shorter implementation.

Checked the source's final paragraph at https://stacks.math.columbia.edu/tag/0BCA;
the cited local literature file is not present on this machine. The source
hypotheses used here are exactly projectivity, the sums-and-summands condition,
and reflection of reduced surjections. No finiteness or proper-ideal assumption
was introduced. For I = 0 reduction is identity and the argument still applies.
For I = R the surjectivity hypothesis forces every class member to be zero, so
the proof remains valid; an empty class is excluded by hfirst. Zero first and
middle objects are also covered by the categorical splitting and zero-object API.

Lean Finder found the generic projective lifting APIs; Loogle found quotient and
tensor surjectivity tools, but no exact reduced-splitting theorem. Grep found no
matching theorem in the project. The complete proof uses Mathlib's adjunction,
quotient tensor equivalence, projective lifting, kernels, and splitting lemmas.

## Second reading by M4

1. PASS: Compared the sole delivered module and existing node with the read-only
   repository using diff. Programmatically checked that the existing theorem's
   complete signature before `:=` is byte-for-byte identical. Its docstring,
   public imports, visibility, hypotheses and conclusion are unchanged. Only
   proof-only imports, proved private helpers, and the proof body were added.
   The node changes only proof and proof_origin; no change record is needed.
2. PASS: Independently compiled the delivered file using lcompile.py (2.6 s,
   no errors or warnings). A scratch copy with #print axioms for the main theorem
   and all three private helpers reports only propext, Classical.choice and
   Quot.sound. No sorry, forbidden declaration, definition or data construction
   was added. The section and factorization choices use proved projectivity;
   the inverse is taken only after a proved IsIso instance.
3. PASS: No statements were split off and no holes were added. Read all three
   private helper proofs: the quotient unit is surjective, projectivity lifts
   reduced morphisms, and a split kernel with zero reduction vanishes by hsurj.
   Checked zero objects, I = 0, I = top, and the empty-class case (excluded by
   hfirst). Independent Lean Finder, Loogle and Mathlib grep searches found
   projective factorization APIs already used here, but no theorem replacing
   the class-specific reflection argument. The related StablyFreeModuleLift
   helper is private and uses the same quotient construction, not a reusable
   public declaration; its public theorem has finiteness and Jacobson hypotheses
   absent here. Mathlib's faithfully-flat reflection theorem does not apply to
   an arbitrary quotient.
4. PASS: Read the proof from the target downward and checked the final paragraph
   of [Stacks Tag 0BCA](https://stacks.math.columbia.edu/tag/0BCA). Directly lifting
   the retraction is a valid shorter implementation of its kernel-vanishing
   argument. Independently removed each new proof import in a scratch copy;
   each removal fails on the declaration that import supplies. Existing public
   imports support the preserved interface. Old proof_deps is empty, so the
   No longer needed section omits no old node. Read dag/units/sk-prop-av-cube.json:
   this auxiliary node realizes no fixed unit statement or step; the unit route
   and its existing empty realized lists are untouched.
5. PASS: Checked every delivered node proof step against the Lean construction.
   The seven steps accurately describe zero membership, quotient surjectivity,
   projective lifting, split-kernel membership, kernel vanishing, retraction
   lifting, and exact splitting. proof_deps stays empty because all supporting
   declarations are Mathlib or proved private helpers; proof_origin correctly
   identifies the shorter route as agent-written. No new node needs validation.

Second reading changed only this report by adding the independent review and
validation evidence. No Lean or DAG repair was necessary. Closed hole:
AlgebraicGeometry.projective_class_reduced_splitting; added holes: none.
