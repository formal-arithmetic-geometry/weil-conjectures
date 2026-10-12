## What changed

The statement of AlgebraicGeometry.affine_picard_torsion_base_change is unchanged.
Its proof now chooses a smooth proper compactification, proves its boundary nonempty,
applies pic_affine_base_change_compatibility, and restricts the supplied canonical
Picard comparison to the degree-zero groups. The existing
Scheme.Hom.pic_proper_ntorsion_div supplies divisibility. The new
AlgebraicGeometry.picZero_torsion_base_change isolates the proper-curve point
comparison (injectivity and lifting of prime-to-characteristic torsion).

The private, fully proved quotient_torsion_comparison lemma carries out the
representative argument: kernel lifting and point injectivity prove quotient
injectivity; divisibility and torsion lifting correct a representative and prove
surjectivity. The final proof explicitly transports the canonical pullback along
hπ.isoPullback and checks the map equals Pic.map π by functoriality.

New proof imports: Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange,
Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv,
WeilConjectures.AlgebraicGeometry.Regular, and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper. Existing public imports
are unchanged. Both modules compile cleanly via lcompile.py --all.

## Proved and sorry left

Closed in the assigned module: AlgebraicGeometry.affine_picard_torsion_base_change
(lem-sc-affine-picard-torsion-base-change), one of one original holes.
The private quotient_torsion_comparison is fully proved and contains no hole.
No sorry remains in the assigned module.

Added: AlgebraicGeometry.picZero_torsion_base_change
(lem-sc-piczero-torsion-base-change), exactly one named public theorem in a new module,
with proof exactly := by sorry. This is a decomposition, not a net reduction of holes:
one upper hole closed, one strictly smaller proper-curve point-comparison hole added.
The affine boundary argument, quotient argument, and arbitrary-square transport are
actual Lean proofs in the assigned module. The new theorem has no affine quotient,
boundary subgroup, or arbitrary pullback square in its statement.

The proof also uses the existing hole
AlgebraicGeometry.pic_affine_base_change_compatibility
(lem-sc-pic-affine-base-change-compatibility); this delivery does not add or change it.
Degree-zero divisibility is supplied by an existing proved declaration.

## No longer needed

Removed direct imports from the assigned module:
- WeilConjectures.AlgebraicGeometry.Picard.Jacobian
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
- WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
- Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

lem-sc-divisible-quotient-torsion and its module
WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic are not needed for the
representative quotient argument: the full short exact sequence is unnecessary.
lem-sc-pic-affine-quotient and its module
Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient are not needed here: the boundary
nonemptiness argument is written directly, and the compatible quotient presentations
come from PicAffineBaseChangeCompatibility. The boundary nonemptiness argument still
uses lem-sc-proper-affine-finite. def-sc-field-extension remains a statement dependency, but its recorded Lean declaration
Etale.cohomologyMap is not used in the proof and is removed from proof_deps.
lem-sc-curve-base-change-relative-dimension-one is also unnecessary here: the
Mathlib base-change instance preserves the already established relative dimension one.
Its module Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne is not imported
or used by this proof. TopologicalInvariance is unnecessary for this proof.

thm-sc-jacobian-representability and thm-av-final are no longer direct dependencies
of this node; they are still needed below it, through the proper-curve comparison and
the existing divisibility declaration. Likewise some removed modules may remain
transitively imported elsewhere. No claim is made that these globally leave the
whole target import closure.

## Where the brief, the DAG or earlier work was wrong

The compatibility theorem's unparenthesized universal quantifiers absorb later
conjuncts: the later boundary equivalence and compatibility equations must be extracted
by evaluating preceding universal quantifiers at the identity elements. The delivered
proof does this without changing the compatibility theorem's signature.

The assigned DAG's full divisible-quotient-torsion sequence is stronger than needed;
the representative argument is sufficient and has been fully formalized. Its boundary
nonemptiness argument does not require choosing a Jacobian first.

The clone does not contain the cited blueprint Markdown files. The full unit text and
proof paragraphs are available in dag/units/sk-prop-ext-invariance.json and the existing
node files, and were read. An attempt to obtain the cited Markdown at its pinned public
GitHub URL returned HTTP 404. The new node's proof_origin explicitly records S1's
expansion of the supplied argument; the source sentence and route are unchanged.

Edge cases checked: n=1 has singleton torsion types; genus zero has trivial Pic-zero;
the identity extension gives the identity comparison; positive-characteristic n
vanishing in k is excluded by hn; properness is necessary for the new comparison.
The compactification boundary cannot be empty in the assigned affine dimension-one case.
The generic quotient proof also works for trivial groups and arbitrary kernel subgroups.

## New nodes

lem-sc-piczero-torsion-base-change, in
lean/Sheaf/AlgebraicGeometry/Curve/PicZeroTorsionBaseChange.lean, isolates exactly the
proper-curve Jacobian point comparison needed to apply the fully proved quotient
argument. Its docstring and DAG give the geometric hypotheses, canonical comparison,
injectivity argument using residue-field maps, and lifting through finite etale
Jacobian torsion. Existing Jacobian representation, Jacobian base-change compatibility,
and the abelian-variety estimate are its inputs; no duplicate definition was introduced.
Blueprint searches for Picard and Jacobian found these existing inputs, but no node
stating this precise proper-curve point-map conclusion. LeanSearch returned HTTP 500;
LeanFinder found only Weierstrass special cases; the scoped Mathlib grep found no match.
The searches were actually run and are recorded in searches.jsonl.


## Second reading by S1

1. Interface: compared the full assigned module with the repository using diff and
   checked the existing theorem signature byte for byte, including the proof terms
   constructing the torsion subtype. It is identical. Existing public imports are
   unchanged; the added imports are private proof imports. No definition, target,
   hypothesis, or conclusion changes, and no change record is needed. Verdict: pass.

2. Kernel checks: both delivered modules compiled cleanly through lcompile.py --all.
   Scratch copies with #print axioms showed propext, Classical.choice, Quot.sound,
   and sorryAx for the assigned theorem and the new open theorem; the private
   quotient_torsion_comparison uses only the three standard axioms. Inspected every
   declaration: the sole delivered sorry is the complete proof of the named public
   picZero_torsion_base_change theorem. No axioms, unsafe/opaque declarations,
   implementation escapes, or hollow definitions were added. Local choices of
   representatives and quotient presentations occur only within a theorem proof;
   no arbitrary existence witness is exported as data. Verdict: pass.

3. Split statement: matched G and G' to the degree-zero subgroups using hG and hG',
   and matched j to canonical pullback using hj. The proper, smooth, connected
   hypotheses are exactly those needed for the Jacobian comparison. Nonzero n in k
   entails n > 0 and invertibility in k. Checked n=1, genus zero, identity extensions,
   and the exclusion of n=0; no counterexample arises. This is strictly a part of the
   argument, with no affine quotient or boundary hypotheses. Its source, complete
   docstring proof, and new DAG node are present. Repeated LeanFinder search with
   "faithfully flat extension injectivity line bundles and finite etale Jacobian
   torsion rational points" and searched lean/ with injectivity, Picard pullback,
   and torsion synonyms: only elliptic special cases, the existing proper torsion
   cardinality calculation, and Scheme.SpecMap_comp_injective were found. The latter
   is already cited in the new node's proof. Read the Jacobian compatibility theorem
   and both clauses of the upstream abelian-variety estimate; they justify the
   planned canonical comparison. Closing the remaining geometric comparison needs
   substantial representing-functor transport, rather than a few-minute proof.
   Verdict: true, needed, nonduplicate, and honestly reported as a decomposition.

4. Route and pruning: checked the quotient helper's kernel-lifting argument and its
   correction of a lifted torsion representative, and checked both inverse equations
   in the arbitrary-pullback transport. The compactification boundary contradiction
   uses proper-affine finiteness and dimension one. Read the unit's affine paragraph:
   compactification, degree-zero Jacobian injectivity, divisibility, and torsion
   correction are retained. The unit's realized arrays are empty in the repository;
   this delivery changes no unit or chapter route. No shorter established theorem
   supplies the canonical proper Picard comparison. Every removed old proof_deps
   entry is listed under No longer needed, with direct versus transitive use
   distinguished. Verdict: pass after the dependency corrections below.

5. DAG: read both delivered nodes and checked their statements, Lean records,
   proof steps, union of uses, proof_origin, chapter/unit, creation and source fields.
   Corrected the assigned node's false citation of
   lem-sc-curve-base-change-relative-dimension-one: the Lean uses Mathlib's instance
   for base change of an already smooth relative-dimension-one map. Removed
   def-sc-field-extension from both proof_deps, since its attached Etale.cohomologyMap
   declaration is not used; it remains a statement dependency. The corresponding
   injectivity step is elementary and cites Scheme.SpecMap_comp_injective in words.
   Changed the assigned proof's regularity consequence to IsRegular.isIntegral,
   exactly the declaration of lem-sc-regular-connected-integral; irreducibility is
   then inferred. Verdict: pass after repair.

Second reading changed the regularity proof line, corrected the unused DAG proof
citations, updated the pruning report, and added this review. It closed no further
hole and added no hole: one of one original holes closed, one proper-comparison
hole added, net zero. No statements or definitions were changed.
