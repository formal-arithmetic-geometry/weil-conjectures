## What changed

`PrincipalThickeningSingleLift.lean` replaces the proof of
`AlgebraicGeometry.Scheme.principal_thickening_single_lift` with a two-part
reduction. The theorem signature and the complete definition of
`principalThickeningCanonical` remain byte for byte unchanged. Private helpers
construct the consecutive transition morphism and prove its ambient-map and
canonical-section identities. A plain proof-only import supplies the new
`PrincipalThickeningIdealFactor.lean`, which uses the image-ideal definitions in
`PrincipalThickeningObstruction.lean`.

The theorem applies the natural boundary sequence, factors the map of image
ideals through O_W, and uses the assumed subsingleton H^1(W,O_W) to kill the
boundary. No public import or top-level open command of an existing module changes. No statement or
existing definition changes, so no interface change record is needed.

## Proved and sorry left

Closed one existing hole, by declaration name:
`AlgebraicGeometry.Scheme.principal_thickening_single_lift`.

Added two named holes, each in its own new module, with a complete proof in
words and a matching node:

- `AlgebraicGeometry.Scheme.principal_thickening_obstruction`
  (`new-principal-thickening-obstruction`).
- `AlgebraicGeometry.Scheme.principal_thickening_ideal_factor`
  (`new-principal-thickening-ideal-factor`).

This is a decomposition, not a completed proof of the mathematical item.
The local hole count changes from one to two (net holes closed minus added is
-1); the import-closure ledger remains the authoritative progress measurement.
The item module has no sorry. The two new modules have exactly the listed
named theorem sorries and no others. All definitions are real constructions.
The boundary and factor witnesses are destructured only in a theorem proof;
no data definition chooses an arbitrary witness from an unproved existence.

## No longer needed

None of the repository's old proof dependencies or imports is pruned: the
repository node had an empty proof_deps list. No library module is made
unreachable by this delivery. The abandoned sandbox-only fixed-level core
is absent and is not counted as pruning. The second reader removed the
redundant new-module import `Mathlib.CategoryTheory.Abelian.Images`.

## Where the brief, the DAG or earlier work was wrong

The earlier fixed-level core merely restated the entire item and was removed
before this reading. Its stale reference was still present in the sandbox
item node; the second reader replaced it with the actual obstruction and
ideal-factor proof steps and dependencies.

The original report incorrectly called the item proved without identifying
this as a decomposition. It also implied that the abandoned core counted as
pruning and supplied an interface change record for a private proof import.
Those claims and that record have been removed.

The ideal-factor docstring's denominator-clearing sentence needed a distinct
multiplier outside the prime, not the fraction's denominator. The corrected
argument applies hkill to t*r. The obstruction docstring cited Tag 01EA as the
long exact cohomology sequence; that tag concerns flasque injectives. It now
cites [Stacks 01DZ](https://stacks.math.columbia.edu/tag/01DZ), Section 20.2,
for cohomology as a universal delta-functor. The factorization was checked
against [Stacks 0H3D](https://stacks.math.columbia.edu/tag/0H3D), and its
quotient-sheaf application against
[Stacks 0H3E](https://stacks.math.columbia.edu/tag/0H3E).

## New nodes

`new-principal-thickening-obstruction` states exactness at the section boundary
and its naturality for every commuting ideal/scheme map. Its Lean statement
is in `PrincipalThickeningObstruction.lean`. The node spells out the quotient
identification and the long exact sequence argument.

`new-principal-thickening-ideal-factor` states the factorization of the higher
image-ideal inclusion through multiplication at the lower level. Its Lean
statement is in `PrincipalThickeningIdealFactor.lean`. The node spells out
localization of the torsion bound and categorical descent. Neither statement
is the target under a new name. No change records are delivered.

## Second reading by T1

1. Compared the existing item module with the repository by diff. Checked the
   target signature and entire canonical restriction definition byte for byte:
   both are identical. The public imports remain identical. The additional
   transition definition and its proofs are private; nothing in another
   existing module is adapted. No existing statement is changed.
2. Compiled all three modules locally with lcompile.py in import order.
   Inspected every declaration for forbidden proof escapes and hollow data.
   A scratch copy with #print axioms shows only propext, Classical.choice and
   Quot.sound for the three public definitions, and those axioms plus sorryAx
   for the two open component theorems and the item that uses them. The tool's
   full declaration probe is also run by deliver3.py. No sorry remains outside
   the two named component theorems. Verdict: kernel-checked reduction with
   exactly the reported remaining holes, not a sorry-free target proof.
3. Read both new statements and their complete docstring arguments. For
   ideal-factor, checked localization using t outside p, c=0, g=0, a unit g,
   n=0 and empty W. For obstruction, checked g=0, a unit g, empty W and the
   identity case n=m. The over-W equation on h determines the map on the
   quotient structure sheaf, so the universal naturality quantifier is valid.
   The statements are independent strict parts of the argument: no H^1
   hypothesis in ideal-factor, and no torsion hypothesis in obstruction.
   Repeated searches with different words using leanfinder, loogle and rg.
   Found upstream H.delta, H.ker_delta_eq_range_map_g (Lean spellings H.δ and
   H.ker_δ_eq_range_map_g), generic Mathlib coimage/image descent tools, and
   proved QuotientBaseChangeIdeal/PrincipalQuotientMultiplicationImage
   components. None supplies either complete new statement. Formalizing the
   missing stalk descent and quotient/cohomology identifications exceeds a
   short repair, so both holes remain. Verdict: true, sourced, substantive
   decomposition with no duplicate theorem found.
4. Read the proof top down: canonical gap, natural boundary, factorization,
   H^1 vanishing, exactness. The private import is used, and the remaining
   public imports support signatures. Removed one redundant new import and
   confirmed compilation. Checked the old proof_deps and the unit record
   dag/units/sk-prop-input-spreading.json: this is below the unit level;
   the local factorization realizes the same bounded-torsion argument. The
   unit and its existing realized fields are untouched, and no unit step is
   bypassed. Verdict: no old module pruning; unit route preserved.
5. Compared the node Lean statement strings with the declarations and matched
   proof steps to the actual code. Replaced the stale core dependency in the
   item node with the two components. Expanded each new node's mathematical
   statement and proof, retained the required source, searches, status,
   creation, blueprint, chapter, unit and Lean fields, and added the second
   reader's search evidence. Verdict: node records now agree with the Lean.

Changes by this reading: corrected the stale item DAG route; clarified both
new-node statements and proofs; corrected denominator clearing and the
cohomology citation; updated the item proof description; qualified the Limits
image names to preserve the original top-level open command after the dry-run
preflight correctly requested an interface record for that command; removed a redundant
new import and an unnecessary interface change record; corrected the progress
and pruning report. No theorem statement or data construction was changed.
