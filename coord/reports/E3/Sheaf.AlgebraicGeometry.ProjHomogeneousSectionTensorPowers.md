## What changed

Replaced the proof of `AlgebraicGeometry.proj_homogeneous_section_tensor_powers`
by a conjunction assembled from invertibility, the tensor-power/multiplication data,
and the nonvanishing-locus equality. The existing target signature and docstring
are unchanged. Added two strict intermediate theorem modules and their DAG nodes.
Invertibility follows from the degree-one chart cover of
`proj_polynomial_twist_chart k 1` and the source lemma `Proj.isInvertible_twist`.
The target retains its original public imports; new intermediate imports are proof-only.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.proj_homogeneous_section_tensor_powers`.
Holes added and left:
- `AlgebraicGeometry.proj_homogeneous_section_tensor_powers_data`
  (`lem-sc-p1-homogeneous-section-tensor-powers-data`).
- `AlgebraicGeometry.proj_homogeneous_section_tensor_powers_locus`
  (`lem-sc-p1-homogeneous-section-tensor-powers-locus`).

This is a decomposition, not a completed proof: one upper hole closed and two
strictly smaller holes added, net -1 holes closed. Invertibility adds no new hole.
The target still uses sorryAx through its dependencies. There is no data definition
choosing an arbitrary witness from either unproved existence statement.

## No longer needed

Removed the direct target import of
`Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication`; its node
`lem-sc-p1-twist-multiplication` is no longer a direct proof dependency of the target.
It remains a planned dependency of the data component, so no whole module is claimed
pruned from the targets' closure. The locus component does not import that module.
Removed the redundant public Ample import from the new data component. Restored the
original public ProjectiveSpectrum.Twist import in the target instead of the first
worker's unnecessary public ProjectiveSpace.Twist import.

## Where the brief, the DAG or earlier work was wrong

The first worker's report omitted a third hole,
`proj_twist_isInvertible_all_degrees`, which had no DAG node. Removed that theorem
rather than adding a node: the existing source lemma proves invertibility using
the existing polynomial chart cover. The two reported split declarations also
lacked their node files and complete proof docstrings. Both are supplied now.
The target's proof/proof_deps/proof_origin now record the actual reduction.

The polynomial-Proj invertibility instance in ProjectiveSpace.Twist ties the index
and coefficient universes together; it cannot directly handle Fin 2 with an arbitrary
Type u coefficient field. The source `Proj.isInvertible_twist` has the required
universe generality, so its degree-one-cover hypothesis is discharged from the chart
node already on the original plan.

## New nodes

`lem-sc-p1-homogeneous-section-tensor-powers-data`: the strict tensor-power and
multiplication component. Chartwise fraction multiplication gives the isomorphisms,
and the coefficient `(f/x_i^d)^n` proves the two identities. Includes n=0, f=0 and
negative m in its proof docstring.

`lem-sc-p1-homogeneous-section-tensor-powers-locus`: the strict locus component.
On each chart, the fibre coefficient is f/x_i^d, nonzero precisely when f is outside
the homogeneous prime. Includes f=0 in its proof docstring.

No statements or definitions were changed, so no change record is needed.

## Second reading by E3

1. Compared all delivered existing modules with the repository. The target theorem
signature and docstring are byte-for-byte unchanged. Its original public imports
are preserved. There are no definition changes or unreported statement changes.

2. All three files compile without warnings with `lcompile.py --all`. A scratch copy
with `#print axioms` shows only propext, Classical.choice, Quot.sound and sorryAx for
all three theorems. Only the two named intermediate theorems contain sorry. Checked
for axiom, unsafe, opaque, implemented_by, extern and hollow definitions: none.

3. Each split theorem is a strict component, not a restatement of the target.
Checked small cases: n=0 is the unit/multiplication-by-one identity, f=0 gives the
empty locus and zero positive powers, d=1 agrees with coordinate-section formulas,
and negative m uses the same chart basis. Both have complete source proof docstrings
and matching new nodes. Repeated msearch with LeanSearch (unavailable), loogle, leanfinder and grep, and local
rg on the upstream Twist and Sheaf projective APIs. No existing theorem proves the
arbitrary homogeneous section data or locus equality. Source UnitToTwist has local
fraction formulas and freeness but not these global conclusions.

4. Read top-down. Replaced the gratuitous invertibility hole by the existing source
lemma and original chart-cover node. Removed the unnecessary direct multiplication
import and recorded its dependency transfer to the data node. Reviewed
`dag/units/sk-thm-picard-duality.json` and its realized fields: this auxiliary node
is not a realization of the unit statement or a unit step, and the chartwise route
of the original node remains in the component plans. No unit route is bypassed.

5. Updated the target node's proof, proof_deps and proof_origin to the Lean proof.
Both new nodes have source, full proof plan, union proof dependencies, three searches,
created/blueprint/chapter/unit fields and verbatim Lean statements. Compared the
mathematical reduction with Stacks Tags 01MS, 01MV and 01NG at
https://stacks.math.columbia.edu/tag/01MS,
https://stacks.math.columbia.edu/tag/01MV and
https://stacks.math.columbia.edu/tag/01NG; the local literature file is absent here,
so read the official pages instead.

Second reading changed: removed the unreported invertibility hole, repaired imports
and line-width warnings, expanded the two proof docstrings, supplied missing nodes,
updated the target DAG route, and corrected the report to count a decomposition.
