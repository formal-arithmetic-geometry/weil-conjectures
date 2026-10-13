## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.KoszulCoordinateConeIso` with a
complete Lean proof from existing tensor coordinates and one new general assembly criterion.
The signature and existing docstring are unchanged. Proved private helpers for contraction
naturality, exterior-power coercions, generator reindexing, tensor-unit naturality, and
untensored Koszul cone coordinates. The final proof explicitly reindexes the updated
coordinate, assembles the unsheafified cone, and applies the additive tilde cone comparison.

Added proof-only imports of
`Mathlib.LinearAlgebra.ExteriorPower.Basic` and
`Sheaf.Algebra.Homology.ChainConeCoordinatesIso`. Existing public imports remain necessary
for the unchanged statement and its sheaf-category instances.
Updated the item's DAG proof and dependencies to record the actual reduction.

## Proved and sorry left

Closed: `AlgebraicGeometry.koszul_coordinate_cone_iso`
(node `lem-pc-koszul-coordinate-cone-iso`), proved from the named declarations below.
No sorry remains in the item's module or in any private helper.

Added one hole: `ChainComplex.scalarCone_iso_of_coordinates`
(node `lem-pc-chain-cone-coordinates-iso`), in the new module
`Sheaf.Algebra.Homology.ChainConeCoordinatesIso`. Its whole proof is `by sorry`;
its docstring and node give the full assembly argument and all integer-degree cases.
This is a decomposition, not a completed proof of the original axiom-free theorem:
one upper hole closed and one strictly simpler assembly hole added (net zero holes).
The new theorem assumes actual linear cone coordinates and their boundary identities;
it proves only their generic complex assembly. It contains no Koszul, permutation,
coordinate update, sheafification, or arbitrary witness construction.

Both delivered modules compile cleanly together using lcompile.py, and the delivery's
axiom probes pass. The final deliver3.py dry run passes all worker-side checks; the
independent second reading is deliberately left to the second reader.
Edge-case review: in degree zero the shifted source summand is zero; positive
cochain degrees are zero on both sides. For a=0 the stated matrix is the split cone
matrix. Zero modules and the zero ring use the same formulas. The original r=0
case is included in the coordinate theorem and the proved reindexing argument.

## No longer needed

Removed the earlier sandbox attempt's redundant proof import
`Mathlib.LinearAlgebra.TensorProduct.Associator`; recompilation succeeds without it.
No existing import, proof-dependency node, or module of the original library route is pruned.
The tensor cone coordinates are genuinely used. The two remaining added proof imports
support actual proof steps; the unit route is unchanged. The second reading also
removed the redundant added import `Mathlib.Logic.Equiv.Fin.Basic`; the permutation
API remains accessible from the existing imports.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt added file-level `open ExteriorAlgebra` and
`open scoped TensorProduct` commands, which the interface checker flags. These have
been removed: identifiers and the tensor-product type are now qualified, preserving
the original file-level commands and the public signature.

The DAG step 2 described assembling the coordinates but did not name a declaration
which assembles natural-number chain coordinates after extension to integer cochain degrees.
The available tensor coordinate theorem supplies the algebra, not that assembly.
The new generic criterion states precisely this remaining part. Reindexing, transfer
through the tensor unit, and sheafification are proved rather than restated as holes.

LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and source grep
were used and recorded. Stacks Tags 0628 and 0629 were read online because the TeX
source is absent here. Some current online Mathlib search results, notably
`exteriorPower.coe_map`, are absent from the pinned version, so the coercion identity
was proved locally from exterior-power extensionality.

## New nodes

`lem-pc-chain-cone-coordinates-iso`:
`ChainComplex.scalarCone_iso_of_coordinates`, in
`lean/Sheaf/Algebra/Homology/ChainConeCoordinatesIso.lean`.
This is a generic, differential-compatible coordinate assembly theorem over A-modules.
Its node is in `dag/nodes/sec-picard-framework/`, inherits the item's unit and blueprint
ancestry, and records the source, searches, degree-zero case, negative-degree matrix
check, and positive-degree zero-object case. No definitions or existing interfaces changed;
no change record is required.

## Second reading by U3

1. Compared the entire item module with the repository using `diff`. The existing
   declaration's signature and docstring are byte for byte unchanged. Only its
   proof, private proved helpers and proof-only imports change. There are no new
   definitions and no change records or forced adaptations. Verdict: pass.
2. Compiled both modules in import order using lcompile.py. The item and all its
   private helpers have no sorry. The only delivered sorry is the named public
   assembly theorem listed above, with a complete docstring proof and a matching
   node. No forbidden declarations or hollow definitions occur. A separate scratch
   module prints axioms of both public theorems: propext, Classical.choice,
   Quot.sound and sorryAx only. The generic witness is eliminated inside a proof
   of Nonempty, never used to define data. Verdict: pass as a decomposition.
3. Read scalarCone_iso_of_coordinates independently. In degree -(n+1), exchanging
   (x,y) gives the cone's (source,target) coordinates (y,x); the stated matrix is
   then (-d y, d x + a y), matching Mathlib mappingCone.d_fst_v and d_snd_v.
   At degree zero the extended source in degree +1 vanishes; h₀ is precisely
   the remaining differential equation. Positive degrees are zero. This covers
   a=0, zero modules, the zero ring, and the r=0 application without a hidden
   regularity hypothesis. The criterion has actual coordinates and compatibility
   as hypotheses and omits all reindexing, exterior algebra and sheafification;
   it is a strictly smaller part of the argument, not a renamed target.
   Reviewed Stacks [0628](https://stacks.math.columbia.edu/tag/0628) and
   [0629](https://stacks.math.columbia.edu/tag/0629). Fresh searches with the block
   matrix description, Loogle `CochainComplex.mappingCone, CategoryTheory.Iso`,
   Mathlib homology grep, both library roots, and upstream ProjectiveSpace/Koszul
   found generic assembly APIs but no matching coordinate criterion. LeanFinder
   was unavailable on this reading. Verdict: pass; the assembly hole remains.
4. Read the final reduction from the target downward: the explicit permutation
   and contraction-natural exterior equivalence, tensor-unit transfer of existing
   coordinates, the generic assembly criterion, and the additive tilde comparison.
   The existing proof_deps are both used and none is removed. The unit record
   sk-thm-picard-duality.json and its realized fields are unchanged. Removed the
   redundant added Fin.Basic proof import and recompiled successfully. Attempts
   to remove ExteriorPower.Basic or ModuleCat.Biproducts produce missing-identifier
   errors, so retained them. Verdict: pass; no original-route module is pruned.
5. Checked both node records against the declarations, proof steps and dependency
   union. The new node has the required source, searches, creation, ancestry,
   chapter, unit and verbatim Lean statement. The existing node changes only its
   proof, proof_deps and proof_origin. Verdict: pass.

Second-reading changes: removed the redundant added Fin.Basic import; clarified
that the degree-zero cone source is the extended L in degree +1, not the natural
chain term L₁; recorded fresh searches in the new node. No proof rewrite, signature
change or additional hole was needed. The delivery closes one original hole and
adds one smaller hole, so its net hole reduction is zero.
