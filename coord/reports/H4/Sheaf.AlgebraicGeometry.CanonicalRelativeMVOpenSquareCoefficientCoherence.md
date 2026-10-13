## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.CanonicalRelativeMVOpenSquareCoefficientCoherence` with
an explicit specialization of `coefficient_square_coordinate_change` to the
nested open pullback squares and the identity coefficient morphism. Added its
module as a proof-only import. The five square equalities are supplied by
`Scheme.homOfLE_ι`, the two pullback lift equations, and the two pullback
conditions. Expanded comparison components and simplified functorial identities
and associativity. Added the proved private helper `comparison_inv_map_id`,
which is just functorial preservation of identities followed by the category
right-identity law. Abstracting the chosen comparison family during this step
avoids unfolding its full construction. A theorem-local elaboration option
matches the options used in the comparison dependency. All existing signatures
and public imports are unchanged.
The proof follows the existing node's plan; no node changes are needed.

Searches: Lean Finder returned categorical pullback transformation laws, without
an exact match for the fixed derived comparisons. Loogle confirmed
`CategoryTheory.Functor.map_id`. Launcher grep and repository searches located
the exact general project theorem and its use in
`SingleComplexNestedCoefficientCoherence`. The unit record has no realized
statement or steps for this node; its route is preserved.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.canonical_relativeMV_open_square_coefficient_coherence`
(node `new-canonical-relative-mv-open-square-coefficient-coherence`).
No sorry remains in the item; no holes or public declarations were added.
The private helper `comparison_inv_map_id` is proved.
The imported coordinate-change theorem is already proved in its own module.
This closes the item's hole without a decomposition, while retaining the
existing derived-composition dependencies.

Single-file launcher compilation passed cleanly in 10.1 seconds.

## No longer needed

None. No imports were removed, and the only planned proof dependency,
`lem-pc-coefficient-square-coordinate-change` /
`Sheaf.AlgebraicGeometry.CoefficientSquareCoordinateChange`, is used.
The public `RelativeMVMaps` import supplies definitions in the statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement errors found. The planned proof dependency was
absent from the module's imports, so this delivery adds it privately.

## Second reading by H4

1. Interface: PASS. Read the entire delivered module and its repository diff.
   Compared the existing theorem text from its name through `:= by` with a
   byte-for-byte assertion: identical. Its universes, derived-category family,
   arbitrary morphism g', opens W and U, inclusion i and object N are unchanged,
   as are both sides of the identity. The existing public import is unchanged;
   the added coordinate-change import is proof-only. No definitions, public
   declarations, change records or node files were added or altered.
2. Proof: PASS. Independent launcher compilation was clean (13.3 seconds).
   Compiled a scratch copy with `#print axioms` for both the item theorem and
   the private helper: each uses only propext, Classical.choice and Quot.sound;
   neither uses sorryAx. Source scan found no sorry or forbidden declaration.
   The helper is exactly Functor.map_id followed by Category.comp_id. The
   generalization of c only abstracts the existing pinned comparison family;
   it creates no object or new choice. relativeMVComp unfolds to that same
   family, whose defining composition theorem pins its hom to leftDerivedLift.
3. Split statements: PASS, vacuously. There are no new public statements or
   split-off holes. The private helper is proved for arbitrary categories,
   functors, isomorphism and object; its identity calculation needs no geometric
   assumption. In particular no empty-open, equal-open or zero-coefficient case
   is excluded. No data is taken from a new unproved existence theorem.
4. Route and pruning: PASS. Read coefficient_square_coordinate_change and its
   proof, RelativeMVMaps, the existing SingleComplexNestedCoefficientCoherence
   application, and sk-thm-picard-semicon.json. The specialization sets
   v=W.ι, z=U.ι, t=qW, s=pW, qz=qU, pz=pU, e=homOfLE i and b=relativeMVOpenLift;
   K=N, K'=L_g' N and phi=identity. Scheme.homOfLE_ι proves hv;
   lift_snd and lift_fst prove ht and hs; the U and W pullback conditions,
   reversed, prove hz and hrect. Removing the mapped identity and expanding the
   comparison components gives exactly the target. Repository searches and an
   additional launcher grep for relativeMVComp/coordinate_comparison found no
   shorter independent packaged proof. The other relative-MV coherence wrapper
   depends on this item and cannot be used to prove it. Both imports are needed:
   RelativeMVMaps defines the statement's comparisons and lift; coordinate
   change supplies the proof. No old proof dependency is unused. The unit has
   realized.statement=[] and realized.steps=[[]]; no unit route is bypassed.
5. DAG and source: PASS. Read both the item's node and
   lem-pc-coefficient-square-coordinate-change. The item's existing proof step,
   sole proof_deps entry and proof_origin describe precisely this specialization
   and elementary component expansion; no node correction is needed. Read
   Stacks Tag 0D5S, Lemma 20.27.2, at its official page: it supplies the derived
   composition comparison, and the coordinate identity is the formal
   associativity/naturality consequence proved by the dependency, not an extra
   assertion quoted from Stacks. All five required equalities are supplied
   without extra hypotheses or cancellation of coordinate arrows.

Second reading changed only this report. The proof was correct and was kept.
