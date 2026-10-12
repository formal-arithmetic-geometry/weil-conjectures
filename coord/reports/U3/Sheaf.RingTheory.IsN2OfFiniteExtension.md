## What changed

Proved `isN2_of_finite_extension` in
`Sheaf.RingTheory.IsN2OfFiniteExtension` without changing its signature or visibility.
Added the proof-only import `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
The second reading removed two redundant proof-only imports from the first draft.

The proof follows the existing six-step DAG argument. Extend the injective map
from A to E to an A-algebra map from K to E using `IsFractionRing.liftAlgHom`.
Embed an arbitrary finite L/K into `AlgebraicClosure E` using `IsAlgClosed.lift`.
Identify L with the intermediate field given by the embedding's range and apply
`IntermediateField.adjoin_rank_le_of_isAlgebraic_right` to obtain a finite
compositum over E. This compositum lies in the universe of E, as required by
`IsN2 B E`, even when K and E have independent universes. Apply the Japanese
hypothesis and `Module.Finite.trans`. Restrict the embedding to an injective
A-linear map of integral closures, using preservation of integrality and
`IsIntegral.tower_top`, and finish with `Module.Finite.of_injective` over the
Noetherian ring A.

The existing node's route and dependencies are unchanged, so no node edit is
needed. The item is not itself one of the unit's realized statement or steps;
the unit route is preserved.

## Proved and sorry left

Closed: `isN2_of_finite_extension`, node
`lem-weil-pbc-n2-descends-finite-domain-extension` (one of one original holes).
No holes remain in the item's module. No holes or declarations were added.
This is a full proof, not a decomposition. Local compilation succeeds without
warnings; the delivery dry run also checks declaration axioms.

## No longer needed

Removed the redundant first-draft proof imports
`Mathlib.RingTheory.Noetherian.Basic` and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`; their declarations are already
available transitively. Neither was an import of the original repository module.
Every old `proof_deps` node remains used mathematically. In the final step,
`Module.Finite.of_injective` packages the Noetherian submodule argument recorded
by `lem-weil-pbc-noetherian-submodule-finite`. No DAG nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Semantic, type-pattern, and text searches
found no existing Japanese-descent theorem. The supplied Mathlib declarations
suffice to implement the plan completely.

The cited local `literature/stacks-project/algebra.tex` is absent in this clone.
Verified the statement and integral-closure hint against the official source:
[Stacks Project, Tag 032K](https://stacks.math.columbia.edu/tag/032K).


## Second reading by U3

1. PASS: compared the sole delivered module against the repository with `diff`.
   The existing theorem signature, universes, visibility, definitions, and docstring
   are byte for byte unchanged. Only its proof and private imports differ; no
   interface change or change record is needed.
2. PASS: independently compiled the module with `lcompile.py`, without warnings.
   No `sorry`, new declaration, hollow definition, or forbidden construct occurs.
   A scratch copy with `#print axioms isN2_of_finite_extension` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. The chosen embedding is from
   the proved Mathlib `IsAlgClosed.lift`; no object depends on an unproved theorem.
3. PASS: no statements were split off and no holes were added. Reviewed the
   embedding, rank bound, integrality map, and injective linear restriction.
   The argument covers the identity extension and degree-one L/K and requires
   no separability. Independent universes are handled by taking the compositum
   inside `AlgebraicClosure E`, which has E's universe.
4. PASS: read all six steps of the node and the Mathlib matches of its substantive
   dependencies. A fresh semantic search for finiteness of integral closures
   over a smaller Noetherian ring found only results requiring extra hypotheses
   such as separability and normality; repository/upstream text searches found
   no shorter applicable theorem. Read `dag/units/sk-thm-p1.json` including all
   `realized` entries: this node is below the unit's steps, and none is bypassed.
   All old proof dependencies remain used; no node is no longer needed.
5. PASS: the existing `proof`, `proof_deps`, and `proof_origin` describe the actual
   argument. Fraction-field lift, algebraically closed embedding, compositum
   bound, integral-closure inclusion, finite-module transitivity, and Noetherian
   descent are all implemented. The last step uses the direct injective-map
   corollary of the recorded submodule argument. No new nodes are needed.

Changed only the two redundant first-draft imports named above and this report.
Recompiled with both imports removed simultaneously; the proof still compiles
without warnings. Closed one original hole, added zero holes; the proof is complete.
