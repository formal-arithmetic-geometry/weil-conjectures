## What changed
Replaced the all-degrees restatement with a genuine reduction. The existing module
`Sheaf.Algebra.Homology.SecondLocalizationOrdinaryBSquare` now transports a raw
cohomological counit square through `ordinaryIso` and `cohomologyIso`, using the
model `comparison_eq` fields, adjunction naturality, and exact-restriction
homology naturality. Its existing statement and public import are unchanged.
The new proof dependency is a plain, proof-only import of
`Sheaf.Algebra.Homology.SecondLocalizationRawCounitSquare`.
Elaboration transparency options are scoped to the existing theorem.

## Proved and sorry left
Hole closed: `RingTensorCohomology.secondLocalization_ordinary_B_square`.
Hole added and left: `RingTensorCohomology.secondLocalization_raw_counit_square`,
node `lem-pc-second-localization-raw-counit-square`.
There are no other holes in the delivery. This is a decomposition, not a complete
proof: one upper hole is replaced by one strictly smaller raw-counit obligation;
net holes closed is zero. The proved part is the generator calculation, chain
conjugation, cohomology-isomorphism cancellation and ordinary-comparison transport.
The raw obligation mentions none of the model ordinary, cohomology or comparison
identifications; its complete natural-language proof is in its docstring and node.

## No longer needed
No dependency of the repository's old proof_deps is removed; no repository module
is pruned. The attempted `SecondLocalizationOrdinaryBSquareAllDegrees` module,
its new node, and its change record have been removed from the sandbox delivery.
They had never belonged to the repository baseline.

## Where the brief, the DAG or earlier work was wrong
Quantifying the target over all degrees does not make a new proof step. The earlier
report incorrectly called specialization of that still-unproved restatement a
proof. The new target proof instead establishes the model transport and uses only
the raw counit calculation as an open intermediate.
The model-existence choice construction upstream is outside this delivery; no new
data is chosen from an existence theorem here.

## New nodes
`lem-pc-second-localization-raw-counit-square` records the raw homology square for
the universal derived counits and flat second coefficient extension. Source:
[Stacks Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6), with flat cohomological
coefficient transport as used in
[Stacks Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8).
This is the counit step of the old plan, before any ordinary or model-cohomology
transport. LeanSearch returned an Internal Server Error and is recorded as unavailable.
Searches with leanfinder, loogle and grep found general adjunction and
homology naturality tools, but no declaration of this raw square. The existing
`baseDerivedTensor_ring_counit_square` assumes its raw square and handles ring
isomorphisms, so it does not supply this flat, possibly noninvertible coefficient map.
No existing interface changes and no change record are needed.

## Second reading by E1
1. Compared the delivered target module with the repository version. Its existing
   theorem signature is byte for byte unchanged, including `include tRB`; its
   public import is unchanged. The only new import is proof-only. No definitions
   or target statements change.
2. Compiled both modules locally through lcompile.py. The target proof has no
   sorry; the only new sorry is the whole proof of the named raw-counit theorem.
   No axiom, unsafe, opaque, extern or implemented_by occurs. Scratch-copy #print axioms for both declarations gives precisely propext,
   Classical.choice, Quot.sound and sorryAx. The raw theorem is the only direct
   sorry in these two modules; the target depends on it.
3. The all-degrees restatement is rejected and removed. The new raw statement is
   a strict part of the old plan: it has no ordinaryIso, cohomologyIso, comparison,
   or localizedComparison in its formula. Checked generator uniqueness by tensor
   induction and the zero-complex, zero-ring, identity-coefficient and concentrated
   degree-zero cases. In degree zero on flat input the assertion is the ordinary
   tensor coefficient map, so the directions of the transpose and inverse exact
   restriction isomorphism agree. Its docstring and node give the proof. Searched
   Mathlib through three kinds of msearch and the local Sheaf/upstream sources;
   no usable existing raw square was found.
4. Kept the original SecondLocalizationMap import and used its concrete map.
   The remaining step is the raw universal counit calculation. The ordinary
   generator and isomorphism transport have been proved rather than split off.
   The old proof_deps node remains used. The unit sk-thm-picard-semicon has empty
   realized statement and step arrays; this below-unit reduction changes no unit
   route. No repository module becomes unnecessary.
5. Rewrote the target node proof and proof_deps to reflect the actual reduction;
   the new node has its source, proof, proof_deps, proof_origin, searches, creation,
   blueprint ancestry and verbatim Lean statement. Both modules follow the module
   system contract. No node statement or statement dependency changed.

Changed: removed the restatement delivery; wrote the raw counit intermediate and
proved transport to the unchanged target; corrected the node route and report.
