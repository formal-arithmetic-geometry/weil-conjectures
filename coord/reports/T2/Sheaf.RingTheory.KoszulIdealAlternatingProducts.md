## What changed

Proved `AlgebraicGeometry.koszul_ideal_alternating_products` in
`Sheaf.RingTheory.KoszulIdealAlternatingProducts` without changing its signature or
public imports. Added proof-only imports of `KoszulAugmentationLiftExists`,
`KoszulAugmentationLiftHomotopy`, and `KoszulGeneratorChainMap`. Updated the item's
DAG proof and dependencies to the actual route.

The proof uses the existing `ExteriorAlgebra.boundary_wedge`, constructs rectangular
Koszul substitutions degree by degree, and applies homotopy uniqueness of augmentation
lifts. Basis-wedge evaluations then satisfy additivity, scalar compatibility, and
alternation by explicit substitutions into a common Koszul complex. Tensoring with A/I
proves ideal annihilation; monicity of iCycles identifies the prescribed cycle.
The local definitions `wedgeCycles` and `wedgeEval` are concrete linear maps, with no
unproved construction prerequisites. Choices of augmentation maps occur only inside
the theorem proof and use the already proved lifting theorem.

Sources read: Stacks Tags 0621 (in particular Lemma 15.29.3, Tag 0624), 00LS
(parts 1 and 2), and 09PQ. The shorter argument follows Koszul functoriality and the
comparison homotopy theorem, rather than the original Tate-resolution plan.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.koszul_ideal_alternating_products`
(node `new-t4-koszul-ideal-alternating-products`). No holes remain in the item;
no holes or modules were added. This is a proof, not a decomposition.

The single-file compiler passed cleanly. `#print axioms` reported exactly
`propext`, `Classical.choice`, and `Quot.sound` for the theorem, with no sorry axiom.
All delivered Lean lines fit within 100 characters. The proof includes n=0,
I=0, I=A, the zero ring, and characteristic two; alternation is supplied by
exterior powers, without dividing by two. The unit's `realized` lists are empty,
so no prescribed unit statement or step is bypassed.

## No longer needed

No imports removed and no existing nodes or modules pruned. The original proof had
no proof-dependency imports or nodes. A Tate resolution, a strictly commutative Tor
algebra structure, and conormal descent are unnecessary for this proof and were
not imported or constructed. The existing public presentation import stays because
it supplies the statement's concrete wedge-cycle type.

## Where the brief, the DAG or earlier work was wrong

The DAG's three Tate-resolution steps supplied no Lean dependencies, but a fully
proved route is available through finite Koszul substitutions and the existing
augmentation homotopy theorem. The existing equal-rank integer-extension generator
map theorem is not sufficient for substitutions between different tuple lengths;
this proof constructs the required rectangular maps locally using its module's
proved `boundary_wedge` API. No interface was changed and no forced adaptation
was required. The old docstring describes a valid alternative Tate plan; the updated
DAG and the inline proof comments describe the implemented shorter argument.

Lean Finder returned cotangent/Kähler differential lemmas rather than the required
Koszul product; Loogle returned an unrelated ideal norm lemma. The scripted grep
returned no usable product construction, and direct source searches located the
existing lift and homotopy APIs used here. The tempting existing Tate comparison
module cannot be imported because it already depends on this item.

## Second reading by T2

1. **Interface preservation — pass.** Compared the complete module with the
   repository version using `diff`, and compared the declaration tables with
   `stage3_delivery.diff_module`. The existing theorem's signature, visibility,
   and docstring are byte-for-byte unchanged. The original public import is
   unchanged; the three added imports are plain proof-only imports. The only
   delivered Lean module is the claimed item. No statement, definition, or
   downstream module was changed.

2. **Proof and trust — pass.** Read all six private helper theorems, the two
   concrete private linear-map definitions, and the main proof. The cycle maps
   use the inverse of an explicit cycles isomorphism after proving the tensor
   differential zero. Rectangular exterior-power substitutions commute with the
   boundary, and their degree-zero maps preserve augmentation. Tensoring the
   comparison homotopy gives precisely the naturality equality used later.
   The three substitution arguments establish addition, scalar compatibility,
   and equal-entry vanishing, and ideal annihilation is checked on the quotient
   tensor factor. The final cycle identification uses monicity, not a choice of
   arbitrary representatives. Compiled the delivered file cleanly with
   `lcompile.py`, and compiled an independent scratch copy with
   `#print axioms AlgebraicGeometry.koszul_ideal_alternating_products`:
   exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, forbidden
   declaration, or hidden unproved construction is present. Degree zero uses
   the empty wedge; the update identities with an index are vacuous there.
   The zero ideal, unit ideal, zero ring, ranks smaller than the exterior degree,
   and characteristic two require no exclusions.

3. **Split-off statements — pass (none).** No new public statements, modules,
   nodes, or holes were added. The sole original hole is closed, so this is a
   proof rather than a decomposition. Private helpers are fully proved.

4. **Route, search, and pruning — pass.** Independently searched Lean Finder for
   contraction-compatible exterior-power maps, Loogle for
   `exteriorPower.map, exteriorPower.ιMulti`, and Mathlib grep for naturality of
   contraction and Koszul maps. The exterior-power evaluation lemmas found are
   already used; no complete Koszul alternating-product construction was found.
   Inspected the existing generator-map, lifting, and homotopy modules, together
   with the presentation and self-Tor uniqueness modules. The existing
   generator-map theorem has equal ranks and integer-extended complexes, whereas
   this proof needs different ranks and natural degrees. Existing tensor-zero
   proofs in the presentation/uniqueness files are private and cannot replace
   this file's helper through their public interfaces. The Tate comparison
   construction imports CycleRelations, which imports this item; using it here
   would create a cycle. All four imports are needed for the statement or proof.
   The original `proof_deps` is empty, so the report's list of removed nodes is
   complete (none). Checked `dag/units/sk-thm-picard-duality.json`: its
   `realized.statement` and only `realized.steps` entry are empty, and this
   below-unit substitution route bypasses no recorded realization. The source
   claims agree with [Stacks Tag 0624](https://stacks.math.columbia.edu/tag/0624)
   and [Tag 00LS](https://stacks.math.columbia.edu/tag/00LS).

5. **DAG correspondence — pass.** The node differs only in `proof`,
   `proof_deps`, and `proof_origin`. The dependency list is exactly the union of
   the proof steps' `uses`: augmentation-lift existence, the generator-chain-map
   node supplying `boundary_wedge`, and augmentation-lift homotopy. Each has the
   declared Lean module and a proved API used here. The four proof steps describe
   the actual constructions and their order. The node statement and Lean record
   are unchanged; no new-node requirements or change records are needed.

Second-reading changes: appended this review and its independent verification
results. No Lean or node repair was necessary. Holes closed:
`AlgebraicGeometry.koszul_ideal_alternating_products`; holes added: none.
