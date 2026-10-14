## What changed
Split the target proof into two named intermediate declarations in the same module. The open/base-map component is obtained from `affine_torsor_single_stabilizer_component_open`; the target then combines it with the section equation theorem.

## Proved and sorry left
The target theorem `affine_torsor_single_stabilizer_component` is proved by combining the two intermediate results. The two strictly smaller intermediate theorems `affine_torsor_single_stabilizer_component_open` and `affine_torsor_single_stabilizer_component_section` remain `sorry`, with nodes `lem-sbc-affine-torsor-single-stabilizer-component-open` and `lem-sbc-affine-torsor-single-stabilizer-component-section`.

## No longer needed
None; the existing proof dependency import remains required.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped at the quotient descent step. The stage-3 requirement permits this step to be split into the open/base-map construction and the section identity, after which the target proof is a real Lean combination.

## New nodes
`lem-sbc-affine-torsor-single-stabilizer-component-open` and `lem-sbc-affine-torsor-single-stabilizer-component-section` are strict intermediate statements corresponding to the two conjunctive parts of the target conclusion.

## Earlier second reading (a previous round; superseded)
The open/base-map and section declarations are strict conjunctive parts of the target. The target theorem combines them without changing its signature; the unit route through stabilizer quotient descent is retained. Both intermediate proofs remain explicit named holes for a subsequent worker.

## Second reading by P1

1. I compared the delivered module with the repository version. The existing target theorem
signature is unchanged byte-for-byte; its proof now combines the two named component
statements. The added public declarations are the two conjunctive parts recorded by the new
nodes.

2. I compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry`s are the
two named intermediate theorems, each documented and represented by a DAG node. No definition,
axiom, unsafe declaration, or forbidden implementation mechanism was added.

3. I checked the two split statements against the target conclusion. The open theorem gives
exactly the existential, immersion, and base-map conjuncts; the section theorem gives exactly
the remaining section equation for the same restriction map. Both are true strict components
and are used by the target proof; no duplicate library declaration was found.

4. The target proof uses the shortest available route in this module: obtain the open component,
then apply the section equation and assemble the conjunction. All existing imports remain needed
by the public statements or the delegated proof dependencies, so no import was pruned.

5. The DAG nodes' Lean declarations, proof descriptions, and dependencies match the written
decomposition. The unit route through stabilizer quotient descent is retained by both nodes and
the target. No statement or definition change was made.

I changed only this report section; no Lean repair was needed.
