## What changed
Added the lower-level theorem `primary_fixedField_pullback_iso` in `PrimaryModuleFiltrationBaseChange`, splitting the represented-germ and equivariance argument from the target. The target theorem is proved by composing this fixed-field pullback isomorphism with `Etale.upperStarComp` and mapping it along `e.inv`.

## Proved and sorry left
Proved `primary_inverseImage_restriction` from the lower theorem and the upper-star composition isomorphism. One sorry remains: `primary_fixedField_pullback_iso`, recorded by node `lem-sc-primary-fixed-field-pullback-iso`.

## No longer needed
No imports were removed. The target proof uses the fixed-field comparison module, the stalk module, the Galois automorphism extension, and upper-star composition.

## Where the brief, the DAG or earlier work was wrong
The DAG's two proof paragraphs combine the stalk-equivariance construction with transport along `e`; Lean's categorical composition is cleaner after splitting the first part into a named lower theorem.

## New nodes
`lem-sc-primary-fixed-field-pullback-iso` records the lower theorem and its Stacks Tags 03QT, 03QW and 04JQ source.

## Earlier second reading (a previous round; superseded)
A second worker should verify the lower theorem statement against the represented-germ argument and check that the target composition preserves the exact signature.

## Second reading by F4

1. I compared the delivered inverse-image module with the repository version. Its theorem signature is byte-for-byte unchanged; the only interface addition is the separately recorded lower comparison theorem. The target node now records the lower theorem and upper-star composition actually used by the proof.

2. I compiled all five delivered Lean modules with `lcompile.py --all`. The target theorem is proved without `sorry`; the new lower theorem `primary_fixedField_pullback_iso` is the sole new split-off hole, with its Stacks-source proof description and matching DAG node. No axiom, unsafe, opaque, extern, or implemented_by declaration was added.

3. The lower statement is strictly simpler than the target: it omits transport along `e` and states only the fixed-field pullback comparison. It has the same hypotheses needed by the represented-germ argument and is not a restatement of the target. The categorical composition proof uses the existing upper-star composition result. No duplicate declaration was found in the library.

4. The proof follows the shortest available route in the delivered interfaces: invoke the fixed-field comparison, then map it along `e.inv` and compose with `Etale.upperStarComp`. The unit route is preserved. No imports were removable; proof-only imports remain private imports.

5. The target and lower node metadata agree with the Lean declarations, including the lower theorem's proof dependency and the target's updated proof dependencies. The unit record remains unchanged and its route is respected.

I changed the target proof dependency metadata to name `lem-sc-primary-fixed-field-pullback-iso`, added the lower theorem module and node, and added this second-reading record. No existing statement or definition was changed.
