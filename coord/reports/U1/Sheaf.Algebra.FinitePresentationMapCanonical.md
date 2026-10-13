## What changed

Proved `ModuleCat.finitePresentation_map_directedColimit` in
`Sheaf.Algebra.FinitePresentationMapCanonical`, preserving its entire signature,
all original public imports, and its exact canonical comparison isomorphisms.
Added one proof-only import: `Sheaf.Paper.DirectedColimitBaseChangeElementwise`.

The private, fully proved helper `fp_lift` lifts maps out of a finitely presented
module using the representative and eventual-zero properties of a directed module
system. Its finite-set inductions lift the generators together and kill the finite
kernel generators together. The resulting map descends through the kernel quotient.
The private, fully proved helper `comparison_one` handles the cocone equality in
the canonical tensor comparison. The final argument curries the lifted map and
checks the canonical commuting square on unit tensors, using tensor induction to
identify the elementwise coprojection with that comparison.

Updated the existing node's proof, proof_deps, and proof_origin to this route.
No definitions, existing statements, or other modules changed. No new nodes.

Source: [Stacks 05N7 (2)](https://stacks.math.columbia.edu/tag/05N7), which refers to
[Stacks 05LI (3)](https://stacks.math.columbia.edu/tag/05LI). The proof follows the
latter's generator/kernel argument. The local literature file was absent, so the
official pages were read directly.

## Proved and sorry left

Closed the only original hole:
`ModuleCat.finitePresentation_map_directedColimit`
(node `lem-pc-fp-module-map-canonical-preorder`).

Holes closed: 1. Holes added: 0. No sorry remains in any delivered Lean file.
Both private helpers are proved, and the sole imported Sheaf theorem is already
proved. This is a proof, not a decomposition.

The proof treats the upper tail as a preorder directly and uses no antisymmetry.
The empty generator and relation cases are covered by the empty cases of the
finite-set inductions, and zero rings and modules require no extra assumptions.
Finitely presentedness of N is mathematically unnecessary for this route; the
original hypothesis remains, installed as a local instance to keep the unchanged
signature free of unused-variable warnings.

## No longer needed

The old direct proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-tensor-right-exact` (`rTensor_exact`, `lTensor_exact`): the lifted
  map descends through the source's kernel quotient before scalar extension.
- `lem-weil-pbc-tensor-finite-product` (`TensorProduct.piLeft`): the proof uses
  the finite free cover in `Module.FinitePresentation` directly.
- `lem-pc-filtered-colimit-commrings-elementwise`: replaced as a direct dependency
  by the already proved tensor elementwise theorem above.

These three dependencies are removed from this node's proof_deps. They were not
imported in the original module, so no original import was removed. The proof needs
none of `Sheaf.Algebra.FinitePresentationColimit`,
`Sheaf.Algebra.FinitePresentationRestrictedHomColimit`,
`Sheaf.Algebra.FiniteRelationCokernelColimit`, or
`Sheaf.Algebra.FiniteTensorVanishingColimit`; none is imported. This is a local
pruning statement, not a claim that these nodes are globally unreachable from
other targets or from the internals of reused theorems.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned presentation of N and relation-witness coefficient
matrices are unnecessary: the existing tensor-colimit elementwise theorem handles
arbitrary N. The theorem still has the exact original hypotheses and conclusion.
The unit record `sk-thm-picard-semicon` realizes no statement or steps with this
auxiliary node, and the change stays below the unit level.

## Second reading by U1

1. I compared the delivered module with the repository version. The public
   theorem signature and all existing declarations are byte-for-byte unchanged;
   the only module change is the proof and one proof-only import.
2. I compiled the module with `lcompile.py`; it succeeds with no errors. The
   source contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`. The proof uses only the stated elementwise tensor-colimit theorem
   and the finite-presentation generator/kernel construction.
3. The private helpers are fully proved and introduce no split-off statements or
   new nodes. The target theorem is exactly the existing node statement, and
   the finite-set edge cases are handled by the empty induction branches.
4. The proof follows the shortest available route below the unit: it uses the
   existing tensor elementwise criterion and direct finite presentation data.
   The node's proof and proof dependencies match the code, and the three old
   dependencies listed above are genuinely unused.
5. The unit route is preserved: this auxiliary node remains below
   `sk-thm-picard-semicon`, whose statement and realized steps are untouched.

I changed only this report section; no Lean declarations, statements, imports,
or DAG nodes required repair.
