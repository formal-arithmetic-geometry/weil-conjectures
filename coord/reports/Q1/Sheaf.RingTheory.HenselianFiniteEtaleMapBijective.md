## What changed

Proved `CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`
with its original signature and visibility. Only the target algebra is decomposed, using
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`. Formal étaleness of its local
factors follows from Mathlib's `Algebra.FormallyEtale.pi_iff`. The proof explicitly assembles
injectivity and surjectivity from the local comparisons through tensor-product and product
isomorphisms, including the empty product.

Added the proved theorem
`Algebra.bijective_residueField_tensor_map_of_henselian_target` in
`Sheaf.RingTheory.HenselianLocalTargetEtaleMaps`. Its base ring is merely local; the target
is finite, formally unramified and henselian local, and the source is any étale algebra.
The private, fully proved `Algebra.existsUnique_etale_lift_residue` derives residue-point
lifting from the existing unique pointed retraction theorem. Identifying the target's
reduction with its residue field and tensor adjunction finish the local comparison.
No construction chooses data from an unproved mere-existence theorem.

The item's proof imports are now `Sheaf.RingTheory.FiniteOverHenselianLocalProduct`,
`Sheaf.RingTheory.HenselianLocalTargetEtaleMaps`, and `Mathlib.RingTheory.TensorProduct.Pi`.
The new module has proof imports for the existing retraction theorem, unramified local
rings, and tensor products with quotients. The item node records the actual shorter route.
The existing theorem's docstring remains its original valid proof plan; the implemented
alternative is recorded in the node and this report.

Both final modules compile together through `lcompile.py --all`, without warnings or
textual `sorry`, each within the single-file limit. Edge cases were checked in the
argument: a zero source has no maps into a nonzero local target; a zero global target is
an empty product, covered by the same coordinate assembly. There are no added hypotheses
on the item, no modified existing definitions, and no forced adaptations.

## Proved and sorry left

Closed the item's sole hole:
`CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`
(node `lem-weil-pbc-henselian-finite-etale-map-bijective`).

Also proved the new public theorem
`Algebra.bijective_residueField_tensor_map_of_henselian_target`
(node `lem-weil-pbc-henselian-local-target-etale-maps`) and its private residue-lifting
helper. No holes added, no holes split off, and no `sorry` remains in any delivered module.
Existing imported declarations are used as library results; this report does not claim
that the entire transitive library import closure is sorry-free.

## No longer needed

Removed the item's direct imports of `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`
and `Sheaf.RingTheory.HenselianEtaleRetraction`. Their results remain necessary through
the finite henselian decomposition and the new local-target module, respectively;
they are not claimed globally unreachable.

The following original proof dependencies are no longer needed by this proof route:

- `lem-weil-pbc-etale-algebra-finite-presentation-localization`: the proof only extracts
  formal étaleness of the target factors, using Mathlib's finite-product theorem.
- `lem-weil-pbc-etale-algebra-residue-field-separable`: no separable-field decomposition
  or classification of reduced source factors is needed.
- `lem-weil-pbc-etale-algebra-over-field-product`: neither the source nor its reduction
  is decomposed.
- `lem-weil-pbc-etale-composition-cancellation`: the tensor algebra is used as an étale
  algebra over the local target, not as a composite étale algebra over R.
- `lem-weil-pbc-nakayama-jacobson`: unique pointed retractions replace the kernel argument.
- `lem-weil-pbc-etale-algebra-flat`: no finite flatness comparison is made.
- `lem-weil-pbc-finite-flat-local-free`: no freeness or split-kernel argument is made.

These seven edges are removed from the item's node. They are pruned from this argument,
not asserted to be unneeded by every other target or by every existing imported proof.
The quotient-base-change, finite-local-radical, prime-generation, base-change and unique
retraction results remain used by the local-target comparison. Product-local decomposition
and its retractions remain used through `FiniteOverHenselianLocalProduct`.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The seven-step tensor-factor proof plan is valid but longer
than necessary: 04GH makes the target factors henselian, so 04GG (8) lifts maps directly
after base change to a target factor. This changes only the argument below the node; the
unit `sk-thm-p1` and its realized statement and proof steps stay unchanged.

The local checkout contains the literature lists but not `literature/stacks-project/algebra.tex`.
The cited source results were read online at [04GG](https://stacks.math.columbia.edu/tag/04GG),
[04GH](https://stacks.math.columbia.edu/tag/04GH),
[04GK](https://stacks.math.columbia.edu/tag/04GK), and
[00UW](https://stacks.math.columbia.edu/tag/00UW). The new node explicitly marks the
local-target adaptation as written by Q1 rather than claiming it is the verbatim 04GK proof.

## New nodes

`lem-weil-pbc-henselian-local-target-etale-maps` records the proved local-target comparison
in `lean/Sheaf/RingTheory/HenselianLocalTargetEtaleMaps.lean`. It reduces the global Hom
comparison to finite henselian local targets while allowing arbitrary étale sources and
nonhenselian local base rings. Its docstring and node contain the full residue-field,
unique-retraction and tensor-adjunction argument. It is already proved, so adds no next
sorry item. No change record is required: all existing signatures, visibility, public
imports, definitions and instances are unchanged, and the new interface is in its own module.

## Second reading by Q1

1. Compared the delivered target module with the repository version. The target theorem's
   signature and visibility are unchanged; only its proof and proof imports changed. The
   added local-target module is a new declaration in a new module, with no existing
   declaration altered.
2. Compiled both delivered modules with `lcompile.py --all`; no errors or warnings occurred,
   and no `sorry`, forbidden declaration, or hollow definition occurs. The proved
   declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the new local-target statement against its residue-field lifting argument and
   edge cases (zero source and empty products). It is true with exactly the listed
   hypotheses and is strictly more general than the finite target application. Searches
   found no duplicate Mathlib or library theorem.
4. Verified the proof follows the shorter route below the unit: finite henselian product
   decomposition followed by the local-target comparison. The removed imports and seven
   removed dependency edges are listed above; the unit's `sk-thm-p1` route and realized
   steps remain intact.
5. Compared both DAG nodes with the Lean declarations. Their proof steps, dependencies,
   origins, module paths, and statements agree; the new node records its source and
   worker-authored adaptation.

Changed nothing during second reading beyond this report section; the delivered proofs and
nodes passed unchanged.
