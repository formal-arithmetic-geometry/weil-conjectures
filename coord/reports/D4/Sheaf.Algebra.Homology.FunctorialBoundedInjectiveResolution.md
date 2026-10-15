## What changed

The target module now imports `Sheaf.Algebra.Homology.FunctorialObjectResolution` and proves
`CochainComplex.exists_functorial_bounded_injective_resolution` by composing two strictly lower
construction steps.  The first new theorem isolates normalization, recursive cokernels, zero-morphism preservation, and zero-object behavior of functorial injective resolutions of objects.  The second theorem isolates the
bicomplex totalization, first-quadrant quasi-isomorphism argument, finite diagonal injectivity,
and preservation of every lower bound.  The target statement and all its binders are unchanged.

## Proved and sorry left

The original target hole is closed at the level of a real Lean proof:
`CochainComplex.exists_functorial_bounded_injective_resolution` (node
`lem-weil-pbc-functorial-bounded-injective-resolution`).  Its proof obtains the objectwise
resolution and applies the totalization theorem with the resulting data.

Two strictly simpler public construction theorems remain as named `sorry`s:

- `CochainComplex.exists_functorial_object_injective_resolution` (node
  `lem-weil-pbc-functorial-object-resolution`), for normalization, recursive cokernels,
  exactness, zero preservation, and injectivity of the objectwise augmented complexes;
- `CochainComplex.exists_functorial_bounded_injective_resolution_of_object_resolution` (node
  `lem-weil-pbc-functorial-bounded-injective-resolution-totalization`), for totalizing supplied
  functorial object resolutions with zero preservation into one bounded-below complex functor.

No definition contains `sorry`; both remaining holes are the complete proofs of their named
public theorems.

## No longer needed

Removed the unused public import `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the target
interface is already supplied by `CochainComplexPlus`.  The imported `Sheaf.Algebra.Homology.DoubleComplexTotal` and
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation` remain necessary for the totalization theorem;
`Mathlib.Algebra.Homology.CochainComplexPlus` and
`Mathlib.CategoryTheory.Preadditive.Injective.Basic` remain necessary for the target interfaces.
The new object-resolution module uses only the cochain-complex and injective interfaces.
The proof dependency `def-weil-abstract-derived-category` and its
`Mathlib.Algebra.Homology.DerivedCategory.Basic` module are no longer needed by this route.
The import change is recorded in `coord/changes/functorial-bounded-injective-resolution-import.md`.

## Where the brief, the DAG or earlier work was wrong

The original DAG presents normalization, recursive cokernels, bicomplex totalization, and
quasi-isomorphism verification as one theorem-sized hole.  The Lean interface is valid, but a
complete proof requires these two independent construction theorems, so the node was split along
its own numbered proof steps.  No unit statement or target statement was changed, and no route
below the fixed proper-base-change unit was bypassed.

## New nodes

`lem-weil-pbc-functorial-object-resolution` records the objectwise functorial injective
resolution construction and is implemented by
`lean/Sheaf/Algebra/Homology/FunctorialObjectResolution.lean`.

`lem-weil-pbc-functorial-bounded-injective-resolution-totalization` records the totalization
construction from those objectwise resolutions and is implemented as
`CochainComplex.exists_functorial_bounded_injective_resolution_of_object_resolution` in the
item module.  No change record was needed.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and its proof is a real composition of the two strictly lower
construction statements.  The two new statements are parts of the numbered plan: objectwise
normalization/recursion and then totalization.  Their hypotheses include the zero-preservation
data required for the bicomplex identities and lower-bound vanishing.  The fixed unit route is
not bypassed.  All three delivered modules compile in dependency order, and the only changed
existing interface is the explicitly documented redundant import removal.

## Second reading by D4

1. **Signatures and accidental changes.** I compared both delivered Lean modules with the repository versions. The existing target declaration is byte-for-byte unchanged; the only existing-module edit is its proof and the removal of the unused public `DerivedCategory.Basic` import. The two added declarations are new split-off statements and their formal binders match the report and DAG nodes. Verdict: **pass**.

2. **Proof soundness and holes.** Both modules compile with `lcompile.py`. The target theorem has no `sorry`; the only remaining holes are the two named split-off construction theorems, with no `sorry` in definitions and no forbidden declarations. Verdict: **pass**, with the two documented split holes remaining.

3. **Truth and strength of split statements.** The object-resolution theorem states exactly the normalization/recursive-cokernel output needed by the target. The totalization theorem is independently parameterized by an arbitrary supplied objectwise resolution and states precisely the functor, quasi-isomorphism, injective-term, and lower-bound conclusions. Edge cases covered by the hypotheses include the zero object and empty diagonals. Searches recorded in the nodes found no existing theorem duplicating either statement. Verdict: **pass**.

4. **Pruning and route.** The target proof uses only the object-resolution theorem followed by totalization. The redundant `DerivedCategory.Basic` public import is removed, while the totalization and first-quadrant imports remain needed. The fixed proper-base-change unit route and its `realized` fields are unchanged. Verdict: **pass**.

5. **DAG agreement.** The target node proof and dependencies follow the two applications in the Lean proof. I removed the object-resolution dependency from the standalone totalization node because that theorem consumes `E` and `ε` as hypotheses and does not invoke the object-resolution declaration; its statement dependencies remain the definitions used by its interface. Verdict: **pass**.

I changed only the standalone totalization node's dependency metadata and appended this second-reading record. No Lean proof or statement required repair.
