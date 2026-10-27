## What changed

Completed the four proof bodies in `Sheaf.Paper.AdicPurityFiniteTensor` without
changing any existing declaration signature, definition body, instance, or public
import. Added private proof imports of `AdicPurityTwistRestrictionComponents` and
`AdicPurityFiniteTensorComponents`.

The restriction and realization comparisons are assembled from objectwise
normalized isomorphisms. The assembly proves naturality and uniqueness using the
module-sheafification adjunction and tensor extensionality. For realization, a
private lemma proves that the scalar-unit map is surjective on each section:
its underlying map is sheafification of an already sheaf-valued presheaf. Private
map formulas then prove the naturality square on scalar-unit pure tensors.

Exactness specializes the existing `coefficientTwistLine_exact` declaration.
Zero preservation follows from additivity of finite intrinsic realization and
of the finite twist. Updated the existing node's proof route and added a node
for each remaining component construction. No existing statement or definition
was repaired, and no consumer adaptations are needed. Both new component modules
compile, and the final item module compiles against their sandbox outputs
(`lcompile.py`, exit code 0; final item check reported 36.9 seconds).
Existing declaration signatures were also compared with the source text.

## Proved and sorry left

The original module had four holes. All four bodies are now complete:

- `WeilConjectures.adicPurityTwistRestriction_existsUnique`: decomposed into the
  objectwise construction below and a proved naturality/uniqueness argument.
- `WeilConjectures.adicPurityFiniteSheafTwist_exact`: proved by specializing
  `coefficientTwistLine_exact` to the finite first root line.
- `WeilConjectures.adicPurityFiniteTensorRealization_existsUnique`: decomposed
  into the objectwise construction below and a proved naturality/uniqueness
  argument, including sectionwise surjectivity of the realization unit.
- `WeilConjectures.adicPurityFiniteTensorComposite_zero`: proved from the two
  additive functors' map-zero formulas.

There are zero `sorry` bodies in the item module and two new named holes:

- `WeilConjectures.adicPurityTwistRestriction_component`, in
  `Sheaf.Paper.AdicPurityTwistRestrictionComponents`, node
  `lem-pur-adic-twist-restriction-components`.
- `WeilConjectures.adicPurityFiniteTensor_component`, in
  `Sheaf.Paper.AdicPurityFiniteTensorComponents`, node
  `lem-pur-adic-finite-tensor-components`.

Thus two original holes are proved from existing declarations, and two are
proper decompositions. Four old holes are replaced and two holes are added;
the textual net reduction is two. Imported declarations that already contain
holes are retained as existing stage-3 dependencies.

## No longer needed

None. The original node had no proof steps or proof dependencies to prune.
The original public import of `AdicPurityRootComparisons` remains necessary for
the statements and root normalization. Both new private imports are used.
No nodes or modules are withdrawn, and the blueprint unit route is preserved.

The searches also inspected the generic constant-scalar tensor comparison and
intrinsic tensor-comparison APIs. Neither was imported: the former uses a
different comparison interface, and the latter supplies isomorphism without
the scalar-unit section equation required here.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The item's original node had an
empty proof plan; the existing declaration docstrings supplied the construction,
local-isomorphism, and tensor-generation steps. The updated node records the
assembly actually checked by Lean. The current coefficient-twists blueprint is
the source for the two component steps; both new nodes retain the item's
adic-reconstruction blueprint ancestry.

## New nodes

`lem-pur-adic-twist-restriction-components` isolates construction and invertibility
of the normalized comparison at one module. It does not assert naturality or
uniqueness; those are proved in the item. Its proof uses the prescribed quotient
map on the root line, balanced tensors, and local triviality. Degree zero, zero
modules, zero coefficient rings, and empty schemes satisfy the same argument.

`lem-pur-adic-finite-tensor-components` isolates the normalized component comparing
intrinsic and fixed-scalar tensors at one module. It does not assert naturality
or uniqueness. Its proof uses the scalar-unit/counit identification of the line
and the two tensor/sheafification universal properties. The same constructions
apply to zero modules, zero rings, and empty test objects.

No change records: all pre-existing signatures, definitions, and public imports
are unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
