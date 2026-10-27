## What changed

Reduced `existsUnique_finiteTensorSheafProducts`, with its complete original statement,
to three proper sheaf arguments. `exists_finiteTensorSheafProductMap` constructs only
a morphism, `finiteTensorSheafProductMap_isIso` recognizes local invertibility of any
normalized morphism, and `finiteTensorSheafProduct_frame_ext` detects equality of any
two tensor maps to a signed line, without normalization or invertibility assumptions.
The item chooses the pairwise maps inside its theorem proof, supplies their IsIso
instances, constructs the family with asIso, and proves uniqueness by function and
isomorphism extensionality and the two normalization equations. There is no arbitrary
new data definition or same-statement replacement.

Relocated `FiniteTensorLineFrame`, `FiniteTensorFrame`, `finiteTensorFrameBasis`,
`finiteTensorSection`, and `finiteTensorSectionTmul` verbatim to the frame-detection
module. Its public import from the item preserves their names and definitions for
all consumers and avoids an import cycle. The two other new modules are proof-only
imports. The derived product proof and its flatness helper are unchanged.

Validation: lcompile.py compiled the three new modules and the original item.
After replacing the proof-local letI with let, the item compiled without warnings.
Five direct consumers compiled against the changed item. The sixth,
`FiniteRootTensorPresentation`, exceeded 60 seconds; the unchanged baseline also
exceeded the limit (96 seconds). Profiling the changed version reported 67 seconds,
with kernel checking of its existing positive-presentation theorem and definition
accounting for approximately 54 seconds. No consumer adaptation is included.
The temporary consumer and baseline copies were removed from the delivery.
All original declaration signatures and the five relocated defining bodies were
compared programmatically and are unchanged. DAG signatures match their Lean
statements, and each proof_deps list is exactly the union of its proof-step uses.

Change record: `coord/changes/V4-finite-signed-frame-foundation.md`.

## Proved and sorry left

Original item: one direct hole, in
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSheafProducts`
(node `def-pur-finite-signed-twist-products`). It is closed by a compiling combination
of the following three strictly separate steps, which remain direct holes:

- `WeilConjectures.PurityFiniteSetting.exists_finiteTensorSheafProductMap`
  (`lem-pur-finite-tensor-product-map`): existence of a normalized morphism for one pair.
- `WeilConjectures.PurityFiniteSetting.finiteTensorSheafProductMap_isIso`
  (`lem-pur-finite-tensor-product-map-isIso`): conditional local invertibility.
- `WeilConjectures.PurityFiniteSetting.finiteTensorSheafProduct_frame_ext`
  (`lem-pur-finite-tensor-product-frame-ext`): equality detection for arbitrary maps.

This is a decomposition, not a net proof: one upper hole closed, three lower holes
added; net minus two. There are zero direct holes left in the original item module.
The previously completed `existsUnique_finiteTensorProducts` stays complete.
Every new hole is the whole proof of a named public theorem, with its source and
full argument in its docstring and matching node. No definition contains a hole.

## No longer needed

None of the original nodes or modules is withdrawn. No existing public import is
removed. The old DAG's unsplit ordinary frame-gluing step is replaced by the three
explicit local arguments above; the derived flatness and single-complex dependencies
remain needed. Every new import is used by the item proof or its public definitions.

## Where the brief, the DAG or earlier work was wrong

The current source already has the F5 proof of the derived product theorem, so only
one direct hole remained, in the ordinary product theorem. The original ordinary
DAG step was a narrative, not a theorem that could be applied. Its required content
is now separated into construction, invertibility, and equality detection, rather
than assuming any one of these properties of a putative product family.

The three new statements were checked on zero degrees, opposite signs, positive
and negative pairs, zero rings and empty site objects. Tensor bases and evaluation
duals give their local arguments without assuming the first line globally trivial.
The ordinary morphism construction asserts neither IsIso nor uniqueness; the IsIso
criterion assumes no existence or uniqueness theorem; the extensionality theorem
applies to arbitrary morphisms without a prescribed sum-degree value. The unit route
is unchanged; all three steps expand the invertible-twist clause of finite reduction.

## New nodes

`lem-pur-finite-tensor-product-map`, in `FiniteTensorProductMap`, isolates gluing the
local balanced multiplication rules. Its map is not selected in any new definition.

`lem-pur-finite-tensor-product-map-isIso`, in `FiniteTensorProductMapIsIso`, isolates
the basis criterion and gluing the local inverses of a given morphism.

`lem-pur-finite-tensor-product-frame-ext`, in `FiniteTensorProductFrameExt`, isolates
local generation and separatedness for tensor maps to any signed degree. This module
also owns the five unchanged foundational declarations moved out of the item.

All three cite the latest blueprint finite-reduction proof Step 2 and the Stacks
Modules on Sites tensor-product/invertible sections. Searches included LeanSearch,
LeanFinder, Loogle, Mathlib grep, the source and project libraries, and the complete
blueprint index. `NormalizedSignedTensorPowers` supplies a categorical family but no
sectionwise coherent-frame normalization; `SignedLineOrdinaryConstraints` supplies
successor products and evaluation, not arbitrary signed products; the existing
positive chart detector concerns only a positive single line and imports this item.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
