## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent` with the principal-open
localization argument. Its existing theorem signature and public imports are unchanged.
The proof uses the existing affine exterior sheafification-unit bijectivity theorem,
the upstream localization theorem for sections of a quasi-coherent module, and the
upstream principal-open quasi-coherence criterion. It explicitly transports the
extending-power and killing-power conditions through the unit using its naturality
and linearity.

Added two fully proved dependency modules. `Sheaf.LinearAlgebra.GenericExteriorPowerLocalization`
proves the algebraic localization statement characterized on pure wedges.
It constructs fraction-surjectivity by span induction and proves invertibility of
denominator actions. `Sheaf.LinearAlgebra.ExteriorLocalizationKernelTorsion`
proves the remaining kernel criterion by extending alternating maps through module
localization and constructing a left inverse after localization.
Its statement covers arbitrary multiplicative subsets, degrees, coefficient rings,
and modules; it has no scheme or quasi-coherence hypothesis. Updated the item's DAG
proof and dependency list to match this route. All added imports in the item are
ordinary proof imports.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine`
(node `new-q1-exterior-sheaf-quasicoherent`). No sorry remains in the item's module.

Also proved `exteriorPower.isLocalizedModule_of_pure_wedge`
(node `new-v2-generic-exterior-power-localization`) and
`exteriorPower.exists_smul_eq_zero_of_localized_wedge`
(node `new-v2-exterior-localization-kernel-torsion`).
All private helper declarations are fully proved. `localizedWedge_surj` clears
denominators in pure wedges and then handles sums and A-scalars by span induction.
`extendMulti`, `extendMulti_apply`, `extendMulti_alt`, and `extendAlt` construct and
verify the alternating extension used in the kernel argument. There is no new hole,
no split-off sorry, and no sorry in any delivered module: one original hole closed,
zero holes added, net one hole removed. The item uses the existing theorem
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_affine_unit_bijective`
(node `new-q1-exterior-sheaf-affine-unit-bijective`), which this delivery does not change.
That theorem was proved concurrently and still depends on the existing categorical
exterior-localization and affine-localizing sheafification lemmas. Those existing
holes are unchanged by this delivery; the new algebraic theorems have only the
three permitted axioms. The original theorem retains the dependencies' existing
sorry axioms, as expected for a stage-3 proof from named statements.

The degree-zero and degree-one algebraic specializations were independently proved
and compiled in the scratchpad using zeroEquiv/oneEquiv and the existing localization
API. Further edge cases of the new kernel statement were checked mathematically: n=0 is the
ring localization map; n=1 is the given module localization; M=0 gives the zero
positive exterior powers; 0 in S forces A and N and their exterior powers to be zero.
The fraction construction never assumes injectivity of the localization map, so
it includes modules with torsion and rings with zero divisors. No inverse to 2 is
used, and characteristic 2 is included.

## No longer needed

None globally pruned. No original public import was removed. The original direct
proof dependencies `lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-spec-module-tilde-sections` are replaced by the more precise section
localization, affine-unit, and principal-open-criterion nodes. Those original
nodes remain needed transitively through the existing lemmas; they must not be
removed from the project. The proof does not construct a separate affine
comparison isomorphism or a new sheafification criterion.

## Where the brief, the DAG or earlier work was wrong

The original plan's step 2 combines the algebraic exterior-localization argument,
compatibility of restrictions, and sheafification. The existing
`ExteriorSheafAffineUnit` module already supplies the affine-unit component, so a
second statement of that component would be duplicate work. The algebraic localization component, including its kernel-torsion criterion,
is now fully proved.
The module works with the same statement, without definition or interface changes.
The proof uses the explicit CategoryStruct.id in place of the identity notation:
a proof-only import of the newly published affine-unit file made the notation
elaborator unavailable, while the explicit identity compiles cleanly.
The argument actually works on all schemes, but the original IsAffine binder is
retained unchanged.

The algebraic source is Stacks Tag 0C6F, Lemma 10.13.6, linked from the original
Tag 01I6 proof of Lemma 26.7.2(2). The public Stacks page was read directly; its
omitted proof is expanded in the new node and docstring using the alternating
universal property. The local repository has no Stacks .tex files. WANTED:
`literature/stacks-project/algebra.tex`, lemma 0C6F, for
`new-v2-generic-exterior-power-localization` (the online source is available).
LeanSearch returned Internal Server Error; that search is recorded as unavailable.
Loogle, LeanFinder, local Mathlib/source searches, and whole-blueprint searches
found no equivalent localization theorem. The Clifford-algebra base-change theorem
requires invertibility of 2, so it cannot cover this statement.

The existing created.item fields contain Lean module names, so
`blueprint_refs.py ancestor new-q1-exterior-sheaf-quasicoherent` returns None.
Following the existing explicit blueprint.from chain instead reaches the imported
`lem-sc-finite-duality` node; the new node records that ancestry and identifies the
precise downstream exterior-localization step it serves. No unit statement or
realized step was changed.

## New nodes

A categorical specialization named `new-v2-exterior-power-localization` landed
concurrently from the affine-unit item during this work. It is
unchanged here. This delivery uses its own fully proved generic statement with
independent universes and arbitrary modules, named distinctly to avoid any
change to that existing signature.

`new-v2-generic-exterior-power-localization`, in
`dag/nodes/sec-picard-framework/new-v2-generic-exterior-power-localization.json`, states and proves
that a linear map on nth exterior powers characterized on pure wedges is a
localization whenever the coefficient ring and underlying module map are
localizations. Its Lean declaration is
`exteriorPower.isLocalizedModule_of_pure_wedge`, in
`lean/Sheaf/LinearAlgebra/GenericExteriorPowerLocalization.lean`. This is strictly the
algebraic localization component of the original proof, independent of the
sheafification component supplied by an existing node.

`new-v2-exterior-localization-kernel-torsion`, in
`dag/nodes/sec-picard-framework/new-v2-exterior-localization-kernel-torsion.json`,
proves that the kernel of the induced exterior map consists of elements
annihilated by a denominator. Its declaration
`exteriorPower.exists_smul_eq_zero_of_localized_wedge` is in
`lean/Sheaf/LinearAlgebra/ExteriorLocalizationKernelTorsion.lean`. The proof extends multilinear maps by induction using currying, proves alternation
by clearing denominators, and obtains a left inverse by the exterior universal
property. This is strictly a part of the algebraic argument, and is fully proved.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by V2

1. I compared the delivered item module with the repository version. The theorem signature and all existing declaration statements are unchanged; only the proof and proof-only imports differ. Verdict: pass.

2. I compiled the item and both added modules with `lcompile.py`. They compile without errors or warnings, and no delivered file contains `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proofs use only the permitted kernel axioms (apart from imported open theorems named in the report). Verdict: pass.

3. The two split-off statements are strict algebraic sublemmas: localization of exterior powers and the localized-wedge kernel torsion criterion. Their edge cases include degrees zero and one, zero modules, zero rings, and torsion; their docstrings give the complete construction and source, and matching DAG nodes are present. No duplicate library theorem was found by the recorded searches. Verdict: pass.

4. The proof follows the affine principal-open route, using the existing affine sheafification-unit theorem and the principal-open criterion. The two new algebraic modules are needed by the route; no removable import or proof dependency was found. Verdict: pass.

5. The DAG proof steps, `proof_deps`, `proof_origin`, and unit route agree with the Lean proof. The existing unit realization is unchanged, and the new nodes record their modules and declarations. Verdict: pass.

I changed only this report section during second reading; no Lean code or DAG statements were changed.
