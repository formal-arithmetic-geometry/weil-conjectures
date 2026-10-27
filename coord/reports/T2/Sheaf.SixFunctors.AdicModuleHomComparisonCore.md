## What changed

Proved `AlgebraicGeometry.ProEtale.adicModuleHomComparisonCore` with its statement and
record fields unchanged. The comparison is the slice-Hom curry of the inverse normalized
tensor comparison followed by the image of the native tensor-Hom counit. Full faithfulness,
essential surjectivity, and the two tensor-Hom bijections prove that it is an isomorphism.
The proof derives naturality in both variables from native evaluation naturality, and
obtains the evaluation and bidual formulas by evaluating on local pure tensors.

Added `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorHomEquiv`: a fully constructed
presheaf currying equivalence, composed with module sheafification to give the equivalence
for the existing `siteSheafTensorRight`. Its further-slice formula and naturality in the
first tensor factor are proved. No existing tensor, Hom, action, or equivalence definition
changes. The item adds only private proof imports and private helpers. No other existing
Lean module changes.

Validation: the remote import-order compile passed without errors or warnings. The new
currying module compiled in 15.1 seconds and the item in 34.1 seconds. Every delivered
Lean line is at most 100 characters; both files contain zero textual `sorry`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.adicModuleHomComparisonCore`
(node `lem-sf-adic-module-hom-comparison-core`).

Added no holes and split off no obligations. Both delivered modules contain zero `sorry`.
The proof uses the previously stated `adicModuleTensorComparisonCore`; that existing
obligation is not duplicated or changed by this delivery.

## No longer needed

The planned proof dependency `det-sp-unique-right-adjoint` is unnecessary: the explicit
comparison induces bijections on all Hom sets, so Yoneda proves its invertibility directly.
Its Mathlib right-adjoint-uniqueness API is not imported for this proof.

No original public import is removed: the section-comparison declarations and native bidual
are needed in the unchanged public signatures. No other node or module is withdrawn.
The normalized tensor-comparison core remains necessary, both here and in the parent
comparison's tensor fields.

## Where the brief, the DAG or earlier work was wrong

The listed Hom and unique-right-adjoint declarations do not by themselves supply currying
for the independent-universe tensor model used by the adic comparison. The source
`SheafOfModules.tensorHomEquiv` and `PresheafOfModules.homObjEquiv` require the object,
morphism, coefficient and module universes to agree. The new proved API supplies exactly
the bridge to the existing `siteSheafTensorRight` model, without altering the source API.

The source was read at `sites-modules.tex`, Section Internal Hom and
`lemma-internal-hom-adjoint-tensor` (03EO). LeanSearch, LeanFinder, Loogle and local grep
found the sheafification and generic adjunction ingredients, but no suitable existing
comparison. The unit statement and its realized steps are retained.

## New nodes

`lem-sf-site-tensor-hom-equiv` records the proved currying equivalence for the independent-
universe sectionwise tensor, its formula on every further slice, and naturality in the
first factor. Source: Stacks 03EO and the slice-Hom definition of Section 04TT. The node
records LeanSearch, LeanFinder and grep searches; it introduces no unproved statement.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
