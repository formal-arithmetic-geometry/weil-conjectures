## What changed

Reduced `WeilConjectures.PointSignedCyclotomicAction.point_signed_cyclotomic_action`
to two strict subarguments, with the original statement and all definition bodies unchanged.
The assembly computes the finite root action from the adjunct projection formula, proves
transition compatibility from naturality, and obtains the q unit and inverse exponent from
`FiniteFieldDatum.frobenius_rootsOfUnity_power`. Coefficient factors fix 1 by `map_one`.

The scalar sublemma gives the action on one arbitrary signed section. The assembly proves
its scaled-section consequence using scalar associativity, degree zero, tensor compatibility
using tensor bilinearity, invariance of the dual pairing using inverse powers, bijectivity
using the explicit inverse scalar, the invFun dual formula, and the normalized dual value.
Thus the original conjunction is assembled by actual Lean proofs, not copied into a new hole.

Extracted the existing data declarations verbatim into
`Sheaf.Paper.PointSignedCyclotomicActionData`, publicly reexported by the original module,
so the new theorem modules can use those definitions without an import cycle.
The change record is `coord/changes/A3-point-cyclotomic-data-extraction.md`.
The original module's public prerequisites remain. Only proof imports are pruned.

All four modules compiled with the server sandbox compiler (`lcompile.py --all`).
The primitivity hypothesis is explicitly discarded in the final proof; its name and
statement remain unchanged. Delivery preflight provides the final validation.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.PointSignedCyclotomicAction.point_signed_cyclotomic_action`
(node `lem-pur-point-signed-cyclotomic-action`) by reduction.

Added two named theorem holes, one per new module:

- `WeilConjectures.PointSignedCyclotomicAction.root_limit_cyclotomic_action`
  (`lem-pur-point-root-limit-cyclotomic-action`): inverse-limit root action only.
- `WeilConjectures.PointSignedCyclotomicAction.signed_section_scalar`
  (`lem-pur-point-signed-section-scalar`): one signed-section scalar formula only.

The item module has zero direct sorries; the data module has zero. The delivery adds two.
This is a decomposition of one hole into two strictly smaller true statements, not a
net proof-closure claim. Each new statement has its source and complete proof in words.
All private helpers are proved. No axiom or hollow definition is added.

## No longer needed

The parent no longer directly needs `lem-pur-point-tate-root-coordinates`,
`lem-weil-point-automorphism-restriction-natural`, `def-weil-constant-weil-structure`,
or `lem-pur-isomorphism-inverse-image-tensor-hom` for its assembly: the first three
remain needed in the signed-scalar subargument, and the tensor/Hom compatibility is
used there to justify its normalization. They are not claimed globally pruned.
The historical tool-use entry for the point-automorphism restriction lemma is retained;
that lemma remains cited in the scalar subargument. No module is withdrawn.

Removed unused private imports from the parent:
`Sheaf.Paper.PointAutomorphismRestrictionNatural`,
`Mathlib.CategoryTheory.Limits.HasLimits`, `Sheaf.Paper.ConstantWeilStructure`,
`Sheaf.Paper.PurInverseImageTensorHom`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
The data module retains only the original public prerequisites; no private proof
imports were copied into it. The tensor/Hom APIs used in the proof remain available
through the retained public statement prerequisites.

No unit-level route is bypassed. The current `sk-def-purity-conv` unit has empty
realized statement/steps and remains unchanged. The source-based route still passes
through root actions, completion, coefficient extension, positive tensors and duals.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The original primitivity hypothesis on e is
unnecessary for the assembled consequences but is retained verbatim. The root-limit
sublemma applies to every compatible root section, as is required by the root action
being multiplication by a scalar; the scalar sublemma is independent of any generator.

Read Deligne I (2.2), pp. 280--281: root transition is the l-th power, arithmetic
Frobenius acts by q, and negative twists are duals. The geometric inverse convention
makes the scalar q inverse. Checked degree 0, degree +/-1, b=0, l=2, quotient exponent
1, and ramified/nonreduced finite quotients: all arguments use units and bilinearity,
never cancellation of an arbitrary nonunit or an assumption that sections preserve
general tensor products. The latter is avoided by applying the tensor's defining
sectionwise bilinear map only.

## New nodes

`def-pur-point-cyclotomic-section-data` records the attachment migration of the sixteen
existing data declarations into the publicly reexported data module. It introduces
no new construction, statement repair, or hole. Its formulas and bodies are unchanged.


`lem-pur-point-root-limit-cyclotomic-action` isolates the root sheaf inverse-limit
calculation. Its proof compares root projections using the canonical root comparison,
then the existing cyclotomic Tate-module scalar theorem and the specified completed
action. Its statement neither chooses a generator nor assumes primitivity.

`lem-pur-point-signed-section-scalar` isolates coefficient extension, positive powers
and negative duals for one section. It uses the root-limit lemma, existing point-root
coordinates and the canonical positive/signed normalization declarations. Its statement
omits the finite root clauses, the inverse-limit clause, coefficient-factor clauses,
tensor/evaluation/inverse-dual assertions and normalized-dual assertion of the original.

Searched the current blueprint for cyclotomic scalar, root limit, signed point and
cyclotomic action, and searched the project declarations and Mathlib with LeanFinder,
Loogle, LeanSearch and grep. No existing declaration states either specified sheaf
composite. General field cyclotomic character results do not supply these comparisons.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
