## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_generic_fibre_hypersurface_function_field_model` with a complete
Lean reduction along the original Stacks Tag 0559 route. Its signature and visibility are
unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.FieldHypersurfaceFunctionFieldModel` and
`Sheaf.AlgebraicGeometry.GenericPolynomialHypersurfaceDescent`.

The field-only theorem isolates the separating-transcendence-basis and primitive-element
construction. The generic-polynomial descent theorem is proved completely from Mathlib.
It handles an arbitrary polynomial over the generic residue field, without assuming
irreducibility, reducedness or a function-field identification. It constructs the base
polynomial from finite-support coefficient numerators, identifies the tensor-product
quotient, and constructs the generic-fibre scheme isomorphism over the residue field.

In the descent module, four proved private helpers implement the fraction-ring structure
at the generic point, common coefficient denominators, polynomial-quotient base change,
and the affine scheme isomorphism with its projection compatibility. The parent also
proves integrality over a field and the local finite type property of the polynomial
quotient. A proved private helper transports all properties through the isomorphism and
composes the fraction-ring equivalences, verifying compatibility via
`IsFractionRing.ringEquivOfRingEquiv_algebraMap` and `Scheme.Hom.comp_appTop`.

Updated the parent node and added the two matching nodes. No definitions, existing
statements, target signatures, or other groups' modules were changed. The source read was
Stacks Tag 0559, first proof, `more-morphisms.tex`,
`lemma-geom-irreducible-generic-fibre`, the separating-generators, polynomial numerator,
and clearing-denominators paragraphs. The source was read online and its TeX downloaded
into the sandbox scratchpad. The unit `sk-prop-normal-form` and its realized route are
unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_generic_fibre_hypersurface_function_field_model`
(node `lem-sbc-generic-fibre-hypersurface-function-field-model`). Its full proof now
combines the field construction with the proved descent, integrality, finite type and
fraction-ring transport steps. The parent module and every private helper contain no
`sorry`.

Proved `AlgebraicGeometry.exists_base_hypersurface_of_generic_polynomial`
(node `lem-sbc-generic-polynomial-hypersurface-descent`), including all four private
helpers in `Sheaf.AlgebraicGeometry.GenericPolynomialHypersurfaceDescent`.
This whole module has no `sorry` and uses only Mathlib.

Added exactly one hole:
`AlgebraicGeometry.exists_field_hypersurface_function_field_model`, node
`lem-sbc-field-hypersurface-function-field-model`, in
`Sheaf.AlgebraicGeometry.FieldHypersurfaceFunctionFieldModel`, with proof exactly
`:= by sorry` and a complete source-based proof docstring.

This is a reduction: one original hole closed, one strictly narrower field-construction
hole added, net 0 before other closure effects. It does not claim an axiom-free proof of
the parent theorem. The denominator-descent part of the original plan and the complete
scheme/fraction-ring glue are proved.

## No longer needed

None of the original imports, DAG dependencies, or modules is pruned: the original node
had no stated proof dependencies and its public imports support its unchanged statement.
The new descent module exposes only `Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.Properties`, and `Mathlib.RingTheory.MvPolynomial.Basic`.
Its function-field, fraction-ring, denominator, tensor-polynomial and tensor-quotient
imports are proof-only. The field module needs the finite-type morphism import rather
than the stronger finite-presentation import.

## Where the brief, the DAG or earlier work was wrong

The original DAG's two long steps had empty `uses` lists and no formal intermediate
interfaces. The new field theorem supplies the first construction interface, and the
proved descent theorem carries the coefficient-clearing step. No existing statement
or source error was found.

Mathlib searches were run through `msearch.py` and logged in `searches.jsonl`.
LeanFinder and Loogle found fraction-ring transport and univariate denominator tools,
but no exact construction/descent theorem. LeanSearch returned HTTP 500 and is recorded
as unavailable. Further local search found `IsLocalization.exist_integer_multiples`,
`MvPolynomial.algebraTensorAlgEquiv`, `tensorQuotientEquiv`, and `pullbackSpecIso`, from
which the descent was proved. Repository searches found the original ancestor modules,
which depend on this item and cannot be imported without a cycle. Blueprint searches
for hypersurface, denominators and function field found no duplicate of either new lemma.

Small-case checks: the remaining field-construction theorem allows an extra variable
with equation T for purely transcendental extensions, including L=K. The proved descent
handles Q=0, empty support, n=0, and nonzero constants (both generic spectra are empty).
The polynomial construction is the sum over the actual finite support; multiplying by
a localization denominator yields an invertible scalar over the residue field. Thus no
nonzero-polynomial assumption or generic integrality hypothesis is needed for descent.

## New nodes

`lem-sbc-field-hypersurface-function-field-model` records the field-only separating
transcendence-basis and primitive-polynomial construction and its compatible fraction-ring
equivalence. Its one-statement module is
`lean/Sheaf/AlgebraicGeometry/FieldHypersurfaceFunctionFieldModel.lean`. This is the sole
remaining named `sorry` of the delivery.

`lem-sbc-generic-polynomial-hypersurface-descent` records the completely proved
denominator-clearing and generic-fibre isomorphism theorem for an arbitrary polynomial.
Its module is `lean/Sheaf/AlgebraicGeometry/GenericPolynomialHypersurfaceDescent.lean`.
The proof is independent of the remaining field-construction hole.

There are no change records or forced adaptations, because no existing interface changed.

## Second reading by S2

1. **Statements and accidental changes.** Compared the delivered parent module byte for byte
with the repository copy. The existing theorem signature and visibility are unchanged. The two
new declarations have signatures matching their DAG nodes; no existing definition or target was
changed. Verdict: pass.

2. **Proof checks.** Compiled all three delivered modules with `lcompile.py --all`. The parent and
descent modules contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
The sole remaining `sorry` is the named field-construction theorem, exactly as split off and
documented. Verdict: pass subject to that declared split.

3. **New statements.** The field theorem is the strict field-level construction needed by the
parent and is not a restatement of the parent. The descent theorem is independent, handles an
arbitrary polynomial (including zero and constant cases), and supplies only the generic-fibre
isomorphism needed by the parent. Repository and Mathlib searches found no duplicate declarations.
The corresponding node files include sources, proof steps, dependencies, and Lean records.
Verdict: pass.

4. **Shortest route and pruning.** The parent uses the two new interfaces, then Mathlib facts for
integrality, finite type, isomorphism transport, and fraction-ring equivalence. The unit
`sk-prop-normal-form` and its realized route remain unchanged. No old proof dependency or import
was unused; proof-only imports are marked non-public where appropriate. Verdict: pass.

5. **DAG agreement.** The parent node proof and `proof_deps` match the Lean proof, and the two new
nodes record the declarations and their split status. The report accurately records one closed
hole and one named split hole. Verdict: pass.

Changed during this second reading: added this review section to satisfy the stage-3 report
contract. No Lean code or node statements required repair.
