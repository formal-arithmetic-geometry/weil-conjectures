## What changed

Replaced the hole in `Sheaf.Paper.IntegralTensorRestrictionTransition` by a complete
categorical transport and K-flat descent argument. The public signatures, definition
of `restrictionTensor`, public imports, hypotheses and conclusion are unchanged.
The added proof imports provide K-flat resolutions, closure of K-flat complexes
under total tensor, and the two new intermediate statements. A proof-only `import all`
opens the existing private representative-comparison isomorphism and K-flat
extensionality lemmas; no shared
module is modified.

The private helpers construct the mate naturally in both inputs and prove its
component formula, then prove the diagram chase transporting an ordinary square
through representative comparisons. The final theorem uses the two intermediate
lemmas, applies transition normalization to Q and tensor(P,Q), and cancels comparison
isomorphisms. Applying the already proved `sfDerived_natTrans_ext` to the
whiskerings in each input gives the equation for arbitrary derived inputs; that
helper supplies the K-flat resolution and naturality argument. This preserves the blueprint unit route through scalar reduction
and evaluation compatibility.

Validation: the two new modules compiled cleanly in 5.1 s and 16.1 s; the item
module compiled cleanly in 27.0 s, below the 60 s limit. The unchanged direct caller
`Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition` compiled cleanly
against the replacement in 19.3 s. Its temporary sandbox copy was removed, so
it is not included in the delivery.

## Proved and sorry left

Closed the original local hole in
`WeilConjectures.IntegralHom.restrictionTensor_transition` (one of one original
holes), conditional on the following two newly stated intermediate theorems:

- `WeilConjectures.IntegralHom.ordinaryTensorQuotient_contractions`, node
  `lem-sf-integral-ordinary-tensor-quotient-contraction`.
- `WeilConjectures.IntegralHom.restrictionTensor_mate_model`, node
  `lem-sf-integral-tensor-restriction-mate-model`.

Both new theorem proofs are exactly `by sorry`, in their own modules, with source
and full natural-language argument. There are zero holes in the item module and
two added holes. This is a decomposition (one closed, two added, net minus one),
not an axiom-free proof or a reduction in the total hole count. No data definition
uses a hole. The existential contraction is used only inside the theorem proof;
its pure-section formula determines the maps. The representative isomorphism is
likewise specified by its K-flat components and naturality.

The ordinary lemma has no derived category or presentation; it isolates balanced
maps, total differentials and the quotient calculation. The mate lemma has no
consecutive transition: it identifies the one-level adjunction transpose with a
specified ordinary contraction. Neither is the original quotient square under
another name. The transport, cancellation and descent combining them are proved
in Lean in the item module.

## No longer needed

No original imports were removed, and no existing module, declaration, public
import, node or unit step is withdrawn. A redundant newly added direct proof import
of `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` was removed;
its declarations remain available through `CoefficientRingedTensorHomModel`.
The main node no longer calls the K-flat resolution theorem directly, since the
existing extensionality helper handles that step. K-flat resolution remains needed
by the mate-model lemma and the extensionality helper; its module is not pruned.
The reduction presentation and reduction tower remain needed. The route additionally uses the existing K-flat tensor-closure declaration.

## Where the brief, the DAG or earlier work was wrong

The prior disputed comment asserted that absence of an explicit interlevel
compatibility field made the theorem underdetermined. This does not establish a
counterexample: each ReductionPresentation already carries normalization on every
K-flat pair. The one-level mate calculation makes the use of that normalization
explicit; comparing the resulting ordinary contractions then supplies compatibility
without adding a hypothesis or changing any definition. The old disputed comment
is removed; no false-statement repair is claimed.

The original plan combined the ordinary contraction construction and identification
with the derived mate in one prose step. These are now separate Lean statements.
The current blueprint locates the evaluation compatibility in the second paragraph
of the integral Verdier proof, rather than the older first-paragraph shorthand.

## New nodes

`lem-sf-integral-ordinary-tensor-quotient-contraction` realizes the ordinary
balanced-tensor construction and quotient calculation from Stacks Tags 03CZ and
07A4. Its Lean module is `Sheaf.Paper.IntegralTensorQuotientContraction`.
It works for all unbounded complexes and all levels, including n=0; zero complexes
and an empty site give the zero equation. It assumes no flatness.

`lem-sf-integral-tensor-restriction-mate-model` realizes the single-level
K-flat localization and scalar-counit calculation from Stacks Tags 03CZ, 06YY and
07A4. Its Lean module is `Sheaf.Paper.IntegralTensorRestrictionMateModel`.
The first tensor factor is K-flat, ensuring tensor preserves quasi-isomorphisms;
the second factor is resolved before applying the normalization field. The
representative isomorphism depends only on the ambient tensor presentation and
first factor, not on the quotient level. Scalar sections have degree zero, so
the stated formulas introduce no extra sign. No change records are needed because
no existing interface or other existing module is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralTensorQuotientContraction": "00d752eef6ce6dc24d1f7e70c951d3ab4f2bff11", "Sheaf.Paper.IntegralTensorRestrictionMateModel": "6c746f2183e86b48a109cdaf73bd29e363de77fc", "Sheaf.Paper.IntegralTensorRestrictionTransition": "adbf90541eb512a8e163578077ee044d4dc63494"}, "results": {"Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition": {"hash": "d0a105450665f3b9d9bc2d7eb9f9df7b5e8a2157", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T12:27:28+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
