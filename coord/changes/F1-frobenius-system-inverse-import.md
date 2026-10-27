# FrobeniusSystemExchangeInverse private congruence proofs

## Reason

Native derived-category applications otherwise make kernel conversion repeatedly
unfold large sheafification and module-category instances. Private metaprograms,
adapted from FixedBaseCohomologyClassDescent, construct explicit HEq congruences.
The application helper transports each argument along a proved equality of its
type, then transports the result to the goal. All generated terms are checked by
the kernel; no axiom, unchecked code or postponed proof is introduced.

The source-level interface scanner may classify `private meta def` and local
elaborator declarations as changed commands. This record identifies those private
proof tools for independent review. There is no public signature, public import,
public definition, instance registration or target meaning change.

## Old

The private declarations `toEq`, `congrProofs`, `structuralExact`,
`repairApplication`, `evaluated_iso`, `intrinsic_tensor_evaluated_iso` and
`system_inverse_evaluation`, and the local tactic elaborators, were absent.

The public theorem `frobeniusSystemDirect_inverse_evaluation` had its unchanged
signature and proof `:= by sorry`.

## New

The public theorem has the identical signature and a complete proof. Private
`evaluated_iso` constructs a conjugated isomorphism; the intrinsic-to-tensor
helper calculates its hom using the forward compatibility equation and computes
its inverse. `system_inverse_evaluation` instantiates this calculation for the
specified operations; the public theorem specializes it to geometric Frobenius.

Private `toEq`, `congrProofs`, `structuralExact` and `repairApplication` construct
ordinary equality and heterogeneous equality proof terms. The local tactics are
`frobenius_structural_exact` and `frobenius_repair_exact`. Their complete code is
in the delivered module. They do not introduce mathematical assumptions.

Existing isomorphism proofs also select the standard derived-category instance
locally. Removal of the two competing semilinear instances is scoped with `in`
to individual proof commands; these attributes are preserved for importers.

## Users

Read-only `tools/downstream.py --direct --uses` and source search found the
following direct consumer. None of the private helpers is used outside this file.
The public theorem is not yet mentioned by another Lean source.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same public declarations and attributes; no adaptation. |

## Status

landed 20261026T065558-L-3095760 2026-10-26 (merge of deliver/F1/Sheaf.Paper.FrobeniusSystemExchangeInverse)
