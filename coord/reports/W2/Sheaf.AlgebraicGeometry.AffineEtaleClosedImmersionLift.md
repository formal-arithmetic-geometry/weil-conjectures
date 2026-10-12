## What changed

Proved `AlgebraicGeometry.Etale.exists_affine_lift_of_closedImmersion` without changing
its signature or public imports. Added the fully proved private helper `lift_spec_quotient`.
Added proof-only imports `Mathlib.AlgebraicGeometry.Pullbacks` and
`Mathlib.RingTheory.TensorProduct.Quotient`. Updated the existing node's proof to describe
the actual ring pushout and Spec transport argument.

The ring helper uses the existing `Algebra.exists_etale_coefficientLift`, its explicit
`CoefficientLift.LiftRing`, and its specified reduction map. It verifies both base-ring
compatibilities before transporting the tensor pushout. No definition chooses arbitrary
data from an unproved existence theorem: the existential witnesses are eliminated only
inside proofs, and the lifted ring is the existing explicit construction.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_affine_lift_of_closedImmersion`
(node `lem-weil-pbc-affine-etale-closed-immersion-lift`).
No sorry remains in the delivered module. No holes or public statements were added.
The private helper is proved completely. The original dependency
`Sheaf.RingTheory.EtaleAlgebraLift`, in particular
`Algebra.exists_etale_coefficientLift`, remains an existing downstream proof obligation;
this delivery proves the scheme lifting statement from that declared ring theorem.

Local single-file compilation succeeds without warnings. The existing unit route is
preserved: the same affine lifting argument from Stacks 09ZA using 04D1 is implemented.
No additional nontriviality, nilpotence, or nonemptiness assumption is used, so the zero
quotient and empty affine source cases are covered.

## No longer needed

None. All original imports and proof-dependency nodes remain needed. The two new
proof-only Mathlib imports supply the scheme-pullback and tensor-quotient constructions.
No modules or nodes are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The existing coefficient-lift interface is sufficient:
its specified reduction identity supplies the compatibility that a bare ring equivalence
would lack. The repository's referenced Stacks TeX files are absent on this machine;
the source was checked directly at https://stacks.math.columbia.edu/tag/04D1 and
https://stacks.math.columbia.edu/tag/09ZA instead. The updated node makes the constant
and tensor compatibility calculations explicit.

## Second reading by W2

1. **Statements and source.** I read the delivered module and the node
`lem-weil-pbc-affine-etale-closed-immersion-lift`. The theorem signature is byte-for-byte
the repository signature: affine `X` and `V`, a closed immersion `i`, an étale `p`, and
the conclusion giving affine `U`, étale `q`, a map `a`, and `IsPullback a p q i`. The
docstring and node agree with Stacks Tags 09ZA and 04D1. No target or existing declaration
was weakened or given an extra hypothesis.

2. **Proof check.** The private `lift_spec_quotient` helper is fully proved and contains no
`sorry`. It applies the declared coefficient-lift construction, verifies the reduction on
constants, and transports the tensor-product pushout. The main theorem obtains the quotient
description from `IsClosedImmersion.Spec_iff`, represents the étale map by `Spec.map`, and
transports the pushout square through the affine charts. The proof compiles with no warnings.

3. **New statements and dependencies.** No public theorem or DAG node was added. The helper
is private and is not an API statement. The two plain imports are proof-only and are used by
the tensor quotient and scheme pushout calculations. Existing proof dependencies and the
unit route remain represented in the node.

4. **Edge cases and trust.** The construction does not assume nonemptiness, reducedness,
normality, or nilpotence; the zero quotient and empty affine source are included. A scratch
axiom check reports only the expected `sorryAx` inherited from the imported open theorem
`Algebra.exists_etale_coefficientLift`, together with `propext`, `Classical.choice`, and
`Quot.sound`; the delivered module itself has no `sorry`.

5. **Changes made.** I compared the sandbox module and node with the repository versions,
compiled the module with `lcompile.py`, checked line lengths and forbidden declarations, and
verified the Stacks source pages. I added this second-reading record only; no Lean statement,
definition, or proof was changed during the review.
