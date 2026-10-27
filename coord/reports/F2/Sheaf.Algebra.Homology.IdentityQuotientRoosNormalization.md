## What changed

Proved `CategoryTheory.PrincipalQuotientCompletion.identityQuotientRoosNormalization`
without changing its signature or docstring. The proof establishes degreewise epimorphy
of the quotient maps, cancels their scalar-extension images, checks each product
projection, and checks both signed Roos cone coordinates. At exponent one the block
map equals selection; explicit index transports avoid identifying differently
presented products by unfolding their limit constructions.

Added proved private helpers only. Added proof imports of
`TensorColimitsIndependentCoefficients`, `Mathlib.CategoryTheory.Limits.Constructions.EpiMono`,
and `import all PrincipalQuotientCompletionExists`, reusing its already proved private
`quotient_natural` and `tensorUnit_eq` rather than duplicating their proofs. Updated
the existing node's proof and proof dependencies to record this reuse. All existing
public imports and declarations remain unchanged.

Validation: the whole item compiles through lcompile.py. A direct `#print axioms`
check reports only `propext`, `Classical.choice`, and `Quot.sound`. The tensor argument
uses no flatness or regularity hypothesis and applies to all unbounded complexes,
including zero objects and zero coefficient rings. No extra public declaration,
definition repair, or consumer adaptation is needed.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.PrincipalQuotientCompletion.identityQuotientRoosNormalization`
(node `lem-pur-identity-quotient-roos-normalization`).

Added 0 holes; split off 0 statements. No sorry remains in the item or is added
elsewhere. Every private helper is proved, and the final theorem's axiom closure
contains no sorry axiom.

## No longer needed

None. All original declared dependencies remain needed. No original import,
module, node, or unit step is pruned. The additional naturality dependency is an
already proved part of `lem-pur-principal-quotient-completion-exists`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original plan's assertion
that the arithmetic map becomes identity is unnecessary: proving block equals
selection and retaining the index transport suffices. The node now records the
actual argument and the existing naturality lemma it uses.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
