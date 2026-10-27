## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_quotient_comparison`
without changing its statement. Private helpers construct the constant/discrete abelian
comparison, prove that it respects multiplication, reconstruct its section-ring comparison,
and prove naturality for arbitrary coefficient homomorphisms. The comparison is transported
to the coefficient-sized site. The universe-lift quotient equivalence and its formula on
quotient generators then give the required commutative square.

Proof imports use the existing monoidal constant-sheaf comparison and the proved private
section-ring construction and normalization helpers of
`Sheaf.Paper.AdmissibleScalarRealizationExact` via `import all`. The main admissible-scalar
assertion, Noetherianity, finiteness, and topology hypotheses are not used.
No public definition, instance, signature, or import was changed. The helper import
adds no modules or holes to the existing targets import closure (checked from source).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.discrete_quotient_comparison`
(node `lem-sfb-internal-discrete-quotient-comparison`).
Added zero holes; split off zero statements; no `sorry` remains in the delivered module.
All private helper theorems are proved.

Validation: the server compiled the complete module cleanly in 11.8 seconds.
The public theorem signature is byte-for-byte unchanged; no `sorry` remains.
The delivery tool runs the required preflight and axiom checks before pushing.

## No longer needed

No original imports or declared dependencies were removed. The proof follows all three
steps of the existing node. No new nodes or modules are required. No upstream declaration
or unit route is bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Existing private helpers already supply the
constant-abelian-to-section-ring construction, its normalization, and reflection of
invertibility; these can be reused for arbitrary discrete coefficient rings.

Searches: LeanFinder on inverse image of constant ring sheaves found general sheaf
forgetful comparisons, but no exact theorem. Loogle found `Ideal.quotientEquiv` and its
formula on quotient generators. Mathlib grep and searches in both project roots found
`constantCommuteCompose`, `constantSchemeIso`,
`Equivalence.constantSheafSheafCongrIso`, and the section-ring helpers used in the proof.
The zero ring, the ideals zero and top, and the empty scheme require no separate cases:
all comparisons are natural isomorphisms and the quotient calculation is on arbitrary
representatives, with no nonemptiness or nontriviality assumption.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
