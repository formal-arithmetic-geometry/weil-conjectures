## What changed

Preserved the archived item and its complete public statement, including all nine
ordinary/pro-etale quotient cocycles and the literal pro-etale scalar associator. The
checkout restored this item and its dependencies during the session; the sandbox follows
that same source. No archive is deleted and no declaration is withdrawn.

Proved the ordinary pullback cocycle in the item using the existing private
`AlgebraicGeometry.Etale.scalarPullback_chain` from
`Sheaf.Paper.FiniteCoefficientDirectImage`, imported only for the proof. A private helper
inverts its equality of canonical isomorphisms and cancels the scalar associator. The
quotient specialization proves the ring-map composition equality explicitly. This includes
identity quotients and does not need smoothness.

Proved ordinary compact-support coherence in a new module by conjugate pasting of the
existing restriction/pullback coefficient chain, inversion of the open comparison cocycle,
and the existing direct-image coefficient-chain theorem. Naturality pastes the open and
direct-image formulas on the chosen compactification. Reduced the other assertions to two
proper steps: ordinary root-tensor and twisted-source coherence, conditional on the proved
pullback cocycle; and pro-etale transport, conditional on the five ordinary cocycles. The
ordinary exceptional cocycle supplied to transport is obtained by applying the existing
`exceptional_naturality_and_cocycle` to the compact-support cocycle, with the intermediate
positive-index bound proved by transitivity. The parent theorem combines these steps in
Lean. Its DAG proof and dependencies now match that argument. No existing interface or
definition changes.

## Proved and sorry left

Original item: one hole, in
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothQuotientCoherence`. That hole is
closed by a compiling reduction. The private `pullback_chain` helper and the
literal-quotient specialization are proved without new holes. The ordinary
exceptional-mate glue is complete and reuses the existing theorem.

Two new holes remain, each the whole proof of one public theorem in a new module with its
own source, complete proof in words, and DAG node:

- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothOrdinaryTwistedCocycles`:
  `lem-pur-finite-smooth-ordinary-twisted-cocycles`.
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothProQuotientTransport`:
  `lem-pur-finite-smooth-pro-quotient-transport`.

The new `finiteSmoothCompactQuotientCocycle` theorem and its private `open_chain_inverse`,
`open_chain`, `proper_chain`, and `compact_chain` helpers are proved with no new holes.

Counts: one old hole closed; two holes added; two holes in this delivery. This is a
decomposition with proved ordinary pullback and compact-support constituents, not a proof
of the complete nine-cocycle package without remaining obligations. The new statements
omit entire parts of the original conclusion; none is the original theorem with its
hypotheses repackaged.

## No longer needed

No original public import is removed: `FiniteSmoothAdjunctionData` is preserved. The
following original planned dependencies are not used directly by the parent proof and are
replaced by the three more precise subarguments: `lem-weil-pbc-comparison-pullback` /
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` /
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`lem-asd-etale-finite-twist-pullback` /
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`, `lem-amb-proper-coproducts-projection`
/ `Sheaf.AlgebraicGeometry.ProperProjectionFormula`,
`lem-weil-pbc-extension-by-zero-stalks` /
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`, and
`lem-weil-pbc-extension-by-zero-exact` /
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`. The site-comparison,
tensor, twist, and open-extension dependencies remain in the appropriate new nodes' plans
or in the retained statement-import closure. This delivery does not claim those modules
are globally unnecessary or withdraw any of them. No unit statement or realized unit step
is bypassed.

`lem-pur-exceptional-coefficient-comparison` remains directly used. The new direct
dependency `lem-coef-finite-direct-image` supplies the proved scalar pullback
coefficient-chain identity, avoiding a new obligation for that identity. This is a use of
its general coefficient-chain identities as categorical tools: the smooth-purity unit does
not restate these already-proved direct-image and restriction comparison identities.

## Where the brief, the DAG or earlier work was wrong

The assigned source was initially absent from `lean/`, as recorded by its current rework
row. It was recovered from the exact quarantine path; during inspection the shared
checkout restored that source and its dependencies. Absence was not treated as
authorization to withdraw it.

The original DAG collected all nine cocycles in one proof step and did not record the
reusable scalar-pullback coefficient-chain proof. The updated route records that reuse and
isolates two genuine remaining parts and proves the compact-support starting step. The
existing exceptional comparison theorem assumes compact-support coherence, so it cannot
itself supply the first conclusion; the compact-support step is proved independently in
this delivery. The new compact-support proof plan uses injectivity of adjunction Hom
equivalences, not faithfulness of restriction on derived categories.

## New nodes

`lem-pur-finite-smooth-compact-quotient-cocycle`, module
`Sheaf.Paper.FiniteSmoothCompactQuotientCocycle`: only the ordinary compact-support
starting cocycle. Its complete proof expands the chosen open/proper compactification and
pastes the two counit/unit coefficient diagrams, reusing the existing direct-image and
restriction/pullback coefficient-chain proofs. It does not involve twists, exceptional
purity, or pro-etale transport.

`lem-pur-finite-smooth-ordinary-twisted-cocycles`, module
`Sheaf.Paper.FiniteSmoothOrdinaryTwistedCocycles`: root-generator normalization, ordered
tensor-power induction, and pasting with the ordinary pullback cocycle. The statement
keeps the original finite smooth hypotheses and asserts only the ordinary twist and
purity-source conclusions.

`lem-pur-finite-smooth-pro-quotient-transport`, module
`Sheaf.Paper.FiniteSmoothProQuotientTransport`: only transport of the five supplied
ordinary cocycles to the five specified pro-etale comparisons. The plan explicitly uses
the actual origin counits, intrinsic constructible finite-Tor domains, and inverse
site-comparison cancellation. The ordinary exceptional hypothesis is supplied by a
separate existing theorem in the parent proof.

Each new node cites the existing blueprint compatibility proof and records leansearch,
leanfinder, loogle, grep, and blueprint searches. Equal indices, d=0, empty schemes, and
zero inputs satisfy the same categorical diagrams; no strict inequality, nonempty scheme,
choice of roots, or chosen origin is assumed. No definition is changed, so no change
record is needed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
