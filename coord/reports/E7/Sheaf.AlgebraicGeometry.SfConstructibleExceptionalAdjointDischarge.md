## What changed

Replaced the admitted proof body with a complete compiling proof for
`AlgebraicGeometry.ProEtale.sfConstructibleExceptionalAdjointDischarge`.
The theorem statement, its public imports, and all existing definitions are unchanged.
The private helpers construct the transported counit at the specified compactification,
prove its naturality, and prove the Hom bijection first on bounded-below etale
representatives and then by transport along the essential-image isomorphism.
The first conjunct follows by transporting proper direct-image vanishing through
comparison isomorphisms, including the prescribed pro-etale base changes.

The proof imports `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction` directly
for its canonical fixed compact-support comparison. The existing node
`cor-sf-ambient-adjoint-discharge` now records the proof and its actual dependencies.
There are no new modules or statements with admissions and no interface adaptations.
The local helper context is documented in
`coord/changes/E7-fixed-discharge-private-proof-context.md` as required by preflight.

The resumed required dry run compiled and passed server preflight on 2026-10-19
(dry-run commit `2aee00dfac`). The proof was checked against current shared sources:
the original theorem signature and public imports are verbatim unchanged; the file
has zero `sorry` tokens and no lines over 100 characters. Only `proof`, `proof_deps`
and `proof_origin` change in the node, and its dependency list is exactly the union
of the proof-step dependencies. The delivery is CODEX for independent review.

The earlier attempt reported missing compile-server responses after successful
dry runs. The current required compile gate succeeds with the retained proof;
no definition repair or timeout-limit change is needed to pass it. A separate
`lcompile.py` check also passed without diagnostics in 14.2 seconds. The change
record's transitive-user table was refreshed against the current sources.

## Proved and sorry left

The sole original admitted proof is replaced:
`AlgebraicGeometry.ProEtale.sfConstructibleExceptionalAdjointDischarge`
(node `cor-sf-ambient-adjoint-discharge`).
Holes closed: 1. Holes added: 0. Actual remaining holes: 0.
The proof is compiler-verified from the imported declarations; this does not claim
that their transitive dependencies are free of admissions.
The private adjunction, counit, naturality, comparison computation, and two
bijectivity helpers have complete bodies without admissions.

## No longer needed

Removed these original direct proof imports:

- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`;
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`;
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`;
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`;
- `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`
  (available through the direct fixed-comparison import).

The proof needs the fixed comparison and ordinary etale adjunction rather than the
larger specified-adjoint package or the unrestricted ambient-admissibility notions.
The latter two definitions (`def-weil-ambient-exceptional-adjoint` and
`def-weil-exceptional-adjoint-admissibility`) are removed from `proof_deps`;
the node's original statement dependencies remain unchanged. No global withdrawal
of these modules or nodes is claimed. Both `thm-sf-fullcd-class` and
`thm-sf-ambient-adjoint-class` remain dependencies: their underlying comparison
arguments and canonical maps are used, with the unit's Hom chain preserved.

## Where the brief, the DAG or earlier work was wrong

The published FullCD theorem has an unused invertible-exponent hypothesis.
The proof uses its underlying proper etale vanishing theorem directly, followed
by the same comparison argument, so no additional hypothesis or instance is needed.
The relative counit is constructed from canonical maps; no arbitrary Hom equivalence
is selected from existence and no unrestricted ambient adjunction is asserted.
The retained sandbox lacked the node update for this explicit counit route; this
delivery supplies it.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
