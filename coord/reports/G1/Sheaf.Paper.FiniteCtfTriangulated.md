## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finite_ctf_isTriangulated` by a proof of all four
clauses with its signature unchanged. Construct an exact tensor functor from a K-flat resolution
of each degree-zero test sheaf, compare it with every presentation in the Tor-amplitude
definition, then use homology shifts and the exact homology segment for distinguished triangles.
Intersect the resulting finite-amplitude property with the existing bounded-constructible one.

The proof-only `import all Sheaf.Algebra.Homology.KFlatResolutionGeneral` reuses that module's
already proved private closed tensor, additivity, Grothendieck and functorial flat resolution
constructions. These appear only in a private theorem proof. No public definition is added,
no private data enters a public signature or definition, and no other module is changed.

The notation-scope commands required a static interface change record,
`coord/changes/finite-ctf-proof-scopes.md`. The downstream check reports zero consumer modules,
so no adaptations are needed. No target statement or definition changes meaning.

The node proof and proof dependencies follow this route. The blueprint unit's triangulated
finite-stage statement and all its closure clauses are retained.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.finite_ctf_isTriangulated`, the item's sole original hole.
Added holes: none. Split-offs: none. No `sorry` remains in the delivered module.

The proof uses the existing named theorem
`AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated`; that imported theorem
still has its own hole and remains the constructibility dependency. The derived tensor and
K-flat resolution facts used in this delivery are proved in the existing library.

## No longer needed

- `lem-weil-valued-dvr-finite-quotients`: the already proved
  `Padic.finite_coefficientExtensionRing` directly supplies the needed finite instance. The node
  `def-weil-l-adic-coefficient-extension` remains as its declaration's attachment.
- `lem-weil-pbc-ringed-projection-mate-exact` / `Sheaf.Paper.ProjectionMateExact`: exact tensor is
  supplied by the existing generic monoidal derived-category machinery on the same module
  category, with explicit K-flat comparison. Neither ringed projection mates nor adjunction
  comparisons are used.
- Removed the unused proof import `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- Withdrew the first two corresponding top-level `tool_uses` approvals in the node; the long
  exact homology approval remains. No module is withdrawn by this delivery, and no other
  declared dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The node records a Lean attachment to `Sheaf.Paper.ProjectionMateExact`, but that source module
is absent from this checkout. In any case its abstract ringed tensor interface is unnecessary:
the exact functor needed here is constructed directly for the constant pro-etale coefficient
ring. No completed coefficients, etale-site substitution, or new mathematical hypothesis is
introduced.

The general K-flat module already proves the required class facts privately. Its proof-only
internal import provides those proofs without changing its API. The site has objects in
universe `u+1` and morphisms in `u`, so the equal-universe sheaf tensor shortcuts cannot be
used directly; the existing general-universe constructions fit exactly.

Checks: the complete proof compiled cleanly through `lcompile.py` (37 seconds with profiling),
and `deliver3.py --no-push` returned OK: compilation and preflight pass. The original theorem
signature was compared verbatim modulo whitespace and is unchanged. There are zero `sorry`
tokens and no lines over 100 characters. The added proof-import directions were checked and
introduce no cycle. Review class: CODEX for the node update and notation-scope change record.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
