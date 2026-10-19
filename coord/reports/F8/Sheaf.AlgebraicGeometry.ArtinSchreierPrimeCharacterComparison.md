## What changed

Proved `AlgebraicGeometry.Etale.artinSchreier_prime_character_comparison` in
`Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison`, with its original
signature, definitions and public imports unchanged. All added helpers are private and
proved in this module. No other Lean module is changed. The required interface change record is `coord/changes/artin-schreier-prime-character-comparison-elaboration.md`.

The parameter argument uses the nondegenerate trace character, injectivity of its
multiplicative shifts, and the linear independence of distinct characters to prove
surjectivity by a cardinality bound. The geometric argument uses the existing trace-cover
map theorem and the upstream isotypic descent API. Evaluation at a geometric fibre point
is an isomorphism on either character summand: transitivity gives injectivity and the
projected delta function gives surjectivity. The pullback-of-sections map along theta then
has invertible adjoint, giving the comparison with its required inclusion equation.
The same criterion identifies the q-image with `artinSchreierSheafOf`; existing lisseness
transports to both images. Naturality is proved by composition of section pullbacks,
translation-projector compatibility and an explicit categorical image calculation.

Updated the item's node proof, proof dependencies and proof origin to describe this route.
The unit's `realized` lists are empty for this auxiliary node; no unit statement or unit
proof step is bypassed. No definition/statement repair or consumer adaptation is needed; see the elaboration change record named above.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.Etale.artinSchreier_prime_character_comparison`
(node `lem-a1-artin-schreier-prime-character-comparison`).

The delivered module contains zero `sorry`; zero holes are added and zero are split off.
The proof uses the existing named theorem
`AlgebraicGeometry.artinSchreier_trace_cover_map`, whose proof remains a `sorry` in its
own module/node `lem-a1-artin-schreier-trace-cover-map`; that module is not changed.
This is a proof from the stated dependency, not a claim that its transitive axioms are
already closed. The finite-field and generic sheaf helpers added here are fully proved.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`.
- `WeilConjectures.SixFunctors.Finite.BaseChange`.
- `WeilConjectures.SixFunctors.Finite.Stalk` (its API is already publicly available through
  the upstream Artin–Schreier/isotypic imports).
- `Mathlib.FieldTheory.Finite.Trace` (already publicly imported by the trace-cover module).

The attempted additional `Mathlib.LinearAlgebra.Dimension.Finrank` import was also removed;
the existing imports provide the character dimension bound.

Removed the direct proof dependencies
`lem-weil-pbc-finite-etale-etale-local-split` and `lemma-weil-pbc-finite-exchange`.
Lisseness follows by transporting the proved lisseness of `artinSchreierSheafOf` through
the q-image isomorphism. The universal-sheaf comparison uses its existing eigenmap with
invertible adjoint and the generic isotypic criterion, without finite base change.
The finite stalk formula remains needed; the removed direct Stalk import is redundant,
not a claim to prune that module from the targets' transitive import closure.
No further global module-pruning claim is made: other modules can still need these tools.

## Where the brief, the DAG or earlier work was wrong

The retained attempt was unfinished and unchecked after compile-server failures; this
session repaired its coercion, projector unfolding, instance registration and naturality
elaboration errors. This continuation also replaced a costly stalk rewrite by direct
transport, supplied the isomorphism instance explicitly, and separated inference from
destructuring of the large comparison results. Scoped heartbeat settings accommodate
the dependent sheaf conversions; the 60-second compile limit is unchanged. The compiler
is responding again. The DAG's mathematical statement
was correct. Its separate finite-exchange and finite-etale splitting steps were unnecessary
with the existing upstream Artin–Schreier and generic isotypic interfaces.

The proof works for empty schemes and zero functions, for r = 1 and p = 2, and when p
divides r: it uses nondegeneracy of trace, never a nonzero trace of 1. The prime field is
universe-lifted explicitly rather than changing the statement's universe.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
