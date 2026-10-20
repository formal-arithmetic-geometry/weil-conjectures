## What changed

Proved `AlgebraicGeometry.artinSchreier_trace_cover_map` with its entire original signature
and all five clauses unchanged. All original public definitions and structure fields are
unchanged. Added only proved private helpers for the cover universal property, coordinate
translations, finite-field polynomial and trace calculations, geometric fibres, and arbitrary
base change. The maps are constructed explicitly from their coordinates, with no choice of
unspecified morphisms.

The shorter route uses the existing proved affine-space Artin–Schreier finite/étale results,
then the pullback universal property and Mathlib's finite geometric-point API. It avoids the
relative-Spec sheaf-algebra machinery. Updated the item's node proof and dependencies to
record that route. No unit statement or unit proof step is bypassed.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.artinSchreier_trace_cover_map`
(node `lem-a1-artin-schreier-trace-cover-map`). Holes added: none. Holes remaining: none.
No statement was split off and there are no new public declarations.

## No longer needed

Removed imports `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`Mathlib.NumberTheory.LegendreSymbol.AddCharacter`,
`Mathlib.RingTheory.Etale.StandardEtale`, `Mathlib.FieldTheory.Separable`,
`Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`,
`Sheaf.AlgebraicGeometry.CoherentFiniteType`, and
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`.

The proof does not need nodes `lem-weil-pbc-affine-morphism-relative-spec`,
`lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-standard-etale-monic-derivative`,
`pqf-def-coherent`, `lem-weil-pbc-relative-spec-base-change`,
`def-pc-separable-polynomial`, `lem-pc-separable-polynomial-distinct-roots-alg-closed`, or
`lem-weil-pbc-module-pullback-affine-sections`. Finiteness and étaleness follow from the
upstream affine-space results, while the universal property constructs and compares maps
directly. Geometric points are handled by closed-point sections on finite fibres and the
finite-field factorization of `X^q-X`, rather than a quotient-spectrum/root-counting theorem. Withdrew the three obsolete
relative-Spec and module-pullback `tool_uses` approvals from this node.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG plan's relative-Spec passage is unnecessary
for these already defined pullback covers. The prime-field translation helpers must permit
its field universe to differ from the scheme universe, because `ZMod p : Type` while
`X : Scheme.{u}`. This is a private-helper issue and changes no existing signature.

The proof uses no assumption that `Tr(1)` is nonzero. Mathlib proves trace surjectivity
for finite separable fields; multiplication by nonzero `b` preserves surjectivity. This covers
`p=2`, `r=2`, `b=1`, as well as
`r=1`, `f=0`, empty bases and empty open sets. Polynomial identities use the zero-ring-capable
Frobenius homomorphism, so no unjustified nontriviality assumption is introduced.

The interrupted candidate unfolded pullback and trace-polynomial definitions during large
rewrites. Local irreducibility and proved APIs for composite pullbacks and constants avoid
those expansions. No compiler time limit or heartbeat limit is increased. The import-pruning
change record is `coord/changes/V5-artin-schreier-trace-imports.md`.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
