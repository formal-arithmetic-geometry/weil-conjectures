## What changed

Filled all four remaining theorem proofs in
`Sheaf.Paper.AdicPullbackPresentationTransport`. Public signatures, public imports,
and target statements are unchanged. Added
proved private helpers and private proof imports; updated the item's proof route
in its DAG node. The constant and evaluation representative-normalization
predicates now specialize the generic public definition
`CategoryTheory.Functor.HasRepresentativeNormalization`. Both unfold to their
original equations. The required definition change and consumer check are in
`coord/changes/W7-adic-presentation-normalization-predicates.md`.

The constant comparison is transported to the canonical normalized comparison;
counit compatibility and naturality give the normalization equation, and canonical
uniqueness gives uniqueness. Evaluation is descended through fully faithful
restriction to objectwise K-flat representatives. A functorial flat resolution of
the entire tower supplies these representatives with strict transition maps.
The finite-transition square is the canonical coherence square followed by
naturality of the universal tower comparison. For the open comparison, the
restricted adjunction counit is an isomorphism by the triangle identity. Inverse
image preserves this local isomorphism, and the underlying-abelian-sheaf
comparison for finite scalar extension transports it to the required map.

All proof helpers are proved. No new public theorem statement, module, axiom, hollow
definition, or adaptation of another module is introduced. The new generic
predicate is attached to the existing item node. The argument also
covers identity quotient arrows and empty/full open objects: it uses naturality,
isomorphisms, and adjunction identities without nonemptiness or strict inequality.

Validation: the complete delivered module compiled successfully through
`lcompile.py` in 37.8 seconds (exit code 0), below the 60-second limit. The delivery probe also compiled in 55.6 seconds; its four unused-simp
warnings were removed. Each of the four proof arguments also compiled in
scratch probes. All nine added proof imports pass the import-direction check. All 31 existing declaration
signatures and all public imports were compared with the live source and match.
The packet is validated by the required delivery tool's whole-module compilation
and preflight before pushing. Profiling directives are removed from the delivered
file, which has zero `sorry` tokens and no lines over 100 characters.

## Proved and sorry left

Closed the four original holes:

- `AlgebraicGeometry.Scheme.adicPresentationConstantIso_normalized`
- `AlgebraicGeometry.Scheme.adicPresentationEvaluationIso_exists`
- `AlgebraicGeometry.Scheme.adicPresentationFiniteIso_transition`
- `AlgebraicGeometry.Scheme.adicPresentationLocalizedComparison_isIso`

Holes added: zero. Holes left in the delivered module: zero. Split-off statements:
zero. This is a proof from existing library declarations; it does not claim that
all transitive dependencies of those declarations are already sorry-free.

## No longer needed

The following originally planned direct dependencies are not used by this module:

- `lem-cbc-finite-constant-map-naturality`: its square is already proved here using
  the sheafification and inverse-image adjunctions.
- `lem-cbc-derived-constant-tower-normalization`: the canonical normalized constant
  comparison and counit-preserving transport suffice.
- `lem-cbc-derived-tower-evaluation-normalization`: evaluation descent is proved
  here using fully faithful restriction and functorial tower resolutions.
- `lem-cbc-strict-quotient-pullback-computation`: existing published strict
  reduction/augmentation definitions and finite coherence suffice.
- `lem-cbc-constant-derived-limit-resolution-unit`: the existing specified natural
  unit of the derived constant/limit adjunction suffices.
- `lem-cbc-open-localized-counit-comparison`: the actual counit comparison follows
  from local restriction, inverse-image composition, and the proved underlying
  abelian-sheaf comparison.
- `lem-pur-left-derived-from-kflat-class`: comparison uniqueness uses Mathlib's
  `Functor.leftDerivedUnique` and `Functor.leftDerived_ext` directly; the canonical
  universal structures come from `CompletedTowerPullback`.

No existing public import is removed. No module is withdrawn: these nodes may
still be required by other parents, statements, or transitive imports. In
particular the canonical completed-pullback/reduction modules and their own
proof dependencies remain needed. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Profiling required an implementation refactor of
the two normalization predicates; their equations and meanings are preserved.
The source module with its original holes took about 47 seconds, leaving
insufficient room for the completed proofs. Generic categorical calculations
avoid repeatedly unfolding the concrete sheaf pullback. The original DAG offered
separate general normalization/localized-counit interfaces. The existing
canonical normalization, resolving-representative descent, and restriction APIs
allow the four remaining proofs without importing those interfaces. The node's
proof and proof dependencies now record the Lean argument actually used.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
