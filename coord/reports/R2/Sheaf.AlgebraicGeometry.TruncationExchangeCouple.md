## What changed

Repaired `Sheaf.AlgebraicGeometry.TruncationExchangeCouple` after the upstream-sync
return recorded in `coord/returns/F1.md`. The private `couple` now explicitly constructs
the current upstream `BigradedExactCouple` structure. Its zero-composite fields use the
existing exactness witnesses; its image/kernel fields use
`ShortComplex.exact_iff_image_eq_kernel`. The private `couple_data` proves four reflexive
identities and identifies the transported projection with `g` using two applications of
`Function.hfunext` and `comp_eqToHom_heq`.

The public statements and definitions, imports, and visibility are unchanged. Updated
step 3 and `proof_origin` of `lem-weil-pbc-truncation-couple-morphism` to describe the
current constructor. No consumer adaptation is required for this private implementation.

Change record: `coord/changes/truncation-exchange-couple-upstream-constructor.md`.

## Proved and sorry left

Closed both existing holes:
- `CategoryTheory.TruncationExchange.couple` (private definition, now explicit data).
- `CategoryTheory.TruncationExchange.couple_data` (private lemma, now proved).

Both belong to `lem-weil-pbc-truncation-couple-morphism`, with the constructor realizing
`def-weil-pbc-truncation-exact-couples` as before. Zero holes remain in this module; zero
holes were added or split off. The existing public
`AlgebraicGeometry.Etale.truncation_exchange_couple_morphism` now uses the completed
constructor and accessor proof.

Single-file remote compilation passed in 5.2 seconds. The delivery preflight additionally
compiles the module with its declaration and axiom probe.

## No longer needed

No imports or dependency nodes were removed. All currently imported modules are used.
The obsolete `BigradedExactCouple.ofShifted` constructor and its accessor API are no longer
needed by this proof. No import of `Sheaf.CategoryTheory.ExactCoupleShifted` is needed:
the proof uses the upstream structure already publicly imported through
`Sheaf.CategoryTheory.ExactCouple`. No new exact-couple representation or dependency is
introduced. The unit's statement and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The upstream-sync return correctly identifies the two repaired holes. The recorded DAG
proof still referred to the removed `BigradedExactCouple.ofShifted` API; its constructor
step is now updated to match Lean. The existing exactness and naturality arguments were
sufficient, so no additional mathematical lemma or decomposition was necessary.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
