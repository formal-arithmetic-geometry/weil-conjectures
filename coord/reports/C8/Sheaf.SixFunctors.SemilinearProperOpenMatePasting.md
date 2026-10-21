## What changed

In `lean/Sheaf/SixFunctors/SemilinearProperOpenMatePasting.lean`, proved four
existing declarations without changing any existing signature or public definition:
termwise scalar restriction, its normalized ordinary evaluation/direct-image
comparison, invertibility of the corresponding inverse-image mate, and both
clopen-projector component formulas.

The scalar-restriction proof constructs compatible ringed-sequence-site structural
maps and applies the existing constructive tower functor. The evaluation comparison
is built from module-sheaf pushforward composition and congruence, with identity
section maps in both directions. Its inverse-image mate is identified with the
constant-diagram lift of the existing normalized level inverse-image isomorphism
using its unit equation. The projector proof uses the adjoint-triple triangle
identity on the image and exact localization of the ordinary zero composite on
the complementary open.

Added proved private helpers for constant-diagram isomorphisms, their mate unit
normalization, and the sequence-site evaluation square. Added proof-only imports
of `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.Paper.CoefficientRingedSequenceSite`,
`Sheaf.Paper.SemilinearSystemModels`, and
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`. The two paper imports
expose their existing private constructive helpers only to these proofs. Local
irreducibility attributes keep canonical functor and coefficient constructions
abstract while using their APIs; no imported definition is edited.

Updated the existing node's proof, proof dependencies, and proof origin to record
these arguments. No other module is adapted. The required change record for
local elaboration attributes is
`coord/changes/semilinear-proper-open-proof-reducibility.md`; its consumer check
found zero downstream Lean modules and only the item in the declaration-use lists.

Validation: the complete item file passed single-file server compilation through
`lcompile.py` with exit code 0 in 42.1 seconds. All Lean lines are at most 100
characters. A source audit found exactly the twelve reported remaining holes and
no new forbidden declarations.

## Proved and sorry left

Closed 4 of the item's original 16 holes; added 0 holes and split off 0 statements.
All names below are in `AlgebraicGeometry.ProEtale.SemilinearProperOpen` and are
attached to node `lem-sf-semilinear-proper-open-mate-pasting`.

Proved:

- `rhoOrdinary_existsUnique`
- `evalPushOrdinary_existsUnique`
- `evalPullInv_isIso`
- `pi_components`

Exactly 12 existing holes remain, unchanged:

- `gamma_adjunct`
- `semilinearProperOpenMatePasting`
- `gamma_identities`
- `rhoPushOrdinary_existsUnique`
- `rhoPullInv_isIso`
- `rhoR_isIso`
- `rhoJInv_isIso`
- `gamma_scalarRestriction`
- `evalR_isIso`
- `evalJInv_isIso`
- `gamma_evaluation`
- `compositor_associativity`

The proofs use existing declared dependencies, including
`VaryingRing.moduleEvalG_existsUnique` and `VaryingRing.modulePi_components`.
Their provider modules are unchanged; this packet does not claim the entire
proper/open calculus is axiom-free yet.

## No longer needed

None. No original import, node, declaration, or module is removed or withdrawn.
The remaining clauses still require their existing planned dependencies. The
four proofs reuse existing ringed-sequence and varying-ring declarations without
introducing any new proof obligation or bypassing a unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. Equalities of underlying functors
alone do not justify identifying normalized adjunction comparisons. The
inverse-image evaluation proof explicitly uses the level unit equation and the
mates equivalence; the clopen proof also retains the actual adjunctions. The
section normalization and constant-diagram calculations are factored into proved
private helpers to avoid repeatedly unfolding coefficient and functor data.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
