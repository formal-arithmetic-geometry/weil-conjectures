## What changed

Filled both theorem proofs in `Sheaf.Paper.ProjectiveDiagonalComposition`.
`diagonalPush_preservesFiniteColimits` specializes finite-pushforward exactness to the
projective diagonal. The diagonal is finite and locally of finite presentation over
an arbitrary base. The proof transports exactness from modules over `ULift ℤ` through
the induced equivalence with abelian sheaves, then uses the existing finite-colimit instances
for `mapMod` and restriction of scalars (proved through module forgetful functors). This includes empty and non-Noetherian
bases and arbitrary commutative condensed coefficients.

`projection_existsUnique` unfolds the shared native tensor interface, takes the
published canonical projection family, and uses heterogeneous equality followed by
function extensionality for uniqueness. Every original signature and definition body
is retained. Added six private proof imports: finite pro-etale pushforward,
finite-presentation diagonals, smoothness of the projective line,
the abelian-group/integer-module equivalence,
restriction of scalars, and the lifted integer ring. Updated the existing node's proof,
proof dependencies and proof origin to record these arguments. The exactness theorem
retains its original commutative-coefficient binder; its unused-section-variable
warning is disabled locally because the proof works for more general coefficients.
The complete module is checked on the project server; delivery preflight also checks
the final warning-free form and declaration probes.

The finite-pushforward result is the existing proved declaration
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite`, described
by blueprint node `lem-fd-proetale-finite-pushforward-exact` (whose Lean attachment is
currently absent despite the declaration existing). Its use is a generic tool within
the same six-functors chapter; `lemma-nagata-diagonal-finite-presentation` is a proved
generic tool. The proved projective-line smoothness instance
`ProjectiveLine.smoothOfRelativeDimension_one` supplies its structural map's local
finite presentation (node `lem-sc-projective-line-smooth-relative-dimension-one`);
this is a geometric tool, without using the Picard-duality unit's route. The unit's
route and canonical comparisons are preserved.

## Proved and sorry left

Closed 2 original holes, both attached to `def-sfb-projective-diagonal-composition`:

- `AlgebraicGeometry.ProEtale.RationalP1.diagonalPush_preservesFiniteColimits`.
- `AlgebraicGeometry.ProEtale.RationalP1.projection_existsUnique`.

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The proof uses existing library declarations; it does not claim that every inherited
axiom dependency of the module is already discharged.

## No longer needed

None. The original node had no proof-dependency plan and no proof imports to prune.
All original public imports are retained; every newly added proof import is used.
The direct proof avoids introducing a general closed-support exactness lemma or
requiring a quasi-compact-complement construction for this diagonal. No existing
module or DAG dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan. The earlier exactness docstring appealed generally
to exact closed direct image without recording the relevant geometric hypotheses.
The implemented proof instead uses finite-presentation exactness for the diagonal,
matching the current blueprint's finite-pushforward lemma. No statement repair is
needed. The rework table's quarantine history was checked: the absent live item is restored
from its quarantine archive, preserving all declarations and public dependencies.
The rework reason named a transitive ProjectiveLineGenusZero import, which the
current dependency build already resolves; neither that module nor the item is withdrawn.

LeanFinder, Loogle and Mathlib grep were run through the prescribed search tool.
They did not give the specialized theorem; the existing adopted-source finite
pushforward theorem gives the shorter route. Loogle reported its unqualified
`PreservesFiniteColimits` identifier unknown, so that query was not used as evidence
of absence.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
