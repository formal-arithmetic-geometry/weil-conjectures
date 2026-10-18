## What changed

Proved `AlgebraicGeometry.Etale.isIso_iff_of_jointlySurjective_etale_family`
in `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`, preserving its
statement, universes, visibility, docstring and all imports.

The forward direction uses functorial preservation of isomorphisms. For the converse,
`Scheme.isIso_of_isIso_sheafFiber_map` reduces to the algebraic-closure geometric point
above each point of the target. Joint surjectivity chooses a member of the cover and a
point over that geometric point; Mathlib's
`Scheme.exists_fac_of_etale_of_isSepClosed` lifts the geometric point through this
etale morphism. Rewriting along the factorization and applying
`NatIso.isIso_map_iff` to `upperStarCompUliftSheafFiberIso` identifies the desired stalk
map with a stalk of the assumed invertible pullback. Functoriality finishes.

This is exactly the existing node's four-step stalk argument. The source passages read
were Stacks 0EZR (proof of (1)), 03PR, 03Q1 (3) and 03PU in
`literature/stacks-project/etale-cohomology.tex`. The unit's route is unchanged.

Validation: the module compiles without warnings through `lcompile.py`. A source comparison
checks that the complete original text preceding the proof is unchanged. The proof works
for arbitrary index universe `w`, and makes no nonemptiness assumption: when the index type
is empty, joint surjectivity supplies a contradiction at any putative target point.

Searches: LeanFinder through `msearch.py` returned general etale-site declarations and
local surjectivity results, rather than this criterion. Loogle found the exact geometric
point lifting lemma, and grep found its Mathlib implementation. Repository search also
found `Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective` in
`WeilConjectures.SixFunctors.OpenClosed.Conservative`; its index type is restricted to
`Type u`, so the direct planned stalk argument avoids reindexing and additional imports.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isIso_iff_of_jointlySurjective_etale_family`
(node `lem-weil-pbc-etale-cover-detects-iso`).

Proved 1 of 1 original sorries. Added 0 holes. Remaining holes in the delivery: none.
No split-offs or auxiliary declarations were added.

## No longer needed

None. No imports were removed and no existing planned node was bypassed. The proof uses
the geometric-point lifting leaf, the inverse-image stalk comparison and geometric-stalk
conservativity exactly as planned. The existing coefficient and inverse-image imports
supply the statement; both existing proof imports supply the stalk argument. No new import
of `OpenClosed.Conservative` or `PointedEtaleStalk` is needed: the former was only a search
candidate, and the latter's node already records `Point.sheafFiber` as its Mathlib match.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. The existing declarations suffice to prove the
whole statement, including its unrestricted index universe. No definition, signature, node
or unit route required a change.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
