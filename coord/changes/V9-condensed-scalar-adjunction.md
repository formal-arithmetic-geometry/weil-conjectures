# Canonical scalar functors and comparison presentations

Module: `Sheaf.Paper.CondensedCompactSupportProjection` (held by V9).

Name the original derived scalar/restriction adjunction as
`condensedScalarAdjunction`, with the existing `condensedScalar` functors in its
type. Name its proper and open mates as `condensedPushScalar` and
`condensedOpenScalar`. Use these presentations in `condensedScalarShift`,
`condensedScalarComp`, `condensedScalarId` and `condensedProjection` to avoid
repeated conversion of the same derived functor and tensor-instance arguments.
Unfolding the names restores the original constructor bodies exactly. No
parameter, universe, coefficient ring, support functor or comparison map changes.
No source-library file is changed.

The coefficient-composition proof uses the original restriction compositor,
derived horizontal-square composition, and adjunction mate pasting. Its helpers
are private and proved. The existing shift and identity proofs use the same named
adjunction and comparisons. Give the private ordinary restriction identity its
explicit original functor type. Generic module cancellation avoids expanding
large derived-functor constructions.

Cache the existing small and large sheaf/module colimits, sheaf tensor additivity,
sheaf/module Grothendieck properties, module K-injective resolutions, and
sheaf/module flat-resolution properties as proved public theorems. Their types
are propositions; no assumption or selected object is added. Use them locally
while checking the constructions, then export them as instances with priority
2000 at the end of the module. The original tensor-colimit instance registrations
remain local. Place the base caches before the tensor witnesses that use them.

Forced consumer adaptation: `Sheaf.Paper.CompactSupportRealizationFactorization`
(currently unclaimed, both module and node claims checked). Its original
`coefficientFactorization` proof failed with two unsolved goals: each compares a
composite using `condensedPushScalar` and `condensedOpenScalar` with the composite
using `CondensedRing.derivedPushHom` and
`CondensedRing.derivedOpenImmersionShriekIso`. At line 272 append `<;> rfl` to the
existing `simp only` command. This unfolds the definitionally identical named
presentations in the two residual goals. All signatures, visibility, imports,
other proofs and the five existing holes remain unchanged.

Validation: the main module and all three direct consumers compile within the
single-file limit. The other two consumers,
`Sheaf.Paper.CompactSupportCondensedRealization` and
`Sheaf.Paper.CompactSupportRealizationFactorNormalization`, compile unchanged.
Six temporary Lean examples compile: reflexivity after unfolding identifies the
scalar shift, compositor, identity, proper mate, open mate and full projection
with their original constructor bodies. The temporary examples and unchanged
consumer copies are removed from the delivery. The adapted factorization module
also compiles separately after its one-line proof repair.

Write the original return types explicitly for `fieldDerivedUpperStar`,
`fieldDerivedLowerStar`, `fieldDerivedOpenShriek`, `fieldProperOpenRestrictionNat`,
`fieldProperOpenRestriction` and `fieldRefinementNat`; their constructor bodies
are unchanged. Also cache countable module coproducts, integer colimits and their
exactness, and the existing K-flat quasi-isomorphism preservation of scalar
extension as proved propositions. These are likewise used locally first and
exported at the end of the module.

Name the original Abelian sheaf and module structures as `fieldSheafAbelian`
and `fieldModuleAbelian`, respectively. These are reducible aliases of
`CategoryTheory.sheafIsAbelian` and `CategoryTheory.Mod.instAbelian`, with the
fixed pro-etale sheaf category explicit. Register them locally while constructing
the module and export them at its end, so subsequent category-instance searches
reuse the same constructor data. They add neither chosen witnesses nor assumptions.
Temporary reflexivity examples compare them with those original constructors.

Similarly, `fieldModuleDerivedCategory` names the same
`HasDerivedCategory.ofIsGrothendieckAbelian` construction at universe `u + 1`.
It is a reducible alias with the same local-then-exported registration. No new
localization or resolution is selected; a temporary reflexivity example compares
it with the original instance constructor.
