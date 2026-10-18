## What changed

Return repair: removed the duplicate private `openFullUnit` theorem and changed both
call sites to the existing `sharedBoundedOpenUnitIsIso` from
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`,
which this module already imports with `import all`. The existing shared declaration has
the exact needed binders and is also used by `Derived.LowerShriekIndependence`. No existing
source-library module is adapted, no new import is needed, and no public signature changes.

Replaced the cohomology theorem's hole by a compiling affine-local argument, with its
signature unchanged. On an affine source open, an explicit finite-generator closed embedding
into relative affine space reduces compact support to the smooth projection calculation and
closed support. Closed-support representability is proved from the existing open/closed
recollement, Rj* finiteness, exact pullback and the constructible Serre results for all three
coefficient certificates. It permits integral torsion.

The supplied proper adjunction and open adjunction transpose the representative's counit to
a comparison map. Naturality makes postcomposition bijective on bounded constructible tests;
a cone and double-orthogonal argument makes the comparison invertible on the localizing hull.
This proves the new public `affine_restriction_boundedConstructible` helper. Homology and
finite open/closed induction give the original constructibility theorem.

A direct boundedness proof from these affine restrictions also compiled during the session.
Another group (H3) subsequently claimed that module, so the boundedness adaptation was removed
from this delivery. Its compiled proof is retained in this sandbox's scratchpad only; no
progress for that module is claimed here. The public affine-restriction helper remains
available for the boundedness worker after landing.

The seven original delivery modules compiled through lcompile.py; the unchanged constructibility parent
also compiled as a consumer probe. No compiler limit was increased.
Raw pullback composition and explicit Over projection reductions avoid expensive expansion of
normalized adjunction comparisons. In the supported-projection proof, the comparison
isomorphisms are chosen only locally inside the theorem proof, avoiding repeated elimination
against a large dependent goal; no data definition makes those choices. No existing
definition body or public signature changes. The preflight-required change record for the added public helper and private proof commands is
`coord/changes/A4AffineRestrictionProofAPI.md`; it lists all 21 transitive consumers.

## Proved and sorry left

Closed the original item hole in
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible`.
This is a decomposition through the affine-line lemma below, not an unconditional
proof of the geometric duality theorem.

Proved in the retained delivery, with no direct sorry:

- `AlgebraicGeometry.ProEtale.CondensedRing.affine_restriction_boundedConstructible`.
- `AlgebraicGeometry.ProEtale.CondensedRing.affine_compactSupport_representable`.
- `AlgebraicGeometry.ProEtale.CondensedRing.closed_support_representable`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_compactSupport_comp`.
- `AlgebraicGeometry.ProEtale.CondensedRing.affine_projection_closedSupport_duality`.
- `AlgebraicGeometry.ProEtale.CondensedRing.affine_projection_representable`.

The repair adds zero holes. Exactly one split-off sorry from the retained delivery remains:
`AlgebraicGeometry.ProEtale.CondensedRing.affineLine_compactSupport_isLeftAdjoint`, node
`lem-sfb-adic-affine-line-adjunction`, in
`Sheaf.AlgebraicGeometry.EllAdicAffineLineRepresentable`. It still needs the projective-line
trace/diagonal unit, counit and triangle identities, passage through the standard affine
chart, and bounded constructibility of pullback twisted by one and shifted by two. The
statement includes integral torsion as well as both rational cases; it imposes no derived
completeness condition. Its full docstring gives the two explicit triangle calculations.
It assumes no supplied G and no localizing exceptional functor and is restricted to the
one-dimensional projection, uniformly over the base.

The finite-dimensional projection statement `affine_projection_representable`, initially
considered for a split, is proved in the retained delivery. A generic counit criterion
constructs an adjunction from the already proved closed-support representatives. Isomorphisms
and the empty-coordinate projection follow. Reindexing and affine-space sum isomorphisms,
compact-support composition, and `Finite.induction_empty_option` prove the general projection
case from the line case. Bounded/ambient compatibility and full inclusions then give exactly
the required natural ambient Hom equivalences. Dimension zero is proved, rather than left
inside the unfinished lemma. Empty bases and zero inputs are included in the line statement.

This delivery closes the item's one hole and adds one strictly lower geometric hole: it is a
decomposition, with net zero direct holes. The closed-support, affine-factorization,
compact-support composition, supported-projection and finite-dimensional induction
intermediates are all proved in the retained delivery. All dependencies'
existing holes and all other groups' modules are unchanged.

## No longer needed

The returned delivery's duplicate `openFullUnit` is removed. Its two calls use the existing
shared bounded-unit declaration; no theorem is newly split off for this repair.

Removed these proof imports from the original item (some declarations remain available through
required imports and are used below the item, as indicated):

- `Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure`.
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`.
- `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`.
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`.
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.

The field lfp theorem, algebraic-closure Serre theorem and integral Serre theorem are used
inside the proved closed-support calculation. Their original standalone comparison imports
are unnecessary in the item. The normalized `UpperLowerStar.Coherence` import tried during
proof development is also unnecessary: finite-cover gluing uses raw site composition and
coefficient comap. Redundant explicit imports of BoundedConstructible, OpenImmersionLowerShriek
and RightDerivedFunctor.Triangulated were removed after successful compilation.

The old coefficient-predicate/ctf comparison route and a second choice of Brown adjoint are
not used in the written proofs. The following old proof dependencies and their module
attachments are removed from the item's proof route:

- `det-def-sfb-constructible-local-model` — `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
- `lem-sfb-integral-lfp-constant-model-comparison` — `Sheaf.Paper.IntegralLfpConstantModelComparison`.
- `sk-def-sfb-constructible` — `Sheaf.Paper.CondensedConstantConstructibility`.
- `sk-def-sfb-bounded-constructible` — `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`.
- `det-def-localizing-closure-ctf-equals-bc` — `Sheaf.Paper.LocalizingClosureCtfEqualsBc`.
- `sk-def-localizing-closure` — `Sheaf.Paper.LocalizingAdmissibleCoefficients`.
- `sk-prop-sf-existence` — `Sheaf.Paper.LocalizingExceptionalAdjoint`.
- `det-cor-existence-ii-restriction` — `Sheaf.Paper.ProperExceptionalRestriction`.
- `sk-thm-restriction` — `Sheaf.Paper.RationalExceptionalRestriction`.
- `det-prop-int-brown-adjoint` — `Sheaf.SixFunctors.IntegralBrownAdjoint`.
- `sk-thm-int-restriction` — `Sheaf.SixFunctors.IntegralExceptionalRestriction`.

Also removed as direct proof dependencies: `sk-def-localizing-closure`,
`sk-prop-sf-existence`, `det-cor-existence-ii-restriction`, `sk-thm-restriction`,
`det-prop-int-brown-adjoint`, `sk-thm-int-restriction`, `det-sp-unique-right-adjoint`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`, and
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`. Definitions needed by unchanged
statements remain statement dependencies. Noetherianity comes directly from finite type;
no descending-chain conversion or internal/sectionwise module equivalence is needed.
The hull, proper localizing pushforward, coefficient certificate and actual module
constructibility definitions remain in use. The remaining affine-line proof still follows
the blueprint's rational/integral trace calculation; this is not a claim
that all geometric restriction theory is globally unused.

Pruned all old top-level tool approvals in the item except finite-type Noetherianity:
the two standalone lfp bridges, constant-model comparison, integral model comparison,
ctf=BC, rational restriction, integral Brown adjoint, integral restriction, descending-chain
conversion, section-action equivalence and Brown existence. Existing approvals elsewhere are
untouched. The boundedness nodes and their current proof routes are outside this delivery.

The proved finite-coordinate induction also removes
`det-cor-affine-space-rational-induction` and its module
`Sheaf.Paper.AffineSpaceRationalInduction` from the new projection node's proof route.
The integral/rational affine-line trace calculations remain needed.

## Where the brief, the DAG or earlier work was wrong

The landing tools correctly identified the duplicate `openFullUnit` statement. Directly
importing `Derived.ShriekComposition` would create a cycle through `UpperShriek`, but the
current library already supplies `sharedBoundedOpenUnitIsIso` in the acyclic, already
imported `ExchangeMono` module. Reusing that declaration repairs both duplicate call sites
without moving or changing any existing library declaration.

Eleven old dependency records name module files absent from this read-only checkout (the
list above). A probe import of the affine-space rational induction module also reports its
server olean absent. They cannot be imported merely from their recorded declaration names.
The written proof uses available declarations and isolates the exact missing geometric
calculation rather than duplicating those unavailable interfaces or altering coefficients.

The source library's `EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction` has a finite-ring
small-etale adjunction. Its `Adic` and `Rational` reconstruction modules concern supplied
normalized systems and their derived-complete realizations. Those statements do not supply
the needed adjunction in the ordinary derived category of internal condensed modules, so
they were inspected but not imported or used to impose a completeness hypothesis.

The old proof plan needlessly compared actual stratified lfp constructibility with constant
models and Dctf before using a supplied adjunction. Representability on bounded constructible
tests plus generator detection suffices. The remaining affine-line lemma is not the original
statement renamed: it concerns only the one-dimensional projection, independently of G and
any closed support, and the closed
representability, factorization, comparison-isomorphism and finite-cover arguments are Lean
proofs in this delivery. The closed and affine representability intermediates initially
considered for splits were proved during the session. The first geometric split was also reduced further: a new
coefficient-uniform compact-support composition proof and a generic naturality transport
argument close the supported-projection comparison. The finite-dimensional coordinate
induction was then proved as well; only the affine-line trace adjunction remains open.

The boundedness module changed and was claimed by H3 during this session. The compiled
adaptation was withdrawn from this delivery before further work on it. No held module is
adapted. Preflight nevertheless requires a change record for the public helper and surrounding
proof commands, so `coord/changes/A4AffineRestrictionProofAPI.md` records the unchanged
original signature, added helper and every downstream consumer. No existing statement or
definition changes meaning.

The finite-ring small-etale and derived-complete reconstruction interfaces inspected above
are not substituted for the ordinary condensed-module affine-line theorem. The new induction
also makes `det-cor-affine-space-rational-induction` and
`Sheaf.Paper.AffineSpaceRationalInduction` unnecessary as a proof dependency: the coordinate
induction, including its zero-dimensional case, is implemented here uniformly for every
coefficient certificate.

## New nodes

`lem-sfb-adic-closed-support-representable`: proved localization-triangle calculation for all
certified coefficients, including integral torsion. Its new module has zero holes.

`lem-sfb-adic-affine-compact-support-representable`: proved closed factorization and composition
of the two Hom bijections. Its new module has zero holes.

`lem-sfb-adic-affine-restriction-bounded-constructible`: proved public helper in the item module;
this records the actual generator-comparison step reused by boundedness.

`lem-sfb-adic-affine-projection-closed-support-duality`: now proved by compactification
comparison, compact-support composition, the proper comparison for the closed immersion,
exactness of closed pushforward, and transport of natural Hom equivalences.

`lem-sfb-adic-bounded-compact-support-composition`: proved for all three certificates. Integral
proper base change is assembled from finite reduction and conservativity; rational cases use
the existing proper-base-change declarations. The exchange mate is invertible by open/closed
conservativity, and common refinements give composition. Auxiliary refinement existence is
eliminated only in theorem proofs. No data definition chooses an arbitrary unproved witness.
The existing ShriekComposition module could not be imported here: it imports UpperShriek,
which imports the exceptional-constructibility parent of this item. Its available public
composition statements cover only rational coefficients. The new interface also handles the
integral case without importing UpperShriek. Import-direction checks for Proper,
LowerShriekIndependence and LowerShriek.MorphismDefs all passed.

`lem-sfb-adic-affine-projection-representable`: now proved by empty/option induction on
finite coordinate types. The empty case and coordinate isomorphisms use the proved closed
calculation. The sum case uses the affine-space sum isomorphism, compact-support composition
and composition of adjunctions. The line case is the only new unfinished input. The final
naturality transport to ambient Hom sets is proved in Lean.

`lem-sfb-adic-affine-line-adjunction`: the single unfinished one-dimensional smooth
calculation described above. The local `IsFinitenessCoefficient` requirement follows from
its coefficient certificate. Its full proof plan records the projective-line trace and
diagonal formulas, both triangle identities, the affine chart, and preservation of bounded
constructibility. It does not quantify over higher dimensions, arbitrary closed immersions,
or any supplied exceptional adjoint.

All seven new nodes are in `dag/nodes/sec-six-functors-basics/`, with the same unit as the item.
Updated the item's proof record to match the Lean. The sole change record is
`coord/changes/A4AffineRestrictionProofAPI.md`; no other group's module is adapted.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
