## What changed

Repaired return C-f6e8b (head f6e8b6dd7), points 5 and 6: removed the unused
`Mathlib.Algebra.CharP.Lemmas` import and removed
`lem-weil-pbc-profinite-point-pullback` from the first proof step and `proof_deps`.
The identity proof uses source `lowerStarId`. The repaired item compiled cleanly
through `lcompile.py` in 17.4 seconds. No theorem statement or proof body changed
in this repair; the retained decomposition and hole count below are unchanged.

Completed the Lean proof of `AlgebraicGeometry.ProEtale.CondensedRing.localizingRefinement_coherence`
from the existing declarations and one strictly smaller geometric support lemma. The public
statement and all four clauses are unchanged. Uniqueness, identity and composition hold for
arbitrary unbounded complexes. The identity and composition proofs use the actual canonical
derived identity/compositor, with explicit adjunction, equality-transport and unit normalization.
They do not assume invertibility of general refinements.

For invertibility, proved the normalization on the open, propagated closed-support vanishing
from the Dctf generators through a triangulated kernel closed under the required sums, and
applied the existing source-library derived open-closed detection theorem. This uses
`compactification_localizing` for the compactification `(jprime,h)` of `j`, and
`localizingClosure_exists` for the closure properties. The generic kernel argument and all
coherence calculations are proved private helpers in the item module. Its proof docstring
and the parent DAG now describe the actual coefficient classification, bounded devissage,
relative-sum kernel argument and canonical coherence calculations.

Extracted only the independent boundary calculation of source proof step 5 as
`continuousAlgCl_refinementBoundaryVanishing` (declaration namespace
`AlgebraicGeometry.ProEtale.CondensedRing`). It concerns a closed restriction of proper
pushforward on generators and mentions neither the refinement comparison nor Loc(Dctf).
It therefore does not restate any of the four clauses under a new name. The retained
theorem has only the all-continuous-map algebraic-closure coefficient case
and only constructible sheaves placed in degree zero. The parent proves the passage to
bounded complexes using the already proved `DerivedCategory.prop_of_bounded`, applied
to the triangulated vanishing kernel. No bounded-complex descent is left in the new lemma.
The standard cases are now proved from `properOpenInterchange`: classify the coefficient
presentations (with an explicit continuous-ring isomorphism for a universe lift in the finite
case), specialize to p = identity and the compactification `(jprime,h)`, and carry the zero
closed restriction across its invertible comparison. The remaining coefficient-specific
proper-base-change calculation is a genuine separate source subargument. Searches of
continuous lisse descent, scalar-change push mates, condensed finite-model descent and
proper-boundary acyclicity found no applicable continuous-algebraic-closure declaration: the
first and last are finite-field/discrete-coefficient results, and the condensed descent and
scalar-basis results explicitly use finite-subextension-valued coefficients. The classical
pro-etale proper-base-change theorem needs discrete constant coefficients and torsion
cohomology, and compact bounded-constructible base change uses finite prime-field
coefficients; neither covers this remaining case.

The existing identity helper proofs now use the source module identity and the proved
open-unit lemma rather than their earlier proof-dependency holes. `Mod.isoMk` object arguments
are explicit; the corresponding definition and theorem type are definitionally unchanged.
Change record: `coord/changes/h3-refinement-identity-explicit-objects.md`.

Validation: the final pruned packet compiled cleanly through `lcompile.py --all`:
57.0 seconds for the complete item; the support module was cached (0.1 seconds), with its
last clean fresh compile taking 7.2 seconds. Profiling
repeat runs that reached 60 seconds identified module tensor structures, derived adjunctions,
and flat-resolution instance search. Local irreducibility keeps those definitions folded;
local priorities select the existing module and pro-etale flat-resolution instances directly.
The identity-component API replaces unfolding of the direct-image identity. Explicit common
functor instances are reused in the kernel argument. These are local proof elaboration
settings; no shared definition or exported instance changes. No profiling options are retained.
The standard-coefficient support proof and universe-lift comparison
were also checked separately (7.3 seconds). The unchanged direct consumer
`Sheaf.Paper.CompactificationRefinementIdentity` compiled against the final interface in
13.5 seconds; its unchanged temporary copy was removed from the packet. A separate
21.0-second check proves by `rfl` that the explicit-object identity construction equals
the old definition verbatim, and checks the old naturality type against the proved theorem.
The explicit axiom audit (55.4 seconds) of the triangulated kernel, bounded
devissage, localizing-kernel extension lemma, canonical composition law, and canonical
identity law reports only `propext`,
`Classical.choice`, and `Quot.sound`. The main theorem additionally reports `sorryAx`,
as expected from its named existing dependencies and the single retained boundary lemma.
The audit was compiled in a separate scratch copy; no audit commands occur in the packet. Further delivery checks are recorded by deliver3.py.

## Proved and sorry left

Original item: 1 sorry, in `AlgebraicGeometry.ProEtale.CondensedRing.localizingRefinement_coherence`.
Closed that hole by a complete Lean proof of all four conjuncts. In particular its uniqueness,
identity and composition clauses are proved without the new support lemma.

Added 1 sorry, exactly the public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_refinementBoundaryVanishing`, in
`lean/Sheaf/Paper/RefinementBoundaryVanishing.lean`, node
`lem-sf-refinement-boundary-vanishing`. There are zero sorries in the item module and one
in the delivered packet, confined to constructible sheaves in degree zero for the all-continuous-map
compatibility coefficient. No sorry occurs in a definition or a private helper.

This is a decomposition of the one original hole, not a net hole closure (1 closed minus
1 added = 0). Existing imported theorems with their own sorries remain the project's declared
proof dependencies; they are not newly introduced holes of this delivery.

## No longer needed

Removed these proof-only imports from the item:

- `Mathlib.Algebra.CharP.Lemmas` (return point 5; its used facts come from `CharP.Defs`)
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.ProfinitePointPullback`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.FiniteProperBaseChange`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.Paper.ProperBaseChangeRational`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`

The obsolete tool approvals withdrawn from the parent are the removed dependency edges
listed below except the five statement/definition edges `sk-def-sfb-module-lower-shriek`,
`sk-def-sfb-module-derived-pushpull`, `def-sfb-finite-lower-star`, `def-sfb-module-lower-star`,
and `det-def-sfb-constructible-tor-amplitude`. The retained tool approval
`lem-exc-open-closed-detection` keeps its original position. No approval was added.

The exact derived functor, module coherence, and open-closed results already proved in the
source library replace the corresponding reconstruction interfaces. In particular no separate
proof of the ringed-topos derived-composition theorem is needed for this argument: the
source `CompConjugate` theorem gives the needed normalized compositor. The identity helpers
use the existing source module `lowerStarId`; the profinite-point identity uniqueness theorem
is not used to supply their linearity.

These old direct proof-dependency edges are removed from the parent node:

- `lem-weil-pbc-profinite-point-pullback` (return point 6; source `lowerStarId` suffices)
- `lem-sfb-alpha-iso`
- `lem-weil-pbc-proetale-immersion-limit-preservation`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `sk-def-sfb-module-lower-shriek`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-exact-functor-derived-functor`
- `prop-pur-kinjective-resolutions-exist`
- `sk-def-sfb-module-derived-pushpull`
- `lem-weil-proetale-weakly-etale-localization`
- `def-sfb-finite-lower-star`
- `def-sfb-module-lower-star`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-proper-fp-permanence`
- `det-thm-sfb-proper-base-change-finite`
- `det-thm-sfb-proper-base-change-integral`
- `det-thm-sfb-proper-base-change-rational`
- `det-def-sfb-constructible-tor-amplitude`
- `det-sf-determination-localizing`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`

The finite/integral/rational proper-base-change declarations remain in the proof of the
existing `properOpenInterchange` theorem, which proves all standard coefficient cases here.
The rational interface also supplies the finite-extension side of the coefficient comparison
still needed below the new boundary node. The elementary proper permanence, exactness and
generator-preservation results remain needed below that node. None is claimed globally
unnecessary.
The localizing isomorphism-locus module is unnecessary here because its vanishing-kernel
special case is proved directly from the defining intersection. This is the same generator,
exactness and sums route; it avoids adding a shift-compatibility theorem for the comparison.
No unit statement or realized unit step is withdrawn, and no module is deleted.
The composition unit's `det-sf-comp-composition-interchange` is used as an independent tool
for the standard-coefficient support calculation, specialized to the identity proper edge.
Its Lean module does not import this item, and its DAG proof dependencies do not contain the
refinement node. This shorter realization retains the required generator support calculation,
single-compactification sums and open-closed detection. The new tool dependency is recorded
in `proof_deps` for independent review; no maintainer approval is added to `tool_uses`.

Source-library `CompConjugate`, exact derived whiskering coherence in `MapDerivedCategoryMate`,
and derived `OpenClosed` supply already proved facts. The corresponding existing normalization
and detection nodes record their mathematical roles. The localizing-closure existence theorem
is a generic tool for the closure argument, not a replacement for compactification coherence.

## Where the brief, the DAG or earlier work was wrong

The dependencies do not directly supply the entire generator step in its current coefficient
signature. `IsLocalizingAdmissibleCoefficient` has a separate all-continuous-map
`Profinite.continuousMapRingObj (PadicAlgCl ell)` compatibility case. The current rational
proper-base-change interface instead uses `Profinite.padicAlgClRingObj ell`, whose sections
are finite-subextension-valued. These are not identified by any argument in this delivery. Indeed a sequence of
algebraic elements with unbounded degrees can be scaled to converge to zero; the resulting
continuous map from a convergent sequence has no image in a single finite subextension.
Thus the sectionwise finite-subextension colimit argument cannot simply be reused for
the compatibility ring.
The standard cases, despite their different coefficient presentations, are handled by the
existing proper/open interchange theorem. Only the coefficient comparison for the separate
all-continuous-map model, on the generator closed-support calculation, remains explicit work
of the new boundary lemma. No target
statement or coefficient disjunct was weakened.

The source blueprint's `det-sf-determination-localizing` formulation assumes globally
sum-preserving functors; the declared single-compactification interface supplies preservation
of sums with vertices in Loc(Dctf). The proved kernel-intersection argument uses precisely
that relative preservation and avoids assuming an unprovided global instance.

The unit record still carries the older etale-origin statement and realized node, while this
item follows the current main-20261015 localizing statement. The packet keeps the current
unit route through single-compactification sums, generator proper base change, and open-closed
detection, and leaves the unit record untouched.

The resumed sandbox's dispatcher clock metadata changed across provider interruptions
(the earlier summary recorded start 1792426526.0627887; current start 1792430220.4459267).
No budget metadata was edited. The decomposition is by the independent source step, not
by elapsed time.

## New nodes

`lem-sf-refinement-boundary-vanishing` is precisely the separate all-continuous-map coefficient case of the source's
closed-complement calculation on a constructible sheaf placed in degree zero.
Bounded truncation dévissage is proved in the parent from the existing source theorem. It has its own public module, verbatim Lean
statement, complete proof plan and source. The zero input and empty boundary vanish
immediately; the identity refinement reduces to the existing disjoint-support extension-by-zero
vanishing; boundary preservation is necessary for a nonidentity refinement. These checks
exclude the familiar counterexample where extra open preimages reach the boundary.
Separate Lean checks prove zero input, identity refinement for every unbounded input,
and arbitrary restriction to an empty boundary; all three axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound` (5.0 seconds).

Blueprint searches for “boundary vanishing” and “closed restriction” found no existing node
with this support statement (the latter found only open-closed detection). Actual LeanSearch,
LeanFinder, Loogle and Mathlib grep queries are recorded in the node and `searches.jsonl`;
none stated the geometric generator calculation. The new node is a single smaller hole for just one coefficient model; the main proof
combines it with the proved standard-coefficient support, kernel and coherence arguments.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
