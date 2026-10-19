## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.compactification_localizing` with its signature
unchanged, retaining the open/proper/composite route. A private intersection and closure-minimality
argument proves objectwise preservation from the proper-image hypotheses. Ambient exactness, lifting
diagrams into the middle closure, and composition prove the other three conjuncts.

The new ProperLocalizingAdmissibleCoefficients module proves the seven-case coefficient wrapper. It
reuses the proved constantModelCtf_coefficientIso theorem for finite constant models and Tor
amplitude, and constantModelConstructibleFiniteTor_wellDefined for isomorphism invariance. Its
private helpers transport localizing closures and coproducts across coefficient isomorphisms. The
six literal representatives use the existing proper coefficient theorem. The finite annihilator
condition is evaluated at 1.

The new ProperLocalizingContinuousAlgCl module proves the all-continuous representative from two
separate geometric results. Its coproduct proof uses the lower-tail estimate, truncation, generic
bounded-below continuity, cohomology detection, and a proved support shrinking argument to handle
every existing Type(u+2) coproduct. The nonzero-support lemma is reused from AmbientIndDerivedSums
rather than reproved. The two geometric results have their own modules and nodes, as described
below.

The additional ContinuousAlgClConstructibleTor module proves finite Tor amplitude of every bounded
constant-model constructible complex over the full continuous algebraic closure on a noetherian
scheme. It generalizes the existing local finite-free argument to totally disconnected normed
fields, transports it through the universe lift, proves flatness by detecting tensor monomorphisms
on the strata, and applies the library bounded Postnikov devissage. The proper finiteness hole now
asks only for constructibility of higher proper images of a single constructible sheaf. The
additional ContinuousAlgClLocalFree module exposes the shared, proved local finite-free theorem. The
bounded-complex theorem is proved by identifying constant models with stratified local finite
presentation, applying the proved generic Serre argument, and using the finite Postnikov filtration
and shift compatibility. Boundedness is derived from the retained lower-tail estimate and the
bounded-below right-derived comparison. This is a strict reduction of that geometric obligation.

The compact-monodromy finite coefficient theorem is already proved as
`PadicAlgCl.exists_finiteDimensional_forall_mem` in
WeilConjectures.RepresentationTheory.IntegralModel. The sheaf-level finiteness module imports this
existing source-library result. The finite-coefficient proper-heart theorem is also reused; its integral arguments
are not new obligations here. IntegralModel also already proves
`PadicAlgCl.exists_lattice_of_forall_mem`, supplying the invariant lattice once compactness bounds
the matrix coefficients. The remaining obligations are geometric constructibility and the scalar
comparison for the actual continuous coefficient. The duplicate new module and node from the working
packet were moved to scratchpad before publication; no shared file or published node is deleted.

No existing public signature or definition changes. No other held module is edited. The
complex-level finiteness reduction compiles without errors or warnings. The
constructibility-equivalence helper, local finite-free theorem and finite Tor theorem use exactly
propext, Classical.choice and Quot.sound. The assembly theorems still depend on named imported and
split-off holes. The continuous proper wrapper derives the target scheme's Noetherian instance from
finite type and quasi-compactness. The assigned signature was compared verbatim against the current
repository and is identical. All new node signatures match their Lean declarations verbatim. All
eight retained delivery modules compile together without errors or warnings. A separate consumer
probe importing LocalizingExceptionalAdjoint compiles against the packet. Identity-map edge checks
compile independently of the two new holes: the sheaf-level proper-finiteness conclusion holds in
every degree, and the lower-tail conclusion holds with c=0 for every complex, without a
localizing-membership assumption. The existing finite coefficient and invariant lattice theorems
also use only the standard three axioms. The assigned theorem and the proper-finiteness assembly
still report sorryAx, as expected from their named geometric and existing imported dependencies.
An earlier delivery dry run found missing LeanSearch metadata on three new nodes; actual
LeanSearch calls were run and recorded alongside the existing Loogle/LeanFinder and grep searches.
Automatic axiom probes have timed out for the assigned module, the finiteness assembly and the Tor
module, while the direct axiom checks above completed; the tool leaves these probes to be repeated
at merge. The corrected dry run passed compilation and preflight at commit 93030ace62, with review
class CODEX. Only this report was updated afterwards to record the result.

## Proved and sorry left

Closed the original module's only hole:
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_localizing`
(det-sf-comp-coherence-single): 1 of 1, with zero sorry left in the assigned module. Also proved the
new public theorems `AlgebraicGeometry.ProEtale.CondensedRing.properLocalizingHypotheses_admissible`
(det-sf-comp-proper-admissible-hypotheses) and
`AlgebraicGeometry.ProEtale.CondensedRing.properLocalizingHypotheses_continuousAlgCl`
(det-sf-comp-proper-continuous-algcl), including their coefficient transport and coproduct
arguments. Also proved `AlgebraicGeometry.ProEtale.continuousAlgCl_bounded_finiteTor`
(det-sf-comp-continuous-algcl-constructible-tor), with zero new holes. Also proved
`AlgebraicGeometry.ProEtale.continuousAlgCl_lf` (det-sf-comp-continuous-algcl-local-free) and
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_finiteness`
(det-sf-comp-continuous-algcl-finiteness), with zero holes in either module.

Added exactly two holes, each a public theorem with only `by sorry` as its proof:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_heart_finiteness`
  (det-sf-comp-continuous-algcl-heart-finiteness): constructibility of higher proper images of one
  constructible sheaf for the actual all-continuous-map algebraic-closure ring.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_lowerTail`
  (det-sf-comp-continuous-algcl-lower-tail): a uniform lower-tail estimate on the localizing closure
  for the same coefficient.

This is a decomposition: one original hole closed and two strictly smaller geometric holes added,
net -1. The first asserts sheaf-level constructibility without complex devissage, bounds, Tor
amplitude or sums; the second asserts a cohomological bound without finiteness or sums. Their
assembly, all coefficient transport, and the compactification argument are complete Lean proofs.
Existing imported declarations may still contain sorry; no global axiom-free claim is made.

## No longer needed

The unpublished CompactAlgebraicClosureDescent module and its duplicate node are removed from this
packet: the existing IntegralModel theorem proves precisely its conclusion, with weaker topological
hypotheses. No shared module is withdrawn. The duplicate private small-support proof is also removed
in favor of the proved generic helper in AmbientIndDerivedSums.

The conditional theorem `proper_image_localizing_proper` is not used: closure preservation is
derived directly from ProperLocalizingHypotheses. Its module and node remain needed for the
coefficient theorem and predicate. The main module replaces its private direct import with
ProperLocalizingAdmissibleCoefficients and adds LocalizingClosureExistence. No original
open-immersion dependency is pruned.

Exploratory imports of Mathlib's FullSubcategory module,
Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts and
Sheaf.CategoryTheory.CompactTestsRightAdjointCoproducts are removed. The latter two full theorems
are not needed: the generic truncation and support arguments are proved using the existing proved
small-support lemma of AmbientIndDerivedSums. Their nodes are removed from the new continuous
wrapper's proof dependencies. The duplicate private proofs of finite-presentation, constant-model,
boundedness and Tor transport are removed in favor of CondensedCoefficientIsoConstructible and
ConstantModelTorAmplitude. ContinuousAlgClLocalFree exposes only the raw module/pullback definitions
required by its statement; its broader CondensedConstantConstructibility import is removed. The
direct MapModMonoidal and Monoidal.Equivalence imports are removed. No source-library module or
blueprint unit is withdrawn or bypassed. No change record is needed because existing public
signatures, definitions and visibility are identical.

## Where the brief, the DAG or earlier work was wrong

The proper coefficient theorem accepts literal membership in six representatives; the assigned item
accepts an isomorphism-invariant admissibility predicate. Moreover, all continuous maps into
PadicAlgCl and finite-subextension-valued sections are different condensed rings. The current
predicate has seven cases after A4's recorded repair. This packet supports that seventh case using
the existing literal theorem and retains the all-continuous case separately. It neither deletes that
case nor identifies the rings.

The existing rational proper finiteness and unbounded-window declarations apply to finite extensions
or the finite-subextension-valued coefficient. They cannot directly supply the two retained
all-continuous geometric results. CondensedFieldLfpLocalTriviality also requires a
finite-dimensional coefficient extension; its proof only needs total disconnectedness, so the new
finite Tor module generalizes that argument. It reuses proved constantModel_lfp from
CoefficientHeartLisseRestriction instead of the still sorried duplicate
HasFiniteConstantLocalModel.isLocallyFinitelyPresented. Constructibility stability and
exceptional-preservation routes import this item and would make an import cycle. The two splits
correspond to proper finiteness and the uniform proper window in the source, rather than a renamed
compactification theorem or a repackaged hypothesis.

The constructibility equivalence uses the raw pro-etale pullback explicitly, avoiding its name
collision with normalized coefficient pullback. This changes no public API. An expensive
continuous-case compile was traced to unfolding rightDerivedFunctor, mapDerivedCategory,
monoidalClosed and upperStarFromPoint. Local irreducibility of these definitions prevents that
unfolding; no global definition or compile limit changes. Earlier dry runs were refused by the
split-off proof policy; proof work continued. No launcher or project tool was modified. The resumed
budget metadata changed from start 1792423330.9513497 to 1792426704.6120632, and then to
1792429669.8072855 without a worker edit; proof work continued under the original brief.

## New nodes

`det-sf-comp-proper-admissible-hypotheses`, in Sheaf.Paper.ProperLocalizingAdmissibleCoefficients,
records the proved seven-case and coefficient-isomorphism transport argument.

`det-sf-comp-proper-continuous-algcl`, in Sheaf.Paper.ProperLocalizingContinuousAlgCl, records the
proved assembly from proper finiteness and a uniform lower-tail estimate, including bounded-below
coproduct comparison and support shrinking.

`det-sf-comp-continuous-algcl-finiteness`, in Sheaf.Paper.ContinuousAlgClProperFiniteness, records
the separate proper finiteness assembly from the separate heart theorem by Serre closure and bounded
Postnikov devissage; its proof is complete.

`det-sf-comp-continuous-algcl-lower-tail`, in Sheaf.Paper.ContinuousAlgClProperLowerTail, records
the lower-tail assertion from sk-lem-proper-unbounded-window and remains a named sorry.

`det-sf-comp-continuous-algcl-constructible-tor`, in Sheaf.Paper.ContinuousAlgClConstructibleTor,
records the proved rational finite Tor assertion independent of proper pushforward. No sorry is
added in this module.

`det-sf-comp-continuous-algcl-heart-finiteness`, in
Sheaf.Paper.ContinuousAlgClProperHeartFiniteness, is the remaining sheaf-level proper
constructibility result. The former complex-level finiteness hole is now proved from it by bounded
Postnikov devissage.

`det-sf-comp-continuous-algcl-local-free`, in Sheaf.Paper.ContinuousAlgClLocalFree, exposes the
proved local finite-free result shared by the finite Tor proof and the complex-level proper
finiteness devissage. It has no hole. This extraction records the actual reusable statement in the
DAG; it is not a split to change the compilation limit.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
