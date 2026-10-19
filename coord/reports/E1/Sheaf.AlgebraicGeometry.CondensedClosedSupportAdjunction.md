## What changed

Only `lean/Sheaf/AlgebraicGeometry/CondensedClosedSupportAdjunction.lean` and its existing
node `det-lem-formal-closed-support-adjunction` change. Existing public signatures and
public definitions are unchanged. Proved private helpers lift abelian counits and supported
units to noncommutative module objects, compute the zero open restriction of a closed
pushforward, and lift the extension-by-zero adjunction.

The support adjunction is constructed by an explicit natural kernel-factorization Hom
bijection, with precisely the prescribed counit. The Hom-complex isomorphism is assembled
componentwise and checked against its differential. The injective-unit argument extends a
map across a monic extension counit and verifies the splitting using the two adjunctions.
The recorded derived functor is compared with the upstream functor by its universal property.

The new proof imports are
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono`, and
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`.
All import-direction checks passed. On resumption, the unchanged Lean file compiled
against the current server build in 10.9 seconds (exit code 0), with no diagnostics.
The generic source `mapModLeft` API applies to a monoid object without a commutativity
assumption; the proof does not apply the
commutative-coefficient wrapper at noncommutative coefficients.

## Proved and sorry left

Eight of the original eleven holes closed, with no holes added and no split-offs.
All declaration names below have namespace `AlgebraicGeometry.ProEtale.CondensedRing`.

Proved:

- `closedSupport_additive`.
- `closedSupportKernelComparison_isIso`.
- `existsUnique_closedSupportAdjunction`.
- `closedSupport_leftExact`.
- `closedSupport_open_isKInjective`.
- `closedSupport_globalRHom`.
- `closedSupport_injective_unit_epi`.
- `closedSupport_recordedDerived`.

Three original named theorem holes remain, all attached to
`det-lem-formal-closed-support-adjunction`:

- `closedSupport_lowerStarExact`: the unrestricted signature requires review; see below.
- `closedSupport_triangle`: the degreewise exact sequence must still be localized and
  its boundary descended naturally to derived morphisms, with the canonical derived
  counit and unit identified.
- `closedSupport_fiber`: still needs the comparison of the actual shifted mapping cone
  of the open unit with the support kernel, including transport from arbitrary
  K-injectives to representatives with injective terms.

The completed eight proofs do not invoke `closedSupport_lowerStarExact`, the triangle,
or the fibre theorem. No definition contains `sorry`, no axiom is added, and the chosen
support adjunction is determined uniquely by its fixed counit.

## No longer needed

Removed these thirteen unused proof imports (relative to the current shared source):

- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

Removed these direct node proof dependencies (and removed their old `tool_uses` approvals
where present, preserving the order of remaining approvals):

- `def-weil-extension-by-zero-presheaf`: source extension by zero is already constructed;
  this proof never constructs the alternative presheaf module model.
- `def-weil-presheaf-modules-sheafification`: no alternative sheafification construction.
- `lem-weil-pbc-proetale-ringed-open-closed`: replaced by the proved abelian supported-unit
  interface and direct empty-base-change computation. No commutative ringed comparison.
- `lem-weil-pbc-ring-sheaves-grothendieck`: the existing `Mod.isGrothendieckAbelian` supplies
  exactly the required category and universes.
- `lem-weil-proetale-weakly-etale-localization`: the source open adjunction already has
  its counit isomorphism; no reconstruction of the localized-site equivalence.
- `lem-weil-pbc-kinjective-total-derived`: use the actual upstream total-derived functor
  and its universal property, rather than a second construction.
- `lem-pur-kinjective-degreewise-existence`: no completed proof uses injective-term
  replacement. This remains a possible tool for the still-open triangle/fibre proofs.

The six additional imports in the current source were added after the preserved attempt.
Their interfaces are either supplied by the retained public imports or unused by the eight
completed proofs. In particular the Hom-complex proof uses the abelian adjunction directly.
The SES-triangle, exact-functor, homotopy-adjunction and K-injective Hom nodes are retained
in the node's unimplemented final steps; they are not claimed pruned. Removing an explicit
import does not claim all of its transitive imports disappear globally. No module is
withdrawn. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: closedSupport_lowerStarExact` has only `[IsClosedImmersion i]`,
whereas this node and the source argument require a quasi-compact open complement.
In the checked-in Stacks source `literature/stacks-project/proetale.tex`,
`lemma-closed-immersion-complement-retrocompact-exact` explicitly assumes the complement
is retrocompact. Its proof uses a finite list of generators up to radical and does not
establish the unrestricted Lean statement. Thus the earlier statement packet silently
strengthened this auxiliary assertion. The theorem is marked at its declaration and is
left unchanged and unproved; no weaker replacement is presented as its proof. A formal
counterexample has not been constructed here. The eight completed proofs avoid this
assertion. The derived-adjunction definition and the remaining triangle/fibre obligations
still have the node's quasi-compact-complement hypotheses, so this does not dispute those
intended conclusions.

The shorter route uses existing proved abelian support and extension-by-zero monicity
interfaces. The new node dependencies record those interfaces. No new `tool_uses`
approval is asserted; approval additions remain the maintainer's responsibility. The
partial node records which source-plan steps still lack Lean proofs.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
