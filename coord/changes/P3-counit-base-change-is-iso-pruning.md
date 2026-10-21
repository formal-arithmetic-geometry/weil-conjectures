# AlgebraicGeometry.Scheme.Modules.isIso_counitBaseChange_of_invertibleDirectImage

## Reason

Repair the no-op return at 405ac4e03c against the current live source. The previous
packet restored an implementation that is now already in the library. There is
no remaining restoration or definition defect to fix. Step 8d of the brief
requires withdrawal when the actual parent argument no longer needs the item.

This is supported by the complete replacement argument already present in
WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme, theorem
AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit. It constructs the
ordinary mate beta, proves its endpoints invertible using base-change stability
of IsInvertibleDirectImage, proves beta nonzero on every residue-field fibre via
pullback_baseChangeMap_map_counit_ne_zero and mateEquiv_counit, and concludes that
beta is an isomorphism using Hom.isIso_of_forall_pullback_ne_zero. Finally
Adjunction.arrowIsoMapCounit and counit naturality give the required arrow
isomorphism. This proof does not import or reference the withdrawn theorem.

The packet updates the sole actual DAG parent to that argument and attaches its
two already proved source-library helper results as nodes. These attachments add
no Lean statement and no hole. A scratch import of the published parent implementation compiled in 9.3 seconds.
Axiom checks of the parent theorem and both helpers report only propext,
Classical.choice and Quot.sound. There is no parent source edit or packet copy. No source-library declaration, public
import, signature, attribute, or non-theorem body is removed or changed.

## Old

```lean
theorem isIso_counitBaseChange_of_invertibleDirectImage
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [LocallyOfFinitePresentation f] [Flat f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M]
    (h0 : SheafOfModules.IsInvertible.{u, u, u}
      (((pushforward f).rightDerived 0).obj M))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr sq.w).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    IsIso ((pullbackPushforwardAdjunction f').homEquiv _ _
      (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)))
```

This complete zero-hole theorem was attached to
lem-pc-counit-base-change-is-iso. The stale parent proof_deps named it and
lem-pc-smooth-flat, although the adopted Lean proof uses the fibrewise route.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/Picard/CounitBaseChangeIsIso.lean through
deleted.txt; landing leaves the required empty module stub. Set the item's
lean attachment to null and clear its retired proof dependencies. Preserve its
mathematical statement and its DAG node as history.

Replace only the parent's proof, proof_deps and proof_origin, and remove its
obsolete duplicated tool_uses entries for lem-pc-rf-base-change-flat-module.
The new dependencies describe the actual existing proof: F base-change stability,
nonzero pullback of the counit, and detection of an isomorphism of invertible
modules on residue fibres. The unit's zero-scheme naturality step is retained.

## Users

A scan of every node's stmt_deps, proof_deps and proof-step uses has one parent:
lem-pc-arrow-iso-pullback-counit. All other mentions of the retired node are
creation/blueprint ancestry, not dependency edges. No unit's realized field
contains the retired node. tools/downstream.py reports zero downstream modules;
searches of both lean/ and quarantine/ for the module and declaration find only
the theorem's own live file. No quarantined consumer is overlooked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | P3 | Withdraw redundant intermediate; 0 holes before and after. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Complete adopted proof and signature remain verbatim; reconcile only its parent DAG proof route; published proof passes import and axiom checks. |

The two private imports removed with the withdrawn module are
Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison and
Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange. Their
files and declarations are retained: other uses are not withdrawn by this packet.
No target statement or definition changes.

## Status

landed 20261021T111404-L-100725 2026-10-21 (merge of deliver/P3/Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso)
