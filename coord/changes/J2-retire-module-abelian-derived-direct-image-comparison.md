# AlgebraicGeometry.Etale.moduleAbelianForget_injective_evaluation_acyclic

## Reason

Retire the Sheaf forwarding shim under the human-approved twin retirement.
The current upstream derived-comparison module publicly imports the coefficient
comparison API; the listed missing names have moved there, rather than disappeared.
Its private evaluation-acyclicity helper has the identical type and is accessible
by `import all`, so RawModuleFreeSourceAcyclic needs no replacement proof.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Canonical derived direct image comparison for module coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)
-/

@[expose] public section

-- This shim retains a private API used by an `import all` consumer.
set_option linter.privateModule false

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private alias upstream_evaluation_acyclic := moduleAbelianForget_injective_evaluation_acyclic

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9. -/
private theorem moduleAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  exact upstream_evaluation_acyclic Λ X G W n

end AlgebraicGeometry.Etale
```

Consumers imported `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
(with their existing public/private/import-all visibility).

## New

The shim is withdrawn using deleted.txt. Consumers import
`WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
with the same visibility. Duplicate existing imports of the twin are consolidated.
Every consumer public signature and definition body is unchanged.
In UnboundedAbelianExchangeComparison the two private duplicate underived
comparison proofs are removed in favour of the identically stated, proved
upstream ModuleAbelianUnderivedExchange theorem. Its import is private. The
public theorem proof text is unchanged and its call now resolves to that
canonical declaration. This eliminates duplicate proof checking: the full
adapted file compiles in 48.1 seconds after the original and the initial
import-only version exceeded 60 seconds. This reuses an existing proof; no
file or proof is split and no timeout is raised. All other consumer bodies
remain unchanged.
The evaluation-acyclicity DAG node points directly to the upstream helper.
The other two listed nodes already point to the correct upstream defining modules;
their notes are refreshed to record the completed retirement.
No upstream source, target statement, mathematical dependency or unit route changes.
No proof is replaced by sorry and no definition is hollowed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianHigherDirectImageFilteredColimit | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleCyclicModuleOfAbelian | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyConventions | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.NTorsionModuleLift | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.PrimeCurveCharPHighVanishing | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison | unclaimed | Upstream import; reuse canonical underived proof instead of two private duplicates. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Direct upstream import, same visibility; body unchanged. |
| Sheaf.Paper.UnboundedProperOpenInterchange | S2 | Remove only the obsolete private shim import; retain its existing canonical import and all body text. |

The preflight reports that Sheaf.Paper.UnboundedProperOpenInterchange is now held
by S2. Its only changed line removes the obsolete private shim import (original
line 42); the separate existing upstream import remains in its original position.
There is no original compiler error to report, since that existing canonical
import already supplies the API. The human's explicit RETIRE instruction requires
removing every reference to the withdrawn copy, and the retirement adaptation
exception applies. No signature, visibility, statement, definition or proof is
changed in this held consumer. See report.md, Forced adaptations.

The five absent listed consumers still in quarantine (PrimeCurveArtinSchreierKernel,
AffineLineOrdinaryInvariance, FiniteHorizontalShriekMate, RelativeSupportBottomDescent,
and SfLocalizationAllStages) are preserved archives, not active Lean modules.
Their rework assignments must apply the same import rename when restoring them.
The other absent listed consumers have already been retired. Nothing is withdrawn
from these consumers or their DAG routes by this packet.

## Status

landed 20261020T211739-L-3496230 2026-10-20 (merge of deliver/J2/Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison)
