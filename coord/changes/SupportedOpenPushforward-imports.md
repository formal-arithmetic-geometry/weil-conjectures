# SupportedOpenPushforward imports

## Reason
The item uses the adjunction and derived restriction modules only through its proof
components. Their imports are therefore private, as required by the stage-3 import rule.
The old public import exposed proof infrastructure to three downstream modules.

## Old
`SupportedOpenPushforward.lean` had `public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
and `import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`.

## New
The item imports its three proof/component modules privately. The local-comparison component
privately imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` and
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction` | unclaimed | no effect; it uses the item theorem only |
| `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` | unclaimed | no effect; it uses the item theorem only |
| `Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing` | B2 | no effect; it uses the item theorem only |
| `Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand` | B2 | verified unchanged source compiles against the delivered overlay; no statement or proof effect |

## Status
landed 20261012T154245-L-2435293 2026-10-12 (merge of deliver/R2/Sheaf.AlgebraicGeometry.SupportedOpenPushforward)

## Direct importer verification

`Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand` is currently held by group B2.
Its source was compiled unchanged against the delivered overlay (including all delivered
modules) with `lcompile.py`; compilation succeeded. The private-import changes have no
effect on its theorem statement or proof: it continues to use the supported-open-pushforward
theorem and its own proof-only imports resolve as before.

### Current source supplied for review

The following is the current source of
`lean/Sheaf/AlgebraicGeometry/SupportedKoszulUnitSummand.lean`, copied verbatim from the
repository and compiled against the delivered overlay:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.CategoryTheory.Retract
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import Sheaf.AlgebraicGeometry.SupportedOpenPushforward

/-! # The supported Koszul summand forces the open unit

Source: Stacks Project, Tag 0A9A.
(blueprint: lem-pc-supported-koszul-unit-summand).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Adding the supported Koszul summand forces the open-restriction unit to be an
isomorphism under shifted orthogonality. This does not assert detection or use induction.
Source: Stacks Project, Tag 0A9A, supported Koszul construction and unit paragraphs.
(blueprint: lem-pc-supported-koszul-unit-summand).

Proof:
1. Put Z = X minus U. On affine V the complement W of Z intersect T is the union of
   U intersect V and V minus T. It is quasi-compact by quasi-separatedness and hTc.
   Express W as finitely many principal opens and form their Koszul complex A on V.
   It is perfect with cohomology supported on Z intersect T, which is closed in X
   and contained in V. Its derived open pushforward A' is perfect and supported on T
   by supported_open_pushforward, and agrees with exact extension by zero.
2. Set E = Q biproduct A'. Perfectness, quasi-coherence and support are preserved by
   finite sums. The biproduct inclusion and projection exhibit Q as a retract of E.
3. Orthogonality of a supported K to E implies orthogonality to A'. Exact open
   extension-by-zero adjunction gives orthogonality of K restricted to V to A.
   koszul_open_orthogonality identifies K on V with pushforward from W.
4. On W its support T intersect W lies in U intersect V and is closed in W.
   supported_open_pushforward identifies this restriction with pushforward from
   U intersect V. Derived direct-image composition and open-restriction base change
   identify the unit of restriction to U on V with this isomorphism. On U the unit
   is also invertible. The cone has zero cohomology stalks on the cover U,V and thus
   is zero, making the global unit invertible. Uniqueness of a right adjoint transports
   this assertion to any R and adj as in the statement. For U empty, this is affine
   Koszul detection; for U top the unit is already invertible. -/
theorem exists_supported_koszul_unit_summand
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (V : X.affineOpens) (hU : IsCompact (U : Set X))
    (hcover : U ⊔ (V : X.Opens) = ⊤)
    (R : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (Q : schemeDerivedQCohCategory X) (hQ : Scheme.IsPerfect X Q.obj)
    (hQT : (∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj Q.obj).val.presheaf x)))) :
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      Nonempty (Retract Q.obj E.obj) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) →
        IsIso (adj.unit.app K.obj) := by
  sorry

end AlgebraicGeometry
```
