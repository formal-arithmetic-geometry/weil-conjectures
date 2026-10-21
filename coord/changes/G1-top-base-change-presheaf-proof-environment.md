# AlgebraicGeometry.top_base_change_presheaf proof elaboration environment

## Reason

The static command scan requests this record for
`Sheaf.AlgebraicGeometry.TopBaseChangePresheaf`: local irreducibility attributes,
instance-search transparency, and elaboration options are classified as commands
that may affect importers. They keep the proof at the named construction APIs and
retain its proof bindings. The diagnostic compile passed in 35.8 seconds; previous
versions exceeded the delivery's 60-second limit.

All four existing public construction bodies, all existing public signatures, and
all public imports remain verbatim. The attributes are local and the options apply
only while this file is elaborated. New helper theorems are private and proved;
the added import is private and used only by proofs. No target statement or meaning
changes, and no target statement review reopens. No source-library module changes.

## Old

The existing theorem signature was:

```lean
theorem top_base_change_presheaf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (q : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (q : ℤ))
    (V : S.Opens) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    topBaseChangeClass f F I V (f ⁻¹ᵁ V) rfl R q ≫
        Hom.app (topBaseChangeAdjoint f g F q hC) V =
      moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
          ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
        (topBaseChangeRestrictedUnit (pullback.snd g f) F (f ⁻¹ᵁ V)) q ≫
      topBaseChangeClass (pullback.fst g f) ((tensorPullback (pullback.snd g f)).obj F)
        J (g ⁻¹ᵁ V) ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))
        (flatBaseChangeOpenEquality f g V) R' q
```

Its proof was `by sorry`. Before the first construction, the file had:

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
```

There were no further local irreducibility commands or private proof helpers.

## New

The theorem signature remains verbatim:

```lean
theorem top_base_change_presheaf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (q : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (q : ℤ))
    (V : S.Opens) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    topBaseChangeClass f F I V (f ⁻¹ᵁ V) rfl R q ≫
        Hom.app (topBaseChangeAdjoint f g F q hC) V =
      moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
          ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
        (topBaseChangeRestrictedUnit (pullback.snd g f) F (f ⁻¹ᵁ V)) q ≫
      topBaseChangeClass (pullback.fst g f) ((tensorPullback (pullback.snd g f)).obj F)
        J (g ⁻¹ᵁ V) ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))
        (flatBaseChangeOpenEquality f g V) R' q
```

It now has a complete assembly from the top-edge theorem, the proved transpose,
and the separate local-cocycle theorem. One hole in that new local-cocycle theorem
is reported as a decomposition, not a net proof completion.

The initial commands are:

```lean
set_option cleanup.letToHave false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local irreducible] Scheme.Modules.tensorPullback
attribute [local irreducible] limit limit.π
```

After the proved private adjunction-normalization helper:

```lean
attribute [local irreducible] tensorPullbackSectionAdjunction resolutionSectionClass
  moduleCohomologyFMap Functor.rightDerivedFunctor Functor.rightDerived
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
  InjectiveResolution.isoRightDerivedObj derivedPullbackTopCohomology
  pinnedModulePullbackComparisonAt RingedSpace.topEdgeLocalClass
  RingedSpace.topEdgeLocalLeray RingedSpace.topEdgeInverseLocalClass
```

Immediately after `topBaseChangeDelta`:

```lean
attribute [local irreducible] topBaseChangeDelta
```

After the private construction equations, before the item theorem:

```lean
attribute [local irreducible] topBaseChangeClass topBaseChangeRestrictedUnit
  topBaseChangeAdjoint derivedSquareUnitMap derivedSquareRightComparison
  schemeSingleCohomologyComparison
```

Scoped transparency settings on the private equations and item proof keep the
constructors folded. The original unfolding settings are scoped to the existing
adjoint definition, and narrow unfolding is permitted in the source-class equation
and final definitional transport. No exported reducibility attribute changes.
The canonical total/classical comparison is constructed in the new local-class
module; it is used only in the item's proof and private helper signatures.

## Users

The read-only command
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.TopBaseChangePresheaf --uses
topBaseChangeRestrictedUnit topBaseChangeClass topBaseChangeDelta
topBaseChangeAdjoint top_base_change_presheaf`
reports zero downstream Lean modules and only this item as a textual user.
The DAG parents remain attached: this is not a withdrawal or an assertion that
zero current Lean importers makes the item unnecessary. No consumer needs an
adaptation because every existing signature and construction is unchanged.

A separate temporary importer was compiled in the same ordered sandbox set as all
three production modules. It checked all five existing public declarations and
printed the item's axioms. The importer compiled cleanly in 3.1 seconds; the three
production modules reused their current compiled artifacts. The axiom output
contains the standard axioms and admitted theorem dependencies, as expected for
the decomposition documented in the report. The temporary probe is not delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TopBaseChangePresheaf | G1 | Proof assembly and local elaboration commands only; existing public interface unchanged. |

## Status

landed 20261021T233708-L-851056 2026-10-21 (merge of deliver/G1/Sheaf.AlgebraicGeometry.TopBaseChangePresheaf)
