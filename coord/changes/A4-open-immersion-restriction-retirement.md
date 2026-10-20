# AlgebraicGeometry.openImmersion_restriction_derived_properties

## Reason

Complete the zero-sorry retirement repair listed in `coord/retire-items.tsv`.
The theorem already has an identical, fully proved declaration in
`WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`.
Its public import of `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`
also provides the sectionwise additive instance at line 669, so the extra
`AlgebraicGeometry.restriction_additive` helper is redundant.

Withdraw only the duplicate Sheaf module and migrate its three live direct
consumers. Preserve every upstream declaration and all consumer signatures,
visibility, public imports, and proof lines except the four helper applications.

## Old

The retired module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.AlgebraicGeometry.Restrict

/-! # Exactness and K-injective preservation for open-immersion restriction
Source: Stacks Project, Tag 08BS and sectionwise module limits (Tag 01AH).
(blueprint: lem-pc-open-immersion-restriction-derived-properties).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Open restriction is additive because its maps are sectionwise the original module maps.
Source: Stacks Project, Tag 08FE, proof; sectionwise module operations.
(blueprint: lem-pc-open-immersion-restriction-derived-properties). -/
instance restriction_additive {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (Scheme.Modules.restrictFunctor j).Additive := ⟨by
  intro M N f g
  ext U x
  rfl⟩

/-- Restriction along any open immersion is exact and preserves K-injective complexes.
Source: Stacks Project, Tag 08BS and sectionwise module limits (Tag 01AH).
Proof: identify the source with the image open subscheme. Under this isomorphism,
restriction is the composite of the localized-site restriction, the exact equivalence
from the localized site to the open subscheme, and the equivalence induced by the
source isomorphism. The first functor preserves finite limits and colimits, since
sections over opens in the source are the same sections in the target. It preserves
K-injectives by Tag 08BS: extension by zero is an exact left adjoint, and the adjunction
identifies Hom complexes against acyclic complexes. The two equivalences are exact and
preserve K-injectives. Transport these properties across the natural restriction
isomorphism and compose them. This also covers an empty image open.
(blueprint: lem-pc-open-immersion-restriction-derived-properties). -/
theorem openImmersion_restriction_derived_properties
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) ∧
      (Scheme.Modules.restrictFunctor j).PreservesKInjectiveComplexes := by
  classical
  let e := j.isoOpensRange
  let F := Scheme.Modules.restrictFunctor e.hom
  let G := Scheme.Modules.restrictFunctor e.inv
  let : F.Additive := restriction_additive _
  let : G.Additive := restriction_additive _
  let : F.IsEquivalence := Functor.IsEquivalence.mk' G
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) j.opensRange
  let E := (Scheme.Modules.overEquiv j.opensRange).functor
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  let : R.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open Y.toRingedSpace j.opensRange I⟩
  have h : (R ⋙ E) ⋙ F ≅ Scheme.Modules.restrictFunctor j :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv j.opensRange) F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom j.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι
  exact ⟨inferInstance, Functor.preservesKInjectiveComplexes_of_iso h⟩

end AlgebraicGeometry
```

Each live consumer privately imported
`Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`.
The helper applications were `restriction_additive a` and
`restriction_additive (V.ι ≫ U.ι)` in `NestedOpenSingleDirectImageComparison`,
`restriction_additive j₀` in `PicardAffineStructureModelTransport`, and
`restriction_additive _` in `SelfExtTorResolutionLocal`.

## New

The duplicate module is withdrawn through `deleted.txt`. Its node keeps the
same statement and dependencies and points to the unchanged upstream module:

```lean
theorem openImmersion_restriction_derived_properties
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) ∧
      (Scheme.Modules.restrictFunctor j).PreservesKInjectiveComplexes
```

The three live consumers privately import
`WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`.
Their four named additive-instance applications become `inferInstance`.
The upstream instance is:

```lean
instance {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).Additive where
  map_add := rfl
```

## Users

Source-only `tools/downstream.py` with both declaration names lists four live
transitive consumers. The three direct consumers have no current claim files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NestedOpenSingleDirectImageComparison | unclaimed | Replace private import; infer two additive instances. Signature unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureModelTransport | unclaimed | Replace private import; infer one additive instance. Signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionLocal | unclaimed | Replace private import; infer one additive instance. Signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | unclaimed | Indirect consumer only; no source change and no direct reference to either declaration. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization (quarantine) | rework archive | Same mathematical dependency preserved by the node's upstream attachment. On restoration, replace the public import by the upstream twin and its two helper applications by inferInstance. Archive and rework row preserved. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation (quarantine) | rework archive | Same mathematical dependency preserved by the node's upstream attachment. On restoration, replace its import by the upstream twin and its helper application by inferInstance. Archive and rework row preserved. |

All three adapted consumers compile without warnings via `lcompile.py`:
`NestedOpenSingleDirectImageComparison` 14.7 s,
`PicardAffineStructureModelTransport` 31.3 s,
`SelfExtTorResolutionLocal` 3.6 s.
A separate compiled upstream check synthesizes the additive instance, applies
this exact theorem statement, and prints only `propext`, `Classical.choice`,
and `Quot.sound` as the theorem's axioms.

All five DAG parents retain the same node dependency:
`new-j3-self-ext-tor-local`,
`lem-pc-perfect-hom-open-mate-resolution-normalization`,
`lem-pc-nested-open-single-direct-image-comparison`,
`lem-sc-picard-affine-structure-model-transport`, and
`lem-sc-picard-affine-structure-projective-representation`.
The unit's realized arrays are empty; its statement and proof route are unchanged.
No definition, target statement, or target meaning changes.

## Status

landed 20261020T235533-L-1186969 2026-10-20 (merge of deliver/A4/Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties)
