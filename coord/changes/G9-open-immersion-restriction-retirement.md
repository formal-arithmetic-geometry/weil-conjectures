# AlgebraicGeometry.openImmersion_restriction_derived_properties

## Reason

Retire the duplicate listed in `coord/retire-items.tsv`, following the human's
2026-10-20 hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
The upstream twin proves the identical theorem. Its public import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` also supplies the
instance `(Scheme.Modules.restrictFunctor j).Additive` at line 669.
The copy's extra named instance `AlgebraicGeometry.restriction_additive` is
therefore unnecessary. Replace its four live call sites by `inferInstance`.
No upstream file or target statement changes. No proof is replaced by a hole.

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

Live consumers privately imported
`Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`.
`NestedOpenSingleDirectImageComparison` called `restriction_additive a` and
`restriction_additive (V.ι ≫ U.ι)`; `PicardAffineStructureModelTransport` called
`restriction_additive j₀`; `SelfExtTorResolutionLocal` called `restriction_additive _`.

## New

The duplicate module is withdrawn through `deleted.txt`. Its DAG attachment points to
`WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`, whose
existing declaration has exactly this statement and a complete proof:

```lean
theorem openImmersion_restriction_derived_properties
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) ∧
      (Scheme.Modules.restrictFunctor j).PreservesKInjectiveComplexes
```

The three live direct consumers privately import that upstream module.
Each of the four instance expressions above becomes `inferInstance`.
Existing consumer signatures, visibility, public imports, and all other proof lines
are preserved. The node's auxiliary-declaration list drops the retired named instance;
the mathematical statement, proof plan, and dependencies stay the same.

## Users

The source-only `tools/downstream.py ... --uses restriction_additive
openImmersion_restriction_derived_properties` found the following four live downstream
modules. All three adapted modules were unclaimed when checked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NestedOpenSingleDirectImageComparison | unclaimed | Replace private import; infer the two additive instances. Statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureModelTransport | unclaimed | Replace private import; infer one additive instance. Statement unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionLocal | unclaimed | Replace private import; infer one additive instance. Statement unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | unclaimed | Indirect importer only; no use of the retired declarations. No source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization (quarantine) | rework archive | Mathematical dependency preserved by the same node, now attached upstream. On restoration, import the upstream twin and replace two restriction_additive calls by inferInstance. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation (quarantine) | rework archive | Mathematical dependency preserved by the same node, now attached upstream. On restoration, import the upstream twin and replace one restriction_additive call by inferInstance. |

All three migrated direct consumers and the unchanged indirect consumer compile
cleanly against the sandbox overlay. The source parser confirms every adapted
consumer signature is unchanged. A compiled upstream-theorem check lists only
the permitted axioms and synthesizes the upstream restriction-additive instance.

The last two are absent from `lean/` and listed in `coord/rework.tsv`; their archived
files and Lean attachments are preserved. They are not withdrawn or restored here.
This retirement preserves their planned theorem dependency, including all five DAG
parents. Every parent continues to cite the same node and theorem. The unit's realized
arrays are empty, and no unit route changes.

## Status

landed 20261020T221205-L-4155299 2026-10-20 (merge of deliver/G9/Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties)
