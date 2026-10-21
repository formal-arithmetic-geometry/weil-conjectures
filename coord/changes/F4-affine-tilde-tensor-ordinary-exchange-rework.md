# AlgebraicGeometry.affineTildeTensorOrdinaryExchange

## Reason

Consolidate the duplicate Sheaf coefficient-map definition and ordinary exchange
theorem with their complete adopted implementations. The current declaration
sections are identical after expanding the existing abbreviation
`affineTildeFunctor = affinePushforwardTilde`, ignoring comments and whitespace.
Both original names, signatures, formulas, and proofs remain available through
the same Sheaf import path. No data construction or target meaning changes.

Repair of the return at 52fcc0f4a6c: the older packet also consolidated the
representative. That change already landed in af62f65adee. Its current shared
version is preserved and the stale sandbox copy is removed from this packet.
Only the item module changes; no module is withdrawn.

## Old

Current shared item, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization

/-! # Ordinary affine exchange in tensor coordinates

Source: Stacks Project, Tags 01I9, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) ordinaryCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) ordinaryCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) ordinaryCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


local instance ordinaryExchangeTildeAdditive (C : Type u) [CommRing C] :
    (affineTildeFunctor C).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance ordinaryExchangePullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

/-- The ordinary coefficient map, affine pushforward comparison and derived unit.
This is a concrete map, independent of any derived scalar-extension model.
Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange). -/
def affineTildeTensorOrdinaryTargetMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (φ : A →+* D) (ψ : B →+* D)
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) :
    DerivedCategory.Q.{w}.obj (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M))) ⟶
    (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).obj
      (DerivedCategory.Q.{w}.obj (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let T := affineTildeFunctor B
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let a := affineTildePushforwardComplexMap D B ψ Cg
  exact DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map k) ≫
    DerivedCategory.Q.map a ≫
    (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj Cg))

/-- Ordinary exchange, in unit-normalized affine tensor coordinates, followed by
its right-derived unit. This is independent of any derived tensor model or counit.
Source: Stacks Project, Tags 01I9, 06Y6 (coefficient map) and 08HY (ordinary exchange).
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange).

Proof: on each term, transpose ordinary exchange under tensor pullback along f'.
The defining ordinary mate is pushforward of the p-pullback unit followed by
pushforward composition. Both tensor/tilde isomorphisms take the pullback unit
to 1 tensor q. The canonical affine pushforward comparison is built from the
same tilde unit, sections restriction and tilde counit. Consequently the
transposed arrow sends b tensor q to psi(b) tensor q. The hypothesis on k fixes
exactly these generators; tensor induction gives equality on each term and
complex extensionality gives equality of chain maps. The commutative spectrum
square supplies the scalar-compatibility required in this transposition.
Descend this identity to homotopy and derived categories, respecting the
composition comparisons in moduleHomotopyBaseChange. Naturality of the
right-derived unit moves the inverse tensor/tilde comparison across the final
pushforward unit. This is precisely the displayed equation. The supplied invertible p-counit
normalizes the target representative: its composite with t.hom is the inverse
tensor/tilde comparison. No K-flatness, quasi-coherence or cartesian-square
hypothesis is used here.
Zero complexes and zero rings are included by the same tensor induction. -/
theorem affineTildeTensorOrdinaryExchange
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : A →+* D) (ψ : B →+* D)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))
    (hk : ∀ (i : ℤ) (b : B) (q : M.X i),
      k.f i (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    let t := affineBaseChangeTildeRepresentativeIso A D φ
      (DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) M (Iso.refl _) hc
    DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
        DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) =
      affineTildeTensorOrdinaryTargetMap R A B D M φ ψ k ≫
        (schemeDerivedDirectImage f').map t.hom ≫
        (schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H) := by
  dsimp only
  have h := affineTildeTensorOrdinaryExchange_preNormalization R A B D M φ ψ hw k hk
  dsimp only at h
  rw [← (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).map_comp,
    affineBaseChangeTildeRepresentativeIso_counit A D φ M hc]
  simpa only [affineTildeTensorOrdinaryTargetMap, Category.assoc] using h


end AlgebraicGeometry
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchange

/-! # Ordinary affine exchange in tensor coordinates

Compatibility interface for the complete adopted source implementation.
The coefficient target map and its ordinary exchange equation are re-exported
under their original fully qualified names. The legacy `affineTildeFunctor`
is an abbreviation of the associated-sheaf functor used by that implementation.

Source: Stacks Project, Tags 01I9, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange).
-/

@[expose] public section
```

## Users

`tools/downstream.py --direct --uses affineTildeTensorOrdinaryTargetMap` lists
one direct importer, `AffineTildeDerivedTensorMate`. The homology-coordinate consumer has also been restored by J3 as a
source interface; its adopted source proof unfolds the target map.
The original target-map definition is definitionally equal to the adopted
one, as checked for the entire function by `rfl`; its theorem accepts the
original statement. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | F4 | Re-exports the same target map and exchange theorem. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | unclaimed | Same map, representative and exact exchange equation; no edit. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | unclaimed | Already consolidated by J3; re-exports the source proof; no edit. |
| WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | source library | Unfolds the same adopted target map directly; unchanged. |

The representative, source-comparison, pre-normalization and chain modules
retain their current shared versions. Their other consumers are unaffected.
No target signature or definition meaning changes, so no target statement
review is reopened. The original DAG attachments are retained; the source
proof uses the same pre-normalization and representative-counit cancellation
steps as the node. No dependency is marked globally pruned.

The source import passes `tools/import_direction.py may`. Retained scratch
compatibility checks verify the original theorem signatures, the complete
coefficient-map function, both representative functions and three representative
lemmas; all seven declarations are checked with `#print axioms`.

## Status

landed 20261021T233653-L-847566 2026-10-21 (merge of deliver/F4/Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange)
