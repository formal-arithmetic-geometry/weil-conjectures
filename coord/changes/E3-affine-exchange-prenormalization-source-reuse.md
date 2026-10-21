# AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization

## Reason

Restore the item explicitly preserved in `coord/rework.tsv`, retaining its Lean
attachment and proof dependencies. The adopted source library already supplies
the complete exchange theorem and its ordinary chain calculation under exactly
the original fully qualified names. The restored Sheaf module publicly re-exports
that implementation, following the already restored source-comparison interface.

A direct import of the old Sheaf representative together with the adopted exchange
module fails with:

```text
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative failed,
environment already contains 'AlgebraicGeometry.affineBaseChangeTildeComplexIso._proof_18'
from Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
```

Therefore consolidate the unclaimed Sheaf representative module with its adopted
implementation as part of the same delivery. All five public names and both
concrete data constructions remain available. The source implementations differ
only by the definitionally equal `affinePushforwardTilde` spelling, imports and
docstrings. Scratch checks copy both old definition bodies and prove equality
to their adopted counterparts by `rfl`.

The separate quarantined chain item has a current J1 claim. It is not changed,
restored, withdrawn or reattached here. The restored exchange module gets the
same chain theorem and complex comparison through the adopted exchange module's
public source-chain import. Both the exchange node's chain dependency and the
chain node's original Sheaf Lean attachment are retained. This avoids duplicating
the source chain declarations in J1's module.

The original exchange theorem uses `ModuleCat.extendScalars_additive_sheaf` as a
Prop-valued additive-instance proof. That obsolete helper no longer exists in
the shared library; the adopted theorem uses
`ModuleCat.baseDerivedTensor_extendScalars_additive`. These proof-irrelevant
instances add no hypotheses and do not change either side of the equation.
A textual comparison of the entire public theorem signature AND its proof
matches the adopted implementation exactly after expanding the tilde abbreviation,
renaming that helper, and renaming the two unused let binders `δ` and `b` to
`_δ` and `_b`. All binders, hypotheses and the equality are retained. The duplicate
scratch elaboration of this long theorem exceeded 60 seconds; the delivered
interface compiles in seconds and uses the already checked complete proof.

No source-library file, quarantine archive, target or mathematical statement is
changed. The proof still localizes the ordinary chain equality and applies
right-derived-unit naturality. No unit route is bypassed.

## Old

The quarantined item publicly imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain
```

Its complete public theorem signature is:

```lean
theorem affineTildeTensorOrdinaryExchange_preNormalization
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
 :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback p
    let F' : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward f'
    let F := Scheme.Modules.pushforward f
    let G := Scheme.Modules.tensorPullback g
    let : E.Additive := preNormPullbackAdditive p
    let : G.Additive := preNormPullbackAdditive g
    let : F.Additive := preNormPushforwardAdditive f
    let : F'.Additive := preNormPushforwardAdditive f'
    let : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
      ModuleCat.extendScalars_additive_sheaf _
    let : (affineTildeFunctor A).Additive :=
      instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let : (affineTildeFunctor D).Additive :=
      instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let : (E ⋙ F').PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, E.map_zero]
        exact F'.map_zero _ _⟩
    let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
        ((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C :=
      (Functor.mapHomologicalComplexCompIso
        (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
          (CommRingCat.ofHom φ))) (.up ℤ)).app M
    let b₀ :
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g) ⟶
          (E ⋙ F') :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p hw
        naturality := fun _ _ z ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p hw z }
    let b := (b₀.mapHomologicalComplex (.up ℤ)).app P
    let a := affineTildePushforwardComplexMap D B ψ C
    DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
        DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) =
      (DerivedCategory.Q.map
          (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).map k) ≫
        DerivedCategory.Q.map a ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C))) ≫
        (schemeDerivedDirectImage f').map
          (DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv)
```

The live unclaimed representative module contains the following concrete definitions
and proved equations (the full old declaration block is preserved verbatim):

```lean
/-- The unit-normalized tensor/tilde comparison on complexes, shared by the
pullback representative and calculations with it. Source: Stacks, Tags 01I9 and 08DW.
(blueprint: def-pc-affine-base-change-tilde-representative-iso). -/
def affineBaseChangeTildeComplexIso
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))
    let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} _
    (E.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅
      ((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) := by
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
    Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} _
  let : (affineTildeFunctor A).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (affineTildeFunctor D).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let θ : affineTildeFunctor A ⋙ E ≅
      ModuleCat.extendScalars φ ⋙ affineTildeFunctor D :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  exact (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M

/-- Degreewise formula for the complex comparison.
Source: Stacks, Tag 01I9; this is the defining termwise action of the comparison. -/
theorem affineBaseChangeTildeComplexIso_hom_f
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affineBaseChangeTildeComplexIso A D φ M).hom.f i =
      (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
        (CommRingCat.ofHom φ))).hom.app (M.X i) := by
  rfl

/-- The actual tilde representative of affine derived pullback.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: def-pc-affine-base-change-tilde-representative-iso).
The tensor-pullback comparison is unit-normalized. The other two factors are
respectively the inverse of the supplied derived counit and the image of e. -/
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let δ := affineBaseChangeTildeComplexIso A A' φ M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
    (derivedPullback f).mapIso e


/-- Cancelling the supplied pullback counit leaves exactly the inverse complex
comparison. Source: Stacks, Tags 01I9 and 08HY. The representative has three factors:
the inverse comparison, the inverse counit, and the image of the identity. Functoriality
removes the last factor and the middle factor cancels against the counit. -/
theorem affineBaseChangeTildeRepresentativeIso_counit
    (A D : Type u) [CommRing A] [CommRing D] (φ : A →+* D)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    (affineBaseChangeTildeRepresentativeIso A D φ
      (DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) M
      (Iso.refl _) hc).hom ≫
      (SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) =
      DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv := by
  let p := Spec.map (CommRingCat.ofHom φ)
  let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
  let c := (SingleComplexBaseChange.counit p).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let : IsIso c := hc
  dsimp only [affineBaseChangeTildeRepresentativeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.refl_hom, Category.assoc]
  change DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv ≫
    inv c ≫ (derivedPullback p).map (𝟙 _) ≫ c = _
  erw [(derivedPullback p).map_id]
  change DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv ≫
    inv c ≫ 𝟙 _ ≫ c = _
  simp only [Category.id_comp, IsIso.inv_hom_id, Category.comp_id]

/-- The chosen pullback representative is compatible with transport from the identity
representative. Source: Stacks Project, Tag 08HY. This follows directly from its
three defining factors and functoriality of derived pullback. -/
theorem affineBaseChangeTildeRepresentativeIso_identity_hom
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    (affineBaseChangeTildeRepresentativeIso A A' φ
      (DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) M
      (Iso.refl _) hc).hom ≫ (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map e.hom =
      (affineBaseChangeTildeRepresentativeIso A A' φ K M e hc).hom := by
  dsimp only [affineBaseChangeTildeRepresentativeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  congr 1
  congr 1
  exact ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).map_comp
    (𝟙 _) e.hom).symm.trans
      (congrArg (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
        (Category.id_comp e.hom))
```

## New

The item is restored with the following interface:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization

/-! # Derived affine exchange before target reassociation

Compatibility interface for the complete adopted source implementation.
The derived affine exchange equation is re-exported under its original name.
The source proof localizes the ordinary chain equality and applies naturality
of the right-derived pushforward unit, without assuming the pullback counit
is invertible.

Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization).
-/

@[expose] public section
```

The representative retains its old public normalization import and adds the
canonical implementation:

```lean
public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
```

The latter re-exports `affineBaseChangeTildeComplexIso`,
`affineBaseChangeTildeComplexIso_hom_f`, `affineBaseChangeTildeRepresentativeIso`,
`affineBaseChangeTildeRepresentativeIso_counit` and
`affineBaseChangeTildeRepresentativeIso_identity_hom`, with the same types and
constructions. The complex comparison still uses the uniquely unit-normalized
tensor/tilde isomorphism. The representative still consists of its inverse,
the supplied inverse derived counit, and the derived image of the representative.
No new choice or existence statement is introduced.

Only explanatory `lean.note` fields of the exchange and representative nodes are
updated. All attachments, statements, proof steps and dependencies remain.

Validation with `lcompile.py --all` compiles the two final library interfaces
in 1.7 seconds each, a coexistence/axiom check in 2.0 seconds, and the archived
representative API checks in 27.6 seconds. The latter repeats both original
definition bodies under fresh scratch names and proves both equal to the adopted
definitions by `rfl`; it also applies the three public representative equations
at their archived signatures. The coexistence check imports the restored Sheaf
interface and the canonical ordinary-exchange parent together. All nine axiom
checks report exactly `propext`, `Classical.choice`, and `Quot.sound`, including
that parent's theorem. The scratch checks are excluded from the delivery.
The import-direction checks accept the two added source imports.

## Users

`tools/downstream.py --uses` reports zero live downstream modules for both changed
Sheaf modules. A full source import scan includes these quarantined direct consumers:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative | unclaimed | Consolidate the duplicate definitions with the identical source definitions; preserve the normalization import and all five names. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization | E3 assignment | Restore the same theorem and the source chain dependency through the adopted implementation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain | J1 | Its representative import receives definitionally identical data and the same equations. Its file and node are untouched. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | unclaimed | Its representative and pre-normalization imports supply the same declarations and cancellation law. No signature or proof adaptation is required by this change. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | unclaimed | Uses the identical three-factor representative. No adaptation is required. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization | unclaimed | Uses the identical representative and identity transport equation. No adaptation is required. |

The canonical source consumers are unchanged. Quarantined parent dependency nodes
continue to cite the original exchange and representative nodes. Restoring these
interfaces does not withdraw a node or remove any parent's proof obligations.

## Status

landed 20261021T203432-L-3746592 2026-10-21 (merge of deliver/E3/Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization)
