# AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization_chain

## Reason

Repair the landing conflict returned by C-44af9 for head 44af9ae85f5.
The earlier packet changed AffineBaseChangeTildeRepresentative from the
pre-af62f65adee implementation. Current sheaf-dag already consolidates that
module with the adopted source. The sandbox now takes the current file
verbatim, including its header, imports and docstring. It requires no further
change and contributes no diff to this delivery.

The substantive repair remains in the item module: replace its restored
duplicate chain implementation with a public compatibility interface to the
complete adopted implementation. Both original public Sheaf imports remain.
This prevents duplicate declarations when the current pre-normalization
interface also exposes the adopted chain module.

The current Sheaf and adopted chain declaration blocks agree textually after
removing comments and whitespace and expanding affineTildeFunctor to
its existing definition, affinePushforwardTilde. The current main version
already has the explicit sheaf universe for chainCoordinatesAbelian.
The adopted theorem proves the same degreewise mate calculation, followed
by cancellation of the tensor/tilde comparisons and chain-map extensionality.
The construction of affineTildePushforwardComplexMap and all six named local
instance constructions are preserved, together with their original fully
qualified names and visibility.

No object is replaced by an arbitrary witness. The same unit-normalized
tensor/tilde comparison, its inverse, and the concrete pushforward comparison
are used. The repair changes no mathematical statement, hypothesis, target,
node attachment, proof dependency or unit route. The adopted source files and
quarantine archives are unchanged. This is a zero-hole compatibility repair,
not a new proof closure or a module withdrawal.

## Old

The current sheaf-dag item, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! The termwise affine exchange chain map before localization.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

local instance (priority := 2000) chainCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) chainCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) chainCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


private theorem tilde_map_toOpen {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (a : M ⟶ N) (m : M) :
    (Hom.app ((tilde.functor R).map a) ⊤) (tilde.toOpen M ⊤ m) =
      tilde.toOpen N ⊤ (a m) := by
  exact congr($(tilde.toOpen_map_app a ⊤) m)

private theorem tilde_hom_ext {R : CommRingCat.{u}}
    {M : ModuleCat.{u} R} {F : (Spec R).Modules}
    {a b : (tilde.functor R).obj M ⟶ F}
    (h : ∀ m : M, (Hom.app a ⊤) (tilde.toOpen M ⊤ m) =
      (Hom.app b ⊤) (tilde.toOpen M ⊤ m)) : a = b := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

private theorem sigma_toOpen (A B : Type u) [CommRing A] [CommRing B]
    (ψ : B →+* A) (N : ModuleCat.{u} A) (n : N) :
    (Scheme.Modules.Hom.app ((affineTildePushforwardComparison A B ψ).hom.app N) ⊤)
      (tilde.toOpen (R := .of B) ((ModuleCat.restrictScalars ψ).obj N) ⊤ n) =
        tilde.toOpen (R := .of A) N ⊤ n := by
  let S := moduleSpecΓFunctor (R := .of A)
  let T := affineTildeFunctor B
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
  let ν : ModuleCat.restrictScalars ψ ⟶
      affineTildeFunctor A ⋙ P ⋙ moduleSpecΓFunctor (R := .of B) :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (tilde.toTildeΓNatIso (R := .of A)).hom
        (ModuleCat.restrictScalars ψ) ≫
      (Functor.associator (affineTildeFunctor A) S (ModuleCat.restrictScalars ψ)).hom ≫
      Functor.whiskerLeft (affineTildeFunctor A)
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom ψ)).inv
  have h : (tilde.adjunction (R := .of B)).homEquiv _ _
      ((affineTildePushforwardComparison A B ψ).hom.app N) = ν.app N := by
    exact ((tilde.adjunction (R := .of B)).homEquiv _ _).apply_symm_apply (ν.app N)
  exact congr($h n)

private theorem baseChange_transpose
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (F : X.Modules) :
    (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
        (moduleBaseChangeMap f f' g p h F) =
      (pushforward f).map
          ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F) ≫
        (pushforwardComp p f).hom.app ((tensorPullback p).obj F) ≫
        (pushforwardCongr h).hom.app ((tensorPullback p).obj F) ≫
        (pushforwardComp f' g).inv.app ((tensorPullback p).obj F) := by
  exact ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _).apply_symm_apply _

private theorem presheaf_map_id_apply {X : Scheme.{u}} (F : X.Modules)
    (q : Γ(F, ⊤)) : F.presheaf.map (𝟙 (op ⊤)) q = q := by
  exact congr($(F.presheaf.map_id (op ⊤)) q)

attribute [local irreducible] Scheme.Modules.tensorPullback affineTildePushforwardComparison

set_option maxHeartbeats 800000 in
-- The sectionwise mate calculation traverses both affine comparison interfaces.
private theorem affine_exchange_degree
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] (N : ModuleCat.{u} A)
    (φ : A →+* D) (ψ : B →+* D)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : (ModuleCat.extendScalars (algebraMap R B)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ⟶
      (ModuleCat.restrictScalars ψ).obj ((ModuleCat.extendScalars φ).obj N))
    (hk : ∀ (b : B) (q : N), k (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let θg := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
    let θp := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom φ))
    (tensorPullback g).map ((affineTildePushforwardComparison A R
        (algebraMap R A)).hom.app N) ≫
      moduleBaseChangeMap f f' g p hw ((affineTildeFunctor A).obj N) ≫
      (pushforward f').map (θp.hom.app N) =
      θg.hom.app ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ≫
        (affineTildeFunctor B).map k ≫
        (affineTildePushforwardComparison D B ψ).hom.app
          ((ModuleCat.extendScalars φ).obj N) := by
  dsimp only
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  apply (ag.homEquiv _ _).injective
  rewrite [ag.homEquiv_naturality_left, ag.homEquiv_naturality_right]
  rewrite (config := { transparency := .default }) [baseChange_transpose]
  apply tilde_hom_ext (R := .of R)
  intro q
  simp only [Adjunction.homEquiv_unit, Hom.comp_app,
    pushforward_map_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply]
  change
    (Hom.app ((Classical.choose (exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom φ))).hom.app N) ⊤)
      ((((tensorPullback (Spec.map (CommRingCat.ofHom φ))).obj
        ((affineTildeFunctor A).obj N)).presheaf.map (𝟙 _))
      ((Hom.app ((Classical.choose (exists_tensorPullbackAdjunction
        (Spec.map (CommRingCat.ofHom φ)))).unit.app ((affineTildeFunctor A).obj N)) ⊤)
        ((Hom.app ((affineTildePushforwardComparison A R (algebraMap R A)).hom.app N) ⊤)
          (tilde.toOpen (R := .of R) ((ModuleCat.restrictScalars (algebraMap R A)).obj N)
            ⊤ q)))) =
    (Hom.app ((affineTildePushforwardComparison D B ψ).hom.app
      ((ModuleCat.extendScalars φ).obj N)) ⊤)
      ((Hom.app ((affineTildeFunctor B).map k) ⊤)
        ((Hom.app ((Classical.choose (exists_tensorPullback_tilde_iso
          (CommRingCat.ofHom (algebraMap R B)))).hom.app
            ((ModuleCat.restrictScalars (algebraMap R A)).obj N)) ⊤)
          ((Hom.app (ag.unit.app ((affineTildeFunctor R).obj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj N))) ⊤)
              (tilde.toOpen (R := .of R)
                ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ⊤ q))))
  rewrite (config := { transparency := .default })
    [presheaf_map_id_apply ((tensorPullback (Spec.map (CommRingCat.ofHom φ))).obj
    ((affineTildeFunctor A).obj N))]
  rewrite (config := { transparency := .default }) [sigma_toOpen A R (algebraMap R A) N q]
  rewrite (config := { transparency := .default })
    [(Classical.choose_spec (exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))) N q]
  rewrite (config := { transparency := .default })
    [(Classical.choose_spec (exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom (algebraMap R B))))
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) q]
  rewrite (config := { transparency := .default }) [tilde_map_toOpen (R := .of B) k]
  simp only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rewrite (config := { transparency := .default }) [hk, map_one,
    sigma_toOpen D B ψ ((ModuleCat.extendScalars φ).obj N) _]
  rfl


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance chainPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
local instance chainPushforwardAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive := ⟨fun {_ _} {_ _} ↦ rfl⟩
local instance chainTildeAdditive (A : Type u) [CommRing A] :
    (affineTildeFunctor A).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor

/-- The termwise pushforward comparison used in the target-map expansion.
Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization). -/
def affineTildePushforwardComplexMap
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    (C : CochainComplex (ModuleCat.{u} D) ℤ) :
    let P := RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
    ((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C) := by
  let σ := affineTildePushforwardComparison D B ψ
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
  let : P.Additive := RingedSpace.moduleDirectImage_additive_proof _
  exact { f := fun i ↦ σ.hom.app (C.X i)
          comm' := fun i j _ ↦ (σ.hom.naturality (C.d i j)).symm }

set_option maxHeartbeats 800000 in
-- The degreewise comparison includes the chosen tensor and pushforward functors.
/-- The ordinary termwise exchange chain map in affine tensor coordinates.
Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain).
The assertion is the pre-localization calculation: the source comparison followed by
ordinary module base change equals the coefficient map, affine pushforward comparison,
and the inverse tensor/tilde comparison. It is proved degreewise on pure tensors and
then by tensor induction and extensionality. -/
theorem affineTildeTensorOrdinaryExchange_preNormalization_chain
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
      k.f i (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback p
    let F' : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward f'
    let : E.Additive := chainPullbackAdditive p
    let : F'.Additive := chainPushforwardAdditive f'
    let : (affineTildeFunctor A).Additive := chainTildeAdditive A
    let : (affineTildeFunctor D).Additive := chainTildeAdditive D
    let : (E ⋙ F').PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, E.map_zero]
        exact F'.map_zero _ _⟩
    let δ := affineBaseChangeTildeComplexIso A D φ M
    let b₀ :
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g) ⟶
          (E ⋙ F') :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p hw
        naturality := fun _ _ z ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p hw z }
    let b := (b₀.mapHomologicalComplex (.up ℤ)).app P
    let a := affineTildePushforwardComplexMap D B ψ C
    (affineTildeTensorOrdinarySourceIso R A B M).hom ≫ b =
      (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).map k) ≫ a ≫
        ((F'.mapHomologicalComplex (.up ℤ)).map δ.inv) := by
  intro f g p f' C P E F' hE hF' hTA hTD hEF δ b₀ b a
  apply HomologicalComplex.hom_ext
  intro i
  let θg := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom (algebraMap R B)))
  let θp := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  change θg.inv.app ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X i)) ≫
      (Scheme.Modules.tensorPullback g).map
        ((affineTildePushforwardComparison A R (algebraMap R A)).hom.app (M.X i)) ≫
      Scheme.Modules.moduleBaseChangeMap f f' g p hw ((affineTildeFunctor A).obj (M.X i)) =
    (affineTildeFunctor B).map (k.f i) ≫
      (affineTildePushforwardComparison D B ψ).hom.app
        ((ModuleCat.extendScalars φ).obj (M.X i)) ≫
      F'.map (θp.inv.app (M.X i))
  have hd := affine_exchange_degree R A B D (M.X i) φ ψ hw (k.f i) (hk i)
  apply (cancel_epi (θg.hom.app
    ((ModuleCat.restrictScalars (algebraMap R A)).obj (M.X i)))).1
  apply (cancel_mono (F'.map (θp.hom.app (M.X i)))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc, ← F'.map_comp, Iso.inv_hom_id_app]
  exact hd

end AlgebraicGeometry
```

AffineBaseChangeTildeRepresentative is the current sheaf-dag file verbatim
in the sandbox. The obsolete pre-af62f65adee version from the earlier packet
is no longer proposed as its base or replacement.

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import
  WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain

/-! The termwise affine exchange chain map before localization.

Compatibility interface for the complete adopted chain calculation. The termwise
pushforward map and exchange theorem retain their original fully qualified names.
The associated-sheaf abbreviation reduces to the adopted functor.

Source: Stacks Project, Tags 01I9, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization-chain). -/

@[expose] public section
```

The public source import supplies the same two primary declarations:
AlgebraicGeometry.affineTildePushforwardComplexMap and
AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization_chain.
It also supplies chainCoordinatesCategory, chainCoordinatesPreadditive,
chainCoordinatesAbelian, chainPullbackAdditive, chainPushforwardAdditive and
chainTildeAdditive with their original constructions. The representative
interface is unchanged from current main and still supplies its five public
representative declarations.

## Users

A fresh tools/downstream.py scan on current sheaf-dag finds zero live Lean
importers of the item, and four downstream modules of the representative
interface: AffineTildeDerivedTensorMate, AffineTildeTensorOrdinaryExchange,
AffineTildeTensorOrdinaryExchangePreNormalization and the item itself.
The DAG parent still cites this chain node, and the adopted parent still
imports and uses the adopted chain theorem. Zero live importers therefore
does not justify a withdrawal: the original path and attachment are retained.
The earlier consumer records are reconciled below, including the homology
coordinates consumer required by C-ad096. Holders are from current claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain | J1 | Same chain map, theorem and six local instance constructions through the public source import. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative | unclaimed | Current main copied verbatim; no delivered change. All five public names remain. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization | unclaimed | Already re-exports its adopted implementation, which imports the adopted chain. The chain theorem and instances remain available; no adaptation. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | H1 | Representative interface is unchanged from current main; no adaptation. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | F4 | Same representative equations and pushforward chain map; no adaptation. |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | unclaimed | Already re-exports its adopted implementation. The former J3 consumer and its category, preadditive and abelian constructions are preserved; no adaptation. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization | unclaimed | Now imports the adopted representative directly. Its representative and identity equation are unchanged; no adaptation. |

No held module is changed. No target meaning changes, so no new target
statement review is required. No node is pruned: the original mathematical
proof and all its dependencies remain in the adopted implementation.

Validation is recorded in report.md. The import-direction check accepts the
public source import. Both retained interfaces compile on the server via
lcompile.py --all, with the representative byte-identical to current main.
Scratch compatibility checks use the newly compiled item interface and are
excluded from delivery by their __probe.lean suffix. The complete legacy
chain signature and the chain-map construction equality compile; the current
parent and repaired chain can be imported together. All seven primary names,
all six named instance constructions, the legacy signature, the construction
equality and the parent theorem have only propext, Classical.choice and
Quot.sound in their printed axiom lists.

## Status

landed 20261021T225147-L-3783227 2026-10-21 (merge of deliver/J1/Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain)
