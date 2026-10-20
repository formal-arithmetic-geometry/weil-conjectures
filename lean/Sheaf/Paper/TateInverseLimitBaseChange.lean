/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.NumberTheory.Padics.RingHoms
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.Paper.StrictTowerOperations
import Mathlib.Algebra.Module.Hom

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).

The index `op r` denotes the positive level `r + 1`. Scalar extension is the
recorded sheaf tensor construction, with its pure tensors written in the order `a ⊗ x`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMapMixedUniverses.{u, u + 1, u + 1,
    u + 1} c M i) s m

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
      CommRingCat.{u + 1}
      RingCat.{u + 1})).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (X := M.val.obj Y) (Y := H.val.obj Y) (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (X := M.val.obj X) (Y := H.val.obj X) (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
        CommRingCat.{u + 1}
        RingCat.{u + 1})).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H) :=
  (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
    (P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M)
    (F := H)).trans (tensorPresheafHomEquiv T c M H)

private theorem tensorHomEquiv_apply (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (m : M.val.obj U) :
    (tensorHomEquiv T φ M H f).val.app U m =
      f.val.app U ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
          φ M).presheaf).app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) := by
  rfl

private theorem tensorHomEquiv_tmul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      s • (@id (H.val.obj U) ((tensorHomEquiv T φ M H f).val.app U m)) := by
  let k := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      S).obj) f
  change k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
    s • k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  let k' : (ModuleCat.extendScalars (φ.hom.app U).hom).obj (M.val.obj U) ⟶
      H.val.obj U := k.app U
  have hh := k'.hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at hh
  exact hh

-- Keep the tensor universal-property inverse folded after establishing its API.
-- Otherwise later equivalence comparisons unfold its sectionwise tensor construction.
attribute [local irreducible] restrictionToTensor

/-- The actual constant-coefficient module category.
Source: Stacks Tag 03DB (blueprint: lem-pur-tate-inverse-limit-base-change). -/
abbrev tateModules (T : Scheme.{u}) (R : Type u) [CommRing R] :=
  proEtaleRingModules T (proEtaleConstantRing T R)

/-- The constant sheaf map induced by a coefficient homomorphism.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateConstantMap (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : proEtaleConstantRing T R ⟶ proEtaleConstantRing T A :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom)))

/-- Restriction along the indicated constant coefficient map, with unchanged sections.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRestrict (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : tateModules T A ⥤ tateModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (tateConstantMap T f))

/-- The sheaf tensor `M ⊗_R A_T`, with its natural A-module structure.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensor (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) : tateModules T A :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateConstantMap T f) M

/-- A pure tensor in the sheaf tensor, using the module sheafification unit.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTmul {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) (U : T.ProEt)
    (a : (proEtaleConstantRing T A).obj.obj (op U)) (x : M.val.obj (op U)) :
    (tateTensor T f M).val.obj (op U) :=
  purScalarSection (proEtaleConstantRing T R) (proEtaleConstantRing T A)
    (tateConstantMap T f) M U a x

/-- Inverse image, transported through the stipulated canonical constant-ring isomorphism.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullback {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] : tateModules T R ⥤ tateModules T' R :=
  proEtaleRingModulePullback h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))

/-- The canonical inverse-image unit on local module sections.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateUnit {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] (M : tateModules T R)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    ((tatePullback h R).obj M).val.obj (op ((proEtaleBaseChange h).obj U)) :=
  ((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x

/-- A tower is killed at positive level `r + 1`, sectionwise.
Source: Stacks Tag 03CO (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def TateTowerKilled (l : ℕ) {T : Scheme.{u}} {R : Type u} [CommRing R]
    (F : ℕᵒᵖ ⥤ tateModules T R) : Prop :=
  ∀ (r : ℕ) (U : T.ProEt) (x : (F.obj (op r)).val.obj (op U)),
    (l ^ (r + 1)) • x = 0

/-- The limit comparison is the universal limit comparison followed by the level maps.
It does not assert that inverse image preserves an infinite limit.
Source: Stacks Tags 03DB and 03CO
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateLimitMap {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    (F : ℕᵒᵖ ⥤ tateModules T R) (F' : ℕᵒᵖ ⥤ tateModules T' R)
    (β : F ⋙ tatePullback h R ≅ F') :
    (tatePullback h R).obj (limit F) ⟶ limit F' :=
  limit.post F (tatePullback h R) ≫ limMap β.hom

/-- Compatible level isomorphisms induce exactly one linear limit comparison.
Source: Stacks Tags 03DB and 03CO
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply inverse image to the source limit cone and postcompose with β.
Naturality of β gives the cone equations. The target limit gives the map, and its
jointly monic coordinate projections give uniqueness. This is proof steps 1--3. -/
theorem tateInverseLimitBaseChange (l : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F') :
    (∀ r : ℕ,
      tateLimitMap h _ F F' β ≫ limit.π F' (op r) =
        (tatePullback h _).map (limit.π F (op r)) ≫ β.hom.app (op r)) ∧
    ∀ c : (tatePullback h _).obj (limit F) ⟶ limit F',
      (∀ r : ℕ, c ≫ limit.π F' (op r) =
        (tatePullback h _).map (limit.π F (op r)) ≫ β.hom.app (op r)) →
      c = tateLimitMap h _ F F' β := by
  have _ := hF
  have _ := hF'
  constructor
  · intro r
    dsimp only [tateLimitMap]
    rw [Category.assoc, limMap_π, limit.post_π_assoc]
  · intro c hc
    apply limit.hom_ext
    intro j
    rcases j with ⟨r⟩
    rw [hc r]
    dsimp only [tateLimitMap]
    rw [Category.assoc, limMap_π, limit.post_π_assoc]

/-- The constant-ring unit on sections, before extending the module scalars.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRingUnit {T T' : Scheme.{u}} (h : T' ⟶ T) (A : Type u) [CommRing A]
    (U : T.ProEt) (a : (proEtaleConstantRing T A).obj.obj (op U)) :
    (proEtaleConstantRing T' A).obj.obj (op ((proEtaleBaseChange h).obj U)) :=
  (proEtaleCoefficientDirectImageMap h A).hom.app (op U) a

/-- The pure-tensor normalization of `c ⊗ 1` under canonical inverse-image transport.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M')
    (b : (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M') : Prop :=
  ∀ (U : T.ProEt) (a : (proEtaleConstantRing T A).obj.obj (op U))
    (x : M.val.obj (op U)),
    b.val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h A (tateTensor T φ M) U (tateTmul φ M U a x)) =
      tateTmul φ M' ((proEtaleBaseChange h).obj U) (tateRingUnit h A U a)
        (c.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x))

private def tensorUnit {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (a : R →+* A) (M : tateModules T R) :
    M ⟶ (tateRestrict T a).obj (tateTensor T a M) :=
  tensorHomEquiv T (tateConstantMap T a) M (tateTensor T a M) (𝟙 _)

private theorem tensorUnit_apply {T : Scheme.{u}} {R A : Type u}
    [CommRing R] [CommRing A] (a : R →+* A) (M : tateModules T R)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    (tensorUnit a M).val.app (op U) x = tateTmul a M U 1 x := by
  rfl

attribute [local irreducible] tensorUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantDirectMap_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) :
    tateConstantMap T φ ≫ proEtaleCoefficientDirectImageMap h A =
      proEtaleCoefficientDirectImageMap h R ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map (tateConstantMap T' φ) := by
  apply ((sheafificationAdjunction (ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change toSheafify _ _ ≫ (tateConstantMap T φ).hom ≫
    (proEtaleCoefficientDirectImageMap h A).hom =
      toSheafify _ _ ≫ (proEtaleCoefficientDirectImageMap h R).hom ≫ _
  change toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R))) ≫
      sheafifyMap (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map
      (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        (φ.comp ULift.ringEquiv.{u, u + 1}.toRingHom)))) ≫ _ = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  have hr (B : Type u) [CommRing B] :
      toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} B))) ≫
          (proEtaleCoefficientDirectImageMap h B).hom =
        Functor.whiskerLeft (proEtaleBaseChange h).op
          (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} B)))) :=
    ((sheafificationAdjunction (ProEt.topology T)
      CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [hr A, ← Category.assoc, hr R]
  let f : (Functor.const T'.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} R)) ⟶
      (Functor.const T'.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)) :=
    (Functor.const T'.ProEtᵒᵖ).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).symm.toRingHom.comp
        (φ.comp (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom)))
  have hn := toSheafify_naturality (ProEt.topology T') f
  exact congrArg (fun t ↦ Functor.whiskerLeft (proEtaleBaseChange h).op t) hn

private def constantUnit (T : Scheme.{u}) (R : Type u) [CommRing R] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} R)) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T R)).obj :=
  adicLisseConstantUnit T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallyInjective T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallySurjective T (ULift.{u + 1, u} R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantUnit_map (T : Scheme.{u}) {R Q : Type u}
    [CommRing R] [CommRing Q] (q : R →+* Q) :
    constantUnit T R ≫ ((adicLisseForget T).map (tateConstantMap T q)).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
          (q.comp ULift.ringEquiv.{u, u + 1}.toRingHom))) ≫ constantUnit T Q :=
by
  let f : (Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} R)) ⟶
      (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Q)) :=
    (Functor.const T.ProEtᵒᵖ).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} Q ≃+* Q).symm.toRingHom.comp
        (q.comp (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom)))
  exact (congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T) f)).symm

private theorem constantMap_locallySurjective (T : Scheme.{u}) {R Q : Type u}
    [CommRing R] [CommRing Q] (q : R →+* Q) (hq : Function.Surjective q) :
    Presheaf.IsLocallySurjective (ProEt.topology T)
      ((adicLisseForget T).map (tateConstantMap T q)).hom := by
  let f := (Functor.const T.ProEtᵒᵖ).map
    (RingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
      (q.comp ULift.ringEquiv.{u, u + 1}.toRingHom)))
  have : Presheaf.IsLocallySurjective (ProEt.topology T) f :=
    Presheaf.isLocallySurjective_of_surjective (ProEt.topology T) f (fun U x ↦ by
      obtain ⟨r, hr⟩ := hq x.down
      exact ⟨ULift.up r, congrArg ULift.up hr⟩)
  have : Presheaf.IsLocallySurjective (ProEt.topology T)
      (f ≫ constantUnit T Q) := inferInstance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (ProEt.topology T) (constantUnit_map T q)

private def restrictHomEquiv (T : Scheme.{u}) {R Q : Type u}
    [CommRing R] [CommRing Q] (q : R →+* Q) (hq : Function.Surjective q)
    (M N : tateModules T Q) :
    (M ⟶ N) ≃ ((tateRestrict T q).obj M ⟶ (tateRestrict T q).obj N) := by
  have := constantMap_locallySurjective T q hq
  exact
    { toFun := (tateRestrict T q).map
      invFun := fun f ↦ ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
        ((adicLisseForget T).map (tateConstantMap T q)).hom N.isSheaf).symm f.val⟩
      left_inv := fun f ↦ by
        apply SheafOfModules.hom_ext
        exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          ((adicLisseForget T).map (tateConstantMap T q)).hom N.isSheaf).symm_apply_apply _
      right_inv := fun f ↦ by
        apply SheafOfModules.hom_ext
        exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          ((adicLisseForget T).map (tateConstantMap T q)).hom N.isSheaf).apply_symm_apply _ }

private theorem restrictHomEquiv_apply (T : Scheme.{u}) {R Q : Type u}
    [CommRing R] [CommRing Q] (q : R →+* Q) (hq : Function.Surjective q)
    (M N : tateModules T Q) (f : M ⟶ N) :
    restrictHomEquiv T q hq M N f = (tateRestrict T q).map f := rfl

attribute [local irreducible] restrictHomEquiv

private abbrev tatePush {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] :=
  proEtaleRingModuleDirectImage h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))

private abbrev tateAdj {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] :=
  proEtaleRingModuleAdjunction h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))

private theorem tateAdj_apply {T T' : Scheme.{u}} (h : T' ⟶ T)
    (R : Type u) [CommRing R] [IsIso (proEtaleCoefficientInverseImageMap h R)]
    (M : tateModules T R) (H : tateModules T' R)
    (f : (tatePullback h R).obj M ⟶ H) (U : T.ProEt) (x : M.val.obj (op U)) :
    (((tateAdj h R).homEquiv M H) f).val.app (op U) x =
      f.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

private theorem tateDirectMap_eq {T T' : Scheme.{u}} (h : T' ⟶ T)
    (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] :
    proEtaleRingDirectImageMap h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R)) =
      proEtaleCoefficientDirectImageMap h R :=
  ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def directScalarIso {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)] (H : tateModules T' A) :
    (tateRestrict T φ).obj ((tatePush h A).obj H) ≅
      (tatePush h R).obj ((tateRestrict T' φ).obj H) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
      (X₁ := (((tateRestrict T φ).obj ((tatePush h A).obj H)).val.obj U))
      (X₂ := (((tatePush h R).obj ((tateRestrict T' φ).obj H)).val.obj U))
      { __ := AddEquiv.refl _
        map_smul' := fun r m ↦ by
          change @SMul.smul ((proEtaleConstantRing T' A).obj.obj
            ((proEtaleBaseChange h).op.obj U)) _ _
              ((proEtaleRingDirectImageMap h (proEtaleConstantRing T A)
                (proEtaleConstantRing T' A)
                (asIso (proEtaleCoefficientInverseImageMap h A))).hom.app U
                  ((tateConstantMap T φ).hom.app U r))
                (show H.val.obj ((proEtaleBaseChange h).op.obj U) from m) =
            @SMul.smul ((proEtaleConstantRing T' A).obj.obj
              ((proEtaleBaseChange h).op.obj U)) _ _
                ((tateConstantMap T' φ).hom.app ((proEtaleBaseChange h).op.obj U)
                  ((proEtaleRingDirectImageMap h (proEtaleConstantRing T R)
                    (proEtaleConstantRing T' R)
                    (asIso (proEtaleCoefficientInverseImageMap h R))).hom.app U r))
                  (show H.val.obj ((proEtaleBaseChange h).op.obj U) from m)
          rw [tateDirectMap_eq, tateDirectMap_eq]
          exact congrArg (fun z ↦ z • (show H.val.obj
            ((proEtaleBaseChange h).op.obj U) from m))
            (DFunLike.congr_fun
              (congrArg (fun f ↦ (f.hom.app U).hom)
                (constantDirectMap_naturality h φ)) r) })
      (by intro U V f; ext m; rfl))

private theorem directScalarIso_hom_apply {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)] (H : tateModules T' A)
    (U : T.ProEtᵒᵖ) (x : H.val.obj ((proEtaleBaseChange h).op.obj U)) :
    (directScalarIso h φ H).hom.val.app U x = x := by
  rfl

private def tensorPullbackHomEquiv {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (H : tateModules T' A) :
    ((tatePullback h A).obj (tateTensor T φ M) ⟶ H) ≃
      ((tatePullback h R).obj M ⟶ (tateRestrict T' φ).obj H) :=
  ((tateAdj h A).homEquiv (tateTensor T φ M) H).trans
    ((tensorHomEquiv T (tateConstantMap T φ) M ((tatePush h A).obj H)).trans
      (((Iso.homCongr (Iso.refl M) (directScalarIso h φ H))).trans
        ((tateAdj h R).homEquiv M ((tateRestrict T' φ).obj H)).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullbackHomEquiv_apply {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (H : tateModules T' A)
    (b : (tatePullback h A).obj (tateTensor T φ M) ⟶ H)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    (tensorPullbackHomEquiv h φ M H b).val.app
        (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x) =
      b.val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h A (tateTensor T φ M) U (tateTmul φ M U 1 x)) := by
  have he := ((tateAdj h R).homEquiv _ _).apply_symm_apply
    ((tensorHomEquiv T (tateConstantMap T φ) M ((tatePush h A).obj H)
      (((tateAdj h A).homEquiv _ _) b)) ≫ (directScalarIso h φ H).hom)
  rw [Adjunction.homEquiv_unit] at he
  have hx := congrArg (fun f ↦ f.val.app (op U) x) he
  change (tensorPullbackHomEquiv h φ M H b).val.app
    (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x) = _ at hx
  exact hx

attribute [local irreducible] directScalarIso tensorPullbackHomEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tateTmul_eq_smul {T : Scheme.{u}} {R A : Type u}
    [CommRing R] [CommRing A] (φ : R →+* A) (M : tateModules T R)
    (U : T.ProEt) (a : (proEtaleConstantRing T A).obj.obj (op U))
    (x : M.val.obj (op U)) :
    tateTmul φ M U a x = a • tateTmul φ M U 1 x := by
  have hh := tensorHomEquiv_tmul T (tateConstantMap T φ) M
    (tateTensor T φ M) (𝟙 _) (op U) a x
  change tateTmul φ M U a x = a • tateTmul φ M U 1 x at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tateTmul_map {T : Scheme.{u}} {R A : Type u}
    [CommRing R] [CommRing A] (φ : R →+* A) (M : tateModules T R)
    {U V : T.ProEt} (f : V ⟶ U)
    (a : (proEtaleConstantRing T A).obj.obj (op U)) (x : M.val.obj (op U)) :
    (tateTensor T φ M).val.map f.op (tateTmul φ M U a x) =
      tateTmul φ M V ((proEtaleConstantRing T A).obj.map f.op a) (M.val.map f.op x) := by
  change (tateTensor T φ M).val.presheaf.map f.op
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheafOfUniverses (tateConstantMap T φ) M).presheaf).app
        (op U) (a ⊗ₜ[_, ((tateConstantMap T φ).hom.app (op U)).hom] x)) = _
  erw [← NatTrans.naturality_apply]
  erw [tensorRestriction_tmul]
  rfl

private theorem tateUnit_smul {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T A) (U : T.ProEt)
    (a : (proEtaleConstantRing T A).obj.obj (op U)) (x : M.val.obj (op U)) :
    tateUnit h A M U (a • x) = tateRingUnit h A U a • tateUnit h A M U x := by
  have hh := (((tateAdj h A).unit.app M).val.app (op U)).hom.map_smul a x
  change tateUnit h A M U (a • x) =
    (proEtaleRingDirectImageMap h (proEtaleConstantRing T A)
      (proEtaleConstantRing T' A)
      (asIso (proEtaleCoefficientInverseImageMap h A))).hom.app (op U) a • tateUnit h A M U x at hh
  rw [tateDirectMap_eq] at hh
  exact hh

private theorem pullback_unit_ext {T T' : Scheme.{u}} (h : T' ⟶ T)
    (R : Type u) [CommRing R] [IsIso (proEtaleCoefficientInverseImageMap h R)]
    (M : tateModules T R) (H : tateModules T' R)
    (f g : (tatePullback h R).obj M ⟶ H)
    (he : ∀ (U : T.ProEt) (x : M.val.obj (op U)),
      f.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x) =
        g.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x)) : f = g := by
  apply ((tateAdj h R).homEquiv M H).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact he U.unop x

private theorem tensorPullback_unit_ext {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (H : tateModules T' A)
    (f g : (tatePullback h A).obj (tateTensor T φ M) ⟶ H)
    (he : ∀ (U : T.ProEt) (x : M.val.obj (op U)),
      f.val.app (op ((proEtaleBaseChange h).obj U))
          (tateUnit h A (tateTensor T φ M) U (tateTmul φ M U 1 x)) =
        g.val.app (op ((proEtaleBaseChange h).obj U))
          (tateUnit h A (tateTensor T φ M) U (tateTmul φ M U 1 x))) : f = g := by
  apply (tensorPullbackHomEquiv h φ M H).injective
  refine pullback_unit_ext h R M ((tateRestrict T' φ).obj H) _ _ ?_
  intro U x
  exact (tensorPullbackHomEquiv_apply h φ M H f U x).trans
    ((he U x).trans (tensorPullbackHomEquiv_apply h φ M H g U x).symm)

private theorem tensorPullback_unit_ext_raw {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (H : tateModules T' A)
    (f g : (tatePullback h A).obj (tateTensor T φ M) ⟶ H)
    (he : ∀ (U : T.ProEt) (x : M.val.obj (op U)),
      f.val.app (op ((proEtaleBaseChange h).obj U))
          (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T A)
          (proEtaleConstantRing T' A)
          (asIso (proEtaleCoefficientInverseImageMap h A))).unit.app
            (tateTensor T φ M)).val.app (op U) (tateTmul φ M U 1 x)) =
        g.val.app (op ((proEtaleBaseChange h).obj U))
          (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T A)
          (proEtaleConstantRing T' A)
          (asIso (proEtaleCoefficientInverseImageMap h A))).unit.app
            (tateTensor T φ M)).val.app (op U) (tateTmul φ M U 1 x))) : f = g := by
  exact tensorPullback_unit_ext h φ M H f g he

/-- Canonical tensor transport followed by `c ⊗ 1`, characterized rather than assumed.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: inverse image preserves the bilinear universal property of the tensor.
Constant coefficient comparisons commute with coefficient homomorphisms, since both
maps extend the same constant sections. Sheafify the induced balanced map. Pure tensors
and inverse-image units locally generate, so the displayed formula gives uniqueness.
This is the construction in proof steps 5--6. -/
theorem tateTensorMap_existsUnique {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    ∃! b : (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M',
      IsTateTensorMap h φ M M' c b := by
  let e := tensorPullbackHomEquiv h φ M (tateTensor T' φ M')
  let g : (tatePullback h R).obj M ⟶ (tateRestrict T' φ).obj
      (tateTensor T' φ M') := c ≫ tensorUnit φ M'
  refine ⟨e.symm g, ?_, ?_⟩
  · intro U a x
    rw [tateTmul_eq_smul, tateUnit_smul]
    rw [((e.symm g).val.app _).hom.map_smul]
    have he := tensorPullbackHomEquiv_apply h φ M (tateTensor T' φ M') (e.symm g) U x
    change (e (e.symm g)).val.app _ (tateUnit h R M U x) = _ at he
    rw [e.apply_symm_apply] at he
    rw [← he]
    change tateRingUnit h A U a •
      (show (tateTensor T' φ M').val.obj (op ((proEtaleBaseChange h).obj U)) from
        (tensorUnit φ M').val.app _ (c.val.app _ (tateUnit h R M U x))) = _
    rw [tensorUnit_apply, tateTmul_eq_smul]
    simp only [one_smul]
    exact (tateTmul_eq_smul _ _ _ _ _).symm
  · intro b hb
    apply e.injective
    rw [e.apply_symm_apply]
    apply pullback_unit_ext h R M ((tateRestrict T' φ).obj (tateTensor T' φ M'))
    intro U x
    rw [tensorPullbackHomEquiv_apply]
    have hh := hb U 1 x
    simpa only [tateRingUnit, map_one, g, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, tensorUnit_apply] using hh

/-- The uniquely normalized `c ⊗ 1` after the canonical tensor pullback comparison.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M' :=
  (tateTensorMap_existsUnique h φ M M' c).exists.choose

private theorem tateUnit_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    (R : Type u) [CommRing R] [IsIso (proEtaleCoefficientInverseImageMap h R)]
    (M N : tateModules T R) (f : M ⟶ N) (U : T.ProEt) (x : M.val.obj (op U)) :
    ((tatePullback h R).map f).val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h R M U x) = tateUnit h R N U (f.val.app (op U) x) :=
  (congrArg (fun k ↦ k.val.app (op U) x) ((tateAdj h R).unit.naturality f)).symm

private theorem tensorMap_apply {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    IsTateTensorMap h φ M M' c (tateTensorMap h φ M M' c) :=
  (tateTensorMap_existsUnique h φ M M' c).exists.choose_spec

attribute [local irreducible] tateTensorMap

private theorem tensorPullbackHomEquiv_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (H H' : tateModules T' A)
    (b : (tatePullback h A).obj (tateTensor T φ M) ⟶ H) (f : H ⟶ H') :
    tensorPullbackHomEquiv h φ M H' (b ≫ f) =
      tensorPullbackHomEquiv h φ M H b ≫ (tateRestrict T' φ).map f := by
  apply pullback_unit_ext h R M ((tateRestrict T' φ).obj H')
  intro U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    tensorPullbackHomEquiv_apply]
  rfl

private theorem tensorHomEquiv_naturality (T : Scheme.{u})
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (M : tateModules T R) (H H' : tateModules T A)
    (b : tateTensor T φ M ⟶ H) (f : H ⟶ H') :
    tensorHomEquiv T (tateConstantMap T φ) M H' (b ≫ f) =
      tensorHomEquiv T (tateConstantMap T φ) M H b ≫ (tateRestrict T φ).map f := by
  apply SheafOfModules.hom_ext
  ext U x
  unfold tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction
  rfl

private theorem tensorMap_equiv {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    tensorPullbackHomEquiv h φ M (tateTensor T' φ M') (tateTensorMap h φ M M' c) =
      c ≫ tensorUnit φ M' := by
  apply pullback_unit_ext h R M ((tateRestrict T' φ).obj (tateTensor T' φ M'))
  intro U x
  rw [tensorPullbackHomEquiv_apply]
  have hb := tensorMap_apply h φ M M' c
  simpa only [tateRingUnit, map_one, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, tensorUnit_apply] using hb U 1 x

attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorMap_isIso {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') [IsIso c] :
    IsIso (tateTensorMap h φ M M' c) := by
  apply isIso_of_coyoneda_map_bijective
  intro H
  let e := (tensorHomEquiv T' (tateConstantMap T' φ) M' H).trans
    ((Iso.homCongr (asIso c).symm (Iso.refl _)).trans
      (tensorPullbackHomEquiv h φ M H).symm)
  have hh : (fun f ↦ tateTensorMap h φ M M' c ≫ f) = e := by
    funext f
    apply (tensorPullbackHomEquiv h φ M H).injective
    rw [tensorPullbackHomEquiv_naturality, tensorMap_equiv]
    change c ≫ tensorUnit φ M' ≫ (tateRestrict T' φ).map f = _
    unfold tensorUnit
    erw [← tensorHomEquiv_naturality T' φ M' _ H (𝟙 _) f]
    exact ((tensorPullbackHomEquiv h φ M H).apply_symm_apply _).symm
  rw [hh]
  exact e.bijective

/-- The constant quotient map from p-adic integers at positive level `n + 1`.
Source: Stacks Tag 03PK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePadicReduction (l n : ℕ) [Fact l.Prime] :
    ULift.{u} (PadicInt l) →+* ULift.{u} (ZMod (l ^ (n + 1))) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- The projection tensor formula, using the finite module's quotient-scalar presentation.
The isomorphism i identifies its restriction to R with the specified finite level.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateReduction {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F)
    (α : tateTensor T (a.comp q) L ⟶ tateTensor T a G) : Prop :=
  ∀ (U : T.ProEt) (z : (proEtaleConstantRing T A).obj.obj (op U))
    (x : L.val.obj (op U)),
    α.val.app (op U) (tateTmul (a.comp q) L U z x) =
      tateTmul a G U z (i.inv.val.app (op U) (p.val.app (op U) x))

private theorem tateConstantMap_comp (T : Scheme.{u})
    {R Q A : Type u} [CommRing R] [CommRing Q] [CommRing A]
    (q : R →+* Q) (a : Q →+* A) :
    tateConstantMap T (a.comp q) = tateConstantMap T q ≫ tateConstantMap T a := by
  unfold tateConstantMap
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private def reductionUnit {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    L ⟶ (tateRestrict T (a.comp q)).obj (tateTensor T a G) where
  val :=
    { app U := ModuleCat.ofHom
        (X := L.val.obj U)
        (Y := ((tateRestrict T (a.comp q)).obj (tateTensor T a G)).val.obj U)
        { toFun := fun x ↦ (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x))
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro r x
            have hi := (i.inv.val.app U).hom.map_smul r (p.val.app U x)
            have hp := (p.val.app U).hom.map_smul r x
            have ht := ((tensorUnit a G).val.app U).hom.map_smul
              ((tateConstantMap T q).hom.app U r) (i.inv.val.app U (p.val.app U x))
            change (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U (r • x))) =
              (tateConstantMap T (a.comp q)).hom.app U r •
                (show (tateTensor T a G).val.obj U from
                  (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x)))
            rw [tateConstantMap_comp]
            rw [hp, hi]
            exact ht }
      naturality := by
        intro U V f
        ext x
        exact (congrArg (fun y ↦ (tensorUnit a G).val.app V (i.inv.val.app V y))
          (PresheafOfModules.naturality_apply p.val f x)).trans
          ((congrArg (fun y ↦ (tensorUnit a G).val.app V y)
            (PresheafOfModules.naturality_apply i.inv.val f (p.val.app U x))).trans
            (PresheafOfModules.naturality_apply (tensorUnit a G).val f _)) }

private theorem reductionUnit_apply {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F)
    (U : T.ProEt) (x : L.val.obj (op U)) :
    (reductionUnit q a L F G i p).val.app (op U) x =
      tateTmul a G U 1 (i.inv.val.app (op U) (p.val.app (op U) x)) := by
  exact tensorUnit_apply a G U _

attribute [local irreducible] reductionUnit

/-- The map α is defined by the projection on the first factor, with no chosen square.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the projection is R-linear after restricting G along q. Thus its tensor with A
is balanced: p(rx) ⊗ z = p(x) ⊗ a(q(r))z. The tensor universal property and
sheafification produce α; pure tensors locally generate, proving uniqueness.
This is the balancing calculation of proof step 6. -/
theorem tateReduction_existsUnique {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    ∃! α : tateTensor T (a.comp q) L ⟶ tateTensor T a G,
      IsTateReduction q a L F G i p α := by
  let g := reductionUnit q a L F G i p
  let e := tensorHomEquiv T (tateConstantMap T (a.comp q)) L (tateTensor T a G)
  refine ⟨e.symm g, ?_, ?_⟩
  · intro U z x
    change (e.symm g).val.app (op U)
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheafOfUniverses
          (tateConstantMap T (a.comp q)) L).presheaf).app (op U)
        (z ⊗ₜ[_, ((tateConstantMap T (a.comp q)).hom.app (op U)).hom] x)) = _
    rw [tensorHomEquiv_tmul]
    change z • (show (tateTensor T a G).val.obj (op U) from
      (e (e.symm g)).val.app (op U) x) = _
    rw [e.apply_symm_apply]
    change z • (show (tateTensor T a G).val.obj (op U) from
      g.val.app (op U) x) = _
    dsimp only [g]
    rw [reductionUnit_apply]
    symm
    exact tateTmul_eq_smul a G U z _
  · intro α hα
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (tensorHomEquiv T (tateConstantMap T (a.comp q)) L
      (tateTensor T a G) α).val.app U x = _
    rw [tensorHomEquiv_apply]
    change α.val.app U (tateTmul (a.comp q) L U.unop 1 x) =
      (reductionUnit q a L F G i p).val.app U x
    rw [reductionUnit_apply]
    exact hα U.unop 1 x

/-- The uniquely balanced projection tensor map α.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateReduction {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    tateTensor T (a.comp q) L ⟶ tateTensor T a G :=
  (tateReduction_existsUnique q a L F G i p).exists.choose

private theorem reduction_apply {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    IsTateReduction q a L F G i p (tateReduction q a L F G i p) :=
  (tateReduction_existsUnique q a L F G i p).exists.choose_spec

attribute [local irreducible] tateReduction

/-- The finite-level `β_N ⊗ 1`, normalized on pulled back local pure tensors.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateFiniteTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q A : Type u} [CommRing R] [CommRing Q] [CommRing A]
    (q : R →+* Q) (a : Q →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : tateModules T R) (F' : tateModules T' R)
    (G : tateModules T Q) (G' : tateModules T' Q)
    (i : (tateRestrict T q).obj G ≅ F) (i' : (tateRestrict T' q).obj G' ≅ F')
    (β : (tatePullback h R).obj F ≅ F')
    (d : (tatePullback h A).obj (tateTensor T a G) ⟶ tateTensor T' a G') : Prop :=
  ∀ (U : T.ProEt) (z : (proEtaleConstantRing T A).obj.obj (op U))
    (y : G.val.obj (op U)),
    d.val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h A (tateTensor T a G) U (tateTmul a G U z y)) =
      tateTmul a G' ((proEtaleBaseChange h).obj U) (tateRingUnit h A U z)
        (i'.inv.val.app (op ((proEtaleBaseChange h).obj U))
          (β.hom.val.app (op ((proEtaleBaseChange h).obj U))
            (tateUnit h R F U (i.hom.val.app (op U) y))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientConstantPresentation (T : Scheme.{u})
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q) (M : tateModules T R)
    (hk : ∀ (U : T.ProEtᵒᵖ) (r : R), q r = 0 →
      ∀ x : M.val.obj U, (constantUnit T R).app U (ULift.up r) • x = 0) :
    ∃ G : tateModules T Q, Nonempty ((tateRestrict T q).obj G ≅ M) := by
  let q' : ULift.{u + 1, u} R →+* ULift.{u + 1, u} Q :=
    ULift.ringEquiv.symm.toRingHom.comp (q.comp ULift.ringEquiv.toRingHom)
  have hq' : Function.Surjective q' := fun x ↦ by
    obtain ⟨r, hr⟩ := hq x.down
    exact ⟨ULift.up r, congrArg ULift.up hr⟩
  let P := (PresheafOfModules.restrictScalars (constantUnit T R)).obj M.val
  let e (U : T.ProEtᵒᵖ) : ULift.{u + 1, u} R →+* AddMonoid.End (P.obj U) :=
    Module.toAddMonoidEnd _ _
  have he (U : T.ProEtᵒᵖ) : RingHom.ker q' ≤ RingHom.ker (e U) := by
    intro r hr
    apply AddMonoidHom.ext
    intro x
    exact hk U r.down (congrArg ULift.down hr) x
  let a (U : T.ProEtᵒᵖ) := q'.liftOfSurjective hq' ⟨e U, he U⟩
  let modQ (U : T.ProEtᵒᵖ) : Module (ULift.{u + 1, u} Q) (M.val.presheaf.obj U) :=
    Module.compHom (P.obj U) (a U)
  let : ∀ U : T.ProEtᵒᵖ,
      Module (((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Q))).obj U)
        (M.val.presheaf.obj U) := modQ
  have ha (U : T.ProEtᵒᵖ) (r : ULift.{u + 1, u} R) (x : M.val.obj U) :
      @SMul.smul _ _ (modQ U).toSMul (q' r) x = (constantUnit T R).app U r • x := by
    exact congrArg (fun f : AddMonoid.End (P.obj U) ↦ f x)
      (q'.liftOfSurjective_comp_apply hq' ⟨e U, he U⟩ r)
  let N : PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Q))) :=
    PresheafOfModules.ofPresheaf M.val.presheaf (fun {U V} f r x ↦ by
      obtain ⟨r, rfl⟩ := hq' r
      change M.val.presheaf.map f (@SMul.smul _ _ (modQ U).toSMul (q' r) x) =
        @SMul.smul _ _ (modQ V).toSMul (q' r) (M.val.presheaf.map f x)
      erw [ha, ha]
      exact P.map_smul f r x)
  let G := PresheafOfModules.sheafify (constantUnit T Q)
    (M₀ := N) (A := ⟨M.val.presheaf, M.isSheaf⟩) (𝟙 _)
  have hg (U : T.ProEtᵒᵖ) (r : ULift.{u + 1, u} R) (x : G.val.obj U) :
      (constantUnit T R).app U r •
          (show ((tateRestrict T q).obj G).val.obj U from x) =
        (constantUnit T R).app U r • (show M.val.obj U from x) := by
    have hc := congrArg (fun f ↦ f.app U r) (constantUnit_map T q)
    change (tateConstantMap T q).hom.app U ((constantUnit T R).app U r) =
      (constantUnit T Q).app U (q' r) at hc
    change (tateConstantMap T q).hom.app U ((constantUnit T R).app U r) • x = _
    rw [hc]
    have hh := PresheafOfModules.Sheafify.map_smul_eq (constantUnit T Q)
      (M₀ := N) (A := ⟨M.val.presheaf, M.isSheaf⟩) (𝟙 _)
      ((constantUnit T Q).app U (q' r)) x (𝟙 U) (q' r) (by simp) x (by
        change x = M.val.presheaf.map (𝟙 U) x
        rw [CategoryTheory.Functor.map_id]
        rfl)
    change M.val.presheaf.map (𝟙 U) _ = _ at hh
    rw [CategoryTheory.Functor.map_id] at hh
    change (constantUnit T Q).app U (q' r) • x =
      @SMul.smul _ _ (modQ U).toSMul (q' r) x at hh
    exact hh.trans (ha U r x)
  let g : (tateRestrict T q).obj G ⟶ M :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (M₁ := ((tateRestrict T q).obj G).val) (M₂ := M.val)
      (constantUnit T R) M.isSheaf).symm
        (PresheafOfModules.homMk
          (M₁ := (PresheafOfModules.restrictScalars (constantUnit T R)).obj
            ((tateRestrict T q).obj G).val)
          (M₂ := P) (𝟙 M.val.presheaf) (fun U r x ↦ hg U r x))⟩
  let g' : M ⟶ (tateRestrict T q).obj G := by
    apply SheafOfModules.Hom.mk
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (M₁ := M.val) (M₂ := ((tateRestrict T q).obj G).val)
      (constantUnit T R) ((tateRestrict T q).obj G).isSheaf).symm
        (PresheafOfModules.homMk
          (M₁ := P)
          (M₂ := (PresheafOfModules.restrictScalars (constantUnit T R)).obj
            ((tateRestrict T q).obj G).val)
          (𝟙 M.val.presheaf) (fun U r x ↦ (hg U r x).symm))
  exact ⟨G, ⟨{ hom := g
               inv := g'
               hom_inv_id := by ext U x; rfl
               inv_hom_id := by ext U x; rfl }⟩⟩

/-- The quotient action on a killed module is unique up to its unique compatible isomorphism.
The universal property fixes the object up to exactly the isomorphisms used downstream.
Source: Stacks Tag 03EK and the quotient coefficient action in the finite Kummer-level proof
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: locally lift a section of the constant Z/l^N sheaf to Z_l. Act by a lift;
two lifts differ locally by l^N times a section, which annihilates M. Independence
and the sheaf condition glue this action. Ring and restriction identities are local.
This gives G on the same underlying abelian sheaf and its restriction identification.
Every other presentation has this same action, so the two identifications determine
the unique Q-linear isomorphism between them. -/
theorem tateFinitePresentation_exists (l n : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (M : tateModules T (ULift.{u} (PadicInt l)))
    (hM : ∀ (U : T.ProEt) (x : M.val.obj (op U)), (l ^ (n + 1)) • x = 0) :
    ∃ G : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))),
      ∃ i : (tateRestrict T (tatePadicReduction l n)).obj G ≅ M,
        ∀ (H : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))))
          (j : (tateRestrict T (tatePadicReduction l n)).obj H ≅ M),
          ∃! e : G ≅ H,
            (tateRestrict T (tatePadicReduction l n)).mapIso e ≪≫ j = i := by
  let q := tatePadicReduction.{u} l n
  have hq : Function.Surjective q := fun x ↦ by
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  obtain ⟨G, ⟨i⟩⟩ := quotientConstantPresentation T q hq M (by
    intro U r hr x
    have hr' : r.down ∈ RingHom.ker (PadicInt.toZModPow (n + 1) (p := l)) :=
      congrArg ULift.down hr
    rw [PadicInt.ker_toZModPow] at hr'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr'
    have hr'' : r = ULift.up c * (l ^ (n + 1) : ULift.{u} (PadicInt l)) := by
      apply ULift.ext
      exact hc.symm
    rw [hr'']
    change (constantUnit T (ULift.{u} (PadicInt l))).app U
      (ULift.up (ULift.up c) * (l ^ (n + 1) : ULift.{u + 1} (ULift.{u} (PadicInt l)))) • x = 0
    rw [map_mul, mul_smul]
    have hz : (constantUnit T (ULift.{u} (PadicInt l))).app U
        (l ^ (n + 1) : ULift.{u + 1} (ULift.{u} (PadicInt l))) • x = 0 := by
      rw [← Nat.cast_pow, map_natCast, Nat.cast_smul_eq_nsmul]
      exact hM U.unop x
    rw [hz, smul_zero])
  let F := tateRestrict T q
  let ff : F.FullyFaithful :=
    { preimage := fun f ↦ (restrictHomEquiv T q hq _ _).symm f
      map_preimage := fun f ↦ by
        simpa only [restrictHomEquiv_apply] using
          (restrictHomEquiv T q hq _ _).apply_symm_apply f
      preimage_map := fun f ↦ by
        simpa only [restrictHomEquiv_apply] using
          (restrictHomEquiv T q hq _ _).symm_apply_apply f }
  refine ⟨G, i, ?_⟩
  intro H j
  refine ⟨ff.preimageIso (i ≪≫ j.symm), ?_, ?_⟩
  · apply Iso.ext
    simp
  · intro e he
    apply Iso.ext
    apply ff.map_injective
    have hh := congrArg Iso.hom he
    exact (cancel_mono j.hom).mp (by simpa using hh)

/-- The finite Q-module, selected from the quotient action's universal property.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteModule (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))) :=
  (tateFinitePresentation_exists l n T (F.obj (op n)) (hF n)).choose

/-- The canonical restriction identification of the finite quotient action.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteModuleIso (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    (tateRestrict T (tatePadicReduction l n)).obj (tateFiniteModule l n F hF) ≅
      F.obj (op n) :=
  (tateFinitePresentation_exists l n T (F.obj (op n)) (hF n)).choose_spec.choose

private def quotientPullbackHomEquiv {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h Q)]
    (G : tateModules T Q) (H : tateModules T' Q) :
    ((tatePullback h Q).obj G ⟶ H) ≃
      ((tatePullback h R).obj ((tateRestrict T q).obj G) ⟶
        (tateRestrict T' q).obj H) :=
  ((tateAdj h Q).homEquiv G H).trans
    ((restrictHomEquiv T q hq G ((tatePush h Q).obj H)).trans
      ((Iso.homCongr (Iso.refl _) (directScalarIso h q H)).trans
        ((tateAdj h R).homEquiv ((tateRestrict T q).obj G) ((tateRestrict T' q).obj H)).symm))

private theorem quotientPullbackHomEquiv_apply {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h Q)]
    (G : tateModules T Q) (H : tateModules T' Q)
    (b : (tatePullback h Q).obj G ⟶ H) (U : T.ProEt) (x : G.val.obj (op U)) :
    (quotientPullbackHomEquiv h q hq G H b).val.app
        (op ((proEtaleBaseChange h).obj U))
        (tateUnit h R ((tateRestrict T q).obj G) U x) =
      b.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h Q G U x) := by
  have he := ((tateAdj h R).homEquiv ((tateRestrict T q).obj G) ((tateRestrict T' q).obj
    H)).apply_symm_apply
    ((restrictHomEquiv T q hq G ((tatePush h Q).obj H))
      (((tateAdj h Q).homEquiv G H) b) ≫ (directScalarIso h q H).hom)
  have hx := congrArg (fun f ↦ f.val.app (op U) x) he
  rw [tateAdj_apply] at hx
  change (quotientPullbackHomEquiv h q hq G H b).val.app
    (op ((proEtaleBaseChange h).obj U))
    (tateUnit h R ((tateRestrict T q).obj G) U x) =
      (directScalarIso h q H).hom.val.app (op U)
        (((restrictHomEquiv T q hq G ((tatePush h Q).obj H))
          (((tateAdj h Q).homEquiv G H) b)).val.app (op U) x) at hx
  rw [directScalarIso_hom_apply, restrictHomEquiv_apply] at hx
  exact hx.trans (tateAdj_apply h Q G H b U x)

attribute [local irreducible] quotientPullbackHomEquiv

private theorem quotientPullbackHomEquiv_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h Q)]
    (G : tateModules T Q) (H H' : tateModules T' Q)
    (b : (tatePullback h Q).obj G ⟶ H) (f : H ⟶ H') :
    quotientPullbackHomEquiv h q hq G H' (b ≫ f) =
      quotientPullbackHomEquiv h q hq G H b ≫ (tateRestrict T' q).map f := by
  apply pullback_unit_ext h R ((tateRestrict T q).obj G) ((tateRestrict T' q).obj H')
  intro U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    quotientPullbackHomEquiv_apply]
  rfl

private theorem quotientPullback_isIso {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q)
    (hq : Function.Surjective q)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h Q)]
    (G : tateModules T Q) (H : tateModules T' Q)
    (b : (tatePullback h Q).obj G ⟶ H)
    [IsIso (quotientPullbackHomEquiv h q hq G H b)] : IsIso b := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  let e := (restrictHomEquiv T' q hq H N).trans
    ((Iso.homCongr (asIso (quotientPullbackHomEquiv h q hq G H b)).symm
      (Iso.refl _)).trans (quotientPullbackHomEquiv h q hq G N).symm)
  have he : (fun f ↦ b ≫ f) = e := by
    funext f
    apply (quotientPullbackHomEquiv h q hq G N).injective
    rw [quotientPullbackHomEquiv_naturality]
    change (quotientPullbackHomEquiv h q hq G H b) ≫ (tateRestrict T' q).map f =
      (quotientPullbackHomEquiv h q hq G N)
        ((quotientPullbackHomEquiv h q hq G N).symm
          ((quotientPullbackHomEquiv h q hq G H b) ≫ restrictHomEquiv T' q hq H N f))
    rw [restrictHomEquiv_apply, Equiv.apply_symm_apply]
  rw [he]
  exact e.bijective

/-- The finite tensor square and its isomorphism conclusion.
The finite Q-module presentations i and i' express exactly the quotient actions on
F_N and F'_N; the coefficient map a is the action of Z/l^N on A, fixed by ha.
Source: the final sentence of the finite Kummer-level blueprint proof; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: steps 5--6 identify the inverse image of each tensor with the tensor of the
inverse images. The R-linear level isomorphism is Q-linear because R → Q is locally
surjective. Tensor it with A to obtain d and tensor c with A to obtain b. On a pure
tensor the two square composites are β_N(h⁻¹p_N(x)) ⊗ a and p'_N(c(h⁻¹x)) ⊗ a;
the limit projection equation identifies them. Local generation gives equality.
For step 8, tensor the inverse of β_N to invert d. If both α maps are invertible,
the square expresses b as a composite of three isomorphisms. -/
theorem tateInverseLimitFiniteTensorBaseChange (l n : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    (a : ULift.{u} (ZMod (l ^ (n + 1))) →+* A)
    (ha : a.comp (tatePadicReduction l n) =
      (algebraMap (PadicInt l) A).comp ULift.ringEquiv.toRingHom)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (ZMod (l ^ (n + 1)))))]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F')
    (G : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))))
    (G' : tateModules T' (ULift.{u} (ZMod (l ^ (n + 1)))))
    (i : (tateRestrict T (tatePadicReduction l n)).obj G ≅ F.obj (op n))
    (i' : (tateRestrict T' (tatePadicReduction l n)).obj G' ≅ F'.obj (op n)) :
    ∃ d : (tatePullback h A).obj (tateTensor T a G) ⟶ tateTensor T' a G',
      IsTateFiniteTensorMap h (tatePadicReduction l n) a
        (F.obj (op n)) (F'.obj (op n)) G G' i i' (β.app (op n)) d ∧
      IsIso d ∧
      tateTensorMap h (a.comp (tatePadicReduction l n)) (limit F) (limit F')
          (tateLimitMap h _ F F' β) ≫
          tateReduction (tatePadicReduction l n) a
            (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n)) =
        (tatePullback h A).map
          (tateReduction (tatePadicReduction l n) a
            (limit F) (F.obj (op n)) G i (limit.π F (op n))) ≫ d ∧
      (IsIso (tateReduction (tatePadicReduction l n) a
          (limit F) (F.obj (op n)) G i (limit.π F (op n))) →
        IsIso (tateReduction (tatePadicReduction l n) a
          (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n))) →
        IsIso (tateTensorMap h (a.comp (tatePadicReduction l n)) (limit F) (limit F')
          (tateLimitMap h _ F F' β))) := by
  have _ := hA
  have _ := ha
  let q := tatePadicReduction.{u} l n
  have hq : Function.Surjective q := fun x ↦ by
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  let c : (tatePullback h _).obj ((tateRestrict T q).obj G) ⟶
      (tateRestrict T' q).obj G' :=
    (tatePullback h _).map i.hom ≫ (β.app (op n)).hom ≫ i'.inv
  let e := quotientPullbackHomEquiv h q hq G G'
  let b := e.symm c
  have hb : e b = c := e.apply_symm_apply c
  have : IsIso c := by dsimp [c]; infer_instance
  have : IsIso (e b) := by erw [hb]; infer_instance
  have : IsIso b := quotientPullback_isIso h q hq G G' b
  let d := tateTensorMap h a G G' b
  have hd : IsTateFiniteTensorMap h q a (F.obj (op n)) (F'.obj (op n))
      G G' i i' (β.app (op n)) d := by
    intro U z y
    dsimp only [d]
    erw [tensorMap_apply]
    congr 1
    have hh := quotientPullbackHomEquiv_apply h q hq G G' b U y
    change (e b).val.app (op ((proEtaleBaseChange h).obj U)) _ = _ at hh
    erw [hb] at hh
    dsimp only [c] at hh
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hh
    exact hh.symm.trans (congrArg
      (fun z ↦ i'.inv.val.app (op ((proEtaleBaseChange h).obj U))
        ((β.app (op n)).hom.val.app (op ((proEtaleBaseChange h).obj U)) z))
      (tateUnit_naturality h (ULift.{u} (PadicInt l))
        ((tateRestrict T q).obj G) (F.obj (op n)) i.hom U y))
  have hs : tateTensorMap h (a.comp q) (limit F) (limit F')
        (tateLimitMap h _ F F' β) ≫
        tateReduction q a (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n)) =
      (tatePullback h A).map
        (tateReduction q a (limit F) (F.obj (op n)) G i (limit.π F (op n))) ≫ d := by
    apply tensorPullback_unit_ext h (a.comp q) (limit F) (tateTensor T' a G')
    intro U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    have ht := tensorMap_apply h (a.comp q) (limit F) (limit F')
      (tateLimitMap h _ F F' β) U 1 x
    simp only [tateRingUnit, map_one] at ht
    have hl := (congrArg (fun y ↦
      (tateReduction q a (limit F') (F'.obj (op n)) G' i'
        (limit.π F' (op n))).val.app (op ((proEtaleBaseChange h).obj U)) y) ht).trans
      (reduction_apply q a (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n))
        ((proEtaleBaseChange h).obj U) 1
        ((tateLimitMap h _ F F' β).val.app (op ((proEtaleBaseChange h).obj U))
          (tateUnit h _ (limit F) U x)))
    have hu := tateUnit_naturality h A (tateTensor T (a.comp q) (limit F))
      (tateTensor T a G)
      (tateReduction q a (limit F) (F.obj (op n)) G i (limit.π F (op n)))
      U (tateTmul (a.comp q) (limit F) U 1 x)
    have hr := congrArg (fun y ↦ d.val.app (op ((proEtaleBaseChange h).obj U)) y)
      (hu.trans (congrArg (tateUnit h A (tateTensor T a G) U)
        (reduction_apply q a (limit F) (F.obj (op n)) G i
          (limit.π F (op n)) U 1 x)))
    have hd' := hd U 1
      (i.inv.val.app (op U) ((limit.π F (op n)).val.app (op U) x))
    simp only [tateRingUnit, map_one] at hd'
    refine hl.trans (Eq.trans ?_ (hr.trans hd').symm)
    have hp := congrArg (fun k : (tatePullback h (ULift.{u} (PadicInt l))).obj
        (limit F) ⟶ F'.obj (op n) ↦ k.val.app (op ((proEtaleBaseChange h).obj U))
      (tateUnit h _ (limit F) U x))
      ((tateInverseLimitBaseChange l h F F' hF hF' β).1 n)
    change (limit.π F' (op n)).val.app (op ((proEtaleBaseChange h).obj U))
      ((tateLimitMap h _ F F' β).val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h _ (limit F) U x)) =
      (β.app (op n)).hom.val.app (op ((proEtaleBaseChange h).obj U))
        (((tatePullback h _).map (limit.π F (op n))).val.app
          (op ((proEtaleBaseChange h).obj U)) (tateUnit h _ (limit F) U x)) at hp
    have hp' := hp.trans (congrArg ((β.app (op n)).hom.val.app
      (op ((proEtaleBaseChange h).obj U)))
      (tateUnit_naturality h (ULift.{u} (PadicInt l)) (limit F)
        (F.obj (op n)) (limit.π F (op n)) U x))
    have hi := congrArg (fun k : F.obj (op n) ⟶ F.obj (op n) ↦
      k.val.app (op U)
      ((limit.π F (op n)).val.app (op U) x)) i.inv_hom_id
    change i.hom.val.app (op U)
      (i.inv.val.app (op U) ((limit.π F (op n)).val.app (op U) x)) =
        (limit.π F (op n)).val.app (op U) x at hi
    have hi' := congrArg (fun y ↦ (β.app (op n)).hom.val.app
      (op ((proEtaleBaseChange h).obj U)) (tateUnit h _ (F.obj (op n)) U y)) hi
    exact congrArg (fun y ↦ tateTmul a G' ((proEtaleBaseChange h).obj U) 1
      (i'.inv.val.app (op ((proEtaleBaseChange h).obj U)) y)) (hp'.trans hi'.symm)
  refine ⟨d, hd, tensorMap_isIso h a G G' b, hs, ?_⟩
  intro hα hα'
  have := hα
  have := hα'
  have : IsIso d := tensorMap_isIso h a G G' b
  have hi : IsIso (tateTensorMap h (a.comp q) (limit F) (limit F')
      (tateLimitMap h _ F F' β) ≫
        tateReduction q a (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n))) := by
    exact hs.symm ▸ (inferInstance : IsIso
      ((tatePullback h A).map
        (tateReduction q a (limit F) (F.obj (op n)) G i (limit.π F (op n))) ≫ d))
  exact IsIso.of_isIso_comp_right _
    (tateReduction q a (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n)))

/-- Unit normalization for the canonical identity inverse-image comparison.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTatePullbackId (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)]
    (e : tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R)) : Prop :=
  ∀ (M : tateModules T R) (U : T.ProEt) (x : M.val.obj (op U)),
    (e.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 T)).obj U))
        (tateUnit (𝟙 T) R M U x) =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

private def tateSheafPushId (T : Scheme.{u}) :
    proEtaleSheafDirectImage (𝟙 T) CommRingCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) T)
    CommRingCat.{u + 1} (ProEt.topology T)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tateRingUnit_id (T : Scheme.{u}) (R : Type u) [CommRing R] :
    proEtaleCoefficientDirectImageMap (𝟙 T) R =
      (tateSheafPushId T).inv.app (proEtaleConstantRing T R) := by
  apply ((sheafificationAdjunction (ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change toSheafify _ _ ≫ (proEtaleCoefficientDirectImageMap (𝟙 T) R).hom = _
  rw [show toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R))) ≫
        (proEtaleCoefficientDirectImageMap (𝟙 T) R).hom =
      Functor.whiskerLeft (proEtaleBaseChange (𝟙 T)).op
        (toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R)))) from
    ((sheafificationAdjunction (ProEt.topology T)
      CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _]
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R)))).app
      (op ((proEtaleBaseChange (𝟙 T)).obj U.unop)) =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R)))).app U ≫
        (proEtaleConstantRing T R).obj.map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U.unop).op
  have hn :=
    (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} R)))).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn

private def tatePushId (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    tatePush (𝟙 T) R ≅ 𝟭 (tateModules T R) := by
  letI : (𝟭 T.ProEt).IsContinuous (ProEt.topology T) (ProEt.topology T) :=
    Functor.isContinuous_id _
  let A := (adicLisseForget T).obj (proEtaleConstantRing T R)
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) T
  let t : A ⟶ ((proEtaleBaseChange (𝟙 T)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology T) (ProEt.topology T)).obj A :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 T) (proEtaleConstantRing T R)
        (proEtaleConstantRing T R)
        (asIso (proEtaleCoefficientInverseImageMap (𝟙 T) R))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [tateDirectMap_eq, tateRingUnit_id]
    ext U x
    change ((proEtaleConstantRing T R).obj.map (e.hom.app U.unop).op ≫
      (proEtaleConstantRing T R).obj.map (e.inv.app U.unop).op) x = x
    rw [← (proEtaleConstantRing T R).obj.map_comp, ← CategoryTheory.op_comp,
      Iso.inv_hom_id_app, CategoryTheory.op_id, (proEtaleConstantRing T R).obj.map_id]
    rfl
  exact SheafOfModules.pushforwardCongr₂ (J := ProEt.topology T)
    (K := ProEt.topology T) (F := 𝟭 T.ProEt) (G := proEtaleBaseChange (𝟙 T))
    (φ := t) e.symm ht ≪≫
    SheafOfModules.pushforwardId (K := ProEt.topology T) A

/-- The identity comparison, fixed by its actual inverse-image unit.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: base change by an identity is isomorphic to the identity on the site. Take
the mate of this direct-image identification under the normalized module adjunction.
Its unit equation is the displayed formula. Units locally generate the inverse image,
so this formula fixes every component and hence the natural isomorphism uniquely. -/
theorem tatePullbackId_existsUnique (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    ∃! e : tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R), IsTatePullbackId T R e := by
  let e := (tateAdj (𝟙 T) R).leftAdjointIdIso (tatePushId T R)
  have he : IsTatePullbackId T R e := by
    intro M U x
    have hu := unit_conjugateEquiv Adjunction.id (tateAdj (𝟙 T) R) e.hom M
    rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at hu
    have hu' := (congrArg (fun f ↦ f.val.app (op U) x) hu).symm
    change (e.hom.app M).val.app _ (tateUnit (𝟙 T) R M U x) =
      ((tatePushId T R).inv.app M).val.app (op U) x at hu'
    exact hu'
  refine ⟨e, he, ?_⟩
  intro f hf
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply pullback_unit_ext (𝟙 T) R M M
  intro U x
  exact (hf M U x).trans (he M U x).symm

/-- The canonical identity comparison from its unique unit normalization.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullbackId (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R) :=
  (tatePullbackId_existsUnique T R).exists.choose

private theorem pullbackId_normalized (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    IsTatePullbackId T R (tatePullbackId T R) :=
  (tatePullbackId_existsUnique T R).exists.choose_spec

attribute [local irreducible] tatePullbackId

/-- The canonical inverse-image compositor on constant-coefficient modules: the existing
ordinary composition comparison `exchangeModuleComposition`, whose right-adjoint conjugate
is the sectionwise fibre-product pasting, transported along the canonical equality of the
composite constant-coefficient comparison `proEtaleConstantRingCompositeCoefficients_eq`.
No second compositor is constructed.
Source: Stacks Tags 03D8, 0D6D and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullbackComp {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)] :
    tatePullback (g ≫ h) R ≅ tatePullback h R ⋙ tatePullback g R :=
  eqToIso (congrArg (fun c ↦ proEtaleRingModulePullback (g ≫ h)
      (proEtaleConstantRing T R) (proEtaleConstantRing T'' R) c)
      (proEtaleConstantRingCompositeCoefficients_eq g h R).symm) ≪≫
    exchangeModuleComposition g h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
      (proEtaleConstantRing T'' R) (asIso (proEtaleCoefficientInverseImageMap h R))
      (asIso (proEtaleCoefficientInverseImageMap g R))

private theorem tatePullbackComp_eq {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)] :
    tatePullbackComp h g R =  eqToIso (congrArg (fun c ↦ proEtaleRingModulePullback (g ≫ h)
      (proEtaleConstantRing T R) (proEtaleConstantRing T'' R) c)
      (proEtaleConstantRingCompositeCoefficients_eq g h R).symm) ≪≫
    exchangeModuleComposition g h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
      (proEtaleConstantRing T'' R) (asIso (proEtaleCoefficientInverseImageMap h R))
      (asIso (proEtaleCoefficientInverseImageMap g R)) := rfl

attribute [local irreducible] exchangeModuleComposition

private theorem exchangeComposition_unit {T T' T'' : Scheme.{u}}
    (h : T' ⟶ T) (g : T'' ⟶ T')
    (RH : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (RI : Sheaf (ProEt.topology T') CommRingCat.{u + 1})
    (RJ : Sheaf (ProEt.topology T'') CommRingCat.{u + 1})
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RH ≅ RI)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RI ≅ RJ)
    (M : proEtaleRingModules T RH) (U : T.ProEt) (x : M.val.obj (op U)) :
    ((exchangeModuleComposition g h RH RI RJ ch cg).hom.app M).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))
      (((proEtaleRingModuleAdjunction (g ≫ h) RH RJ
        (proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)).unit.app M).val.app
          (op U) x) =
    ((proEtaleRingModulePullback g RI RJ cg).obj
      ((proEtaleRingModulePullback h RH RI ch).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
          (((proEtaleRingModuleAdjunction g RI RJ cg).unit.app
            ((proEtaleRingModulePullback h RH RI ch).obj M)).val.app
              (op ((proEtaleBaseChange h).obj U))
                (((proEtaleRingModuleAdjunction h RH RI ch).unit.app M).val.app (op U) x)) := by
  let adj := (proEtaleRingModuleAdjunction h RH RI ch).comp
    (proEtaleRingModuleAdjunction g RI RJ cg)
  let adjc := proEtaleRingModuleAdjunction (g ≫ h) RH RJ
    (proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)
  let e := exchangeModuleComposition g h RH RI RJ ch cg
  have hn : ExchangeModuleCompositionNormalized g h RH RI RJ ch cg e := by
    unfold e exchangeModuleComposition
    exact (exchangeModuleComposition_existsUnique g h RH RI RJ ch cg).choose_spec.1
  have hu := unit_conjugateEquiv adj adjc e.hom M
  have hu' := congrArg (fun f ↦ f.val.app (op U) x) hu
  have hnval := hn
    ((proEtaleRingModulePullback h RH RI ch ⋙
      proEtaleRingModulePullback g RI RJ cg).obj M) U
    ((adj.unit.app M).val.app (op U) x)
  exact hu'.symm.trans hnval

private theorem exchangeComposition_transport_unit {T T' T'' : Scheme.{u}}
    (h : T' ⟶ T) (g : T'' ⟶ T')
    (RH : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (RI : Sheaf (ProEt.topology T') CommRingCat.{u + 1})
    (RJ : Sheaf (ProEt.topology T'') CommRingCat.{u + 1})
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RH ≅ RI)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RI ≅ RJ)
    (cc : (proEtaleSheafInverseImage (g ≫ h) CommRingCat.{u + 1}).obj RH ≅ RJ)
    (hc : cc = proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)
    (M : proEtaleRingModules T RH) (U : T.ProEt) (x : M.val.obj (op U)) :
    ((eqToIso (congrArg (fun c ↦ proEtaleRingModulePullback (g ≫ h) RH RJ c) hc) ≪≫
      exchangeModuleComposition g h RH RI RJ ch cg).hom.app M).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))
      (((proEtaleRingModuleAdjunction (g ≫ h) RH RJ cc).unit.app M).val.app
          (op U) x) =
    ((proEtaleRingModulePullback g RI RJ cg).obj
      ((proEtaleRingModulePullback h RH RI ch).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
          (((proEtaleRingModuleAdjunction g RI RJ cg).unit.app
            ((proEtaleRingModulePullback h RH RI ch).obj M)).val.app
              (op ((proEtaleBaseChange h).obj U))
                (((proEtaleRingModuleAdjunction h RH RI ch).unit.app M).val.app (op U) x)) := by
  cases hc
  exact exchangeComposition_unit h g RH RI RJ ch cg M U x

private theorem exchangeComposition_identified_unit {T T' T'' : Scheme.{u}}
    (h : T' ⟶ T) (g : T'' ⟶ T')
    (RH : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (RI : Sheaf (ProEt.topology T') CommRingCat.{u + 1})
    (RJ : Sheaf (ProEt.topology T'') CommRingCat.{u + 1})
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RH ≅ RI)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RI ≅ RJ)
    (cc : (proEtaleSheafInverseImage (g ≫ h) CommRingCat.{u + 1}).obj RH ≅ RJ)
    (hc : cc = proEtaleRingCompositeCoefficients g h RH RI RJ ch cg)
    (e : proEtaleRingModulePullback (g ≫ h) RH RJ cc ≅
      proEtaleRingModulePullback h RH RI ch ⋙ proEtaleRingModulePullback g RI RJ cg)
    (he : e = eqToIso (congrArg (fun c ↦
      proEtaleRingModulePullback (g ≫ h) RH RJ c) hc) ≪≫
        exchangeModuleComposition g h RH RI RJ ch cg)
    (M : proEtaleRingModules T RH) (U : T.ProEt) (x : M.val.obj (op U)) :
    (e.hom.app M).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))
      (((proEtaleRingModuleAdjunction (g ≫ h) RH RJ cc).unit.app M).val.app
          (op U) x) =
    ((proEtaleRingModulePullback g RI RJ cg).obj
      ((proEtaleRingModulePullback h RH RI ch).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
          (((proEtaleRingModuleAdjunction g RI RJ cg).unit.app
            ((proEtaleRingModulePullback h RH RI ch).obj M)).val.app
              (op ((proEtaleBaseChange h).obj U))
                (((proEtaleRingModuleAdjunction h RH RI ch).unit.app M).val.app (op U) x)) := by
  cases he
  exact exchangeComposition_transport_unit h g RH RI RJ ch cg cc hc M U x

attribute [local irreducible] tatePullbackComp

private theorem tatePullbackComp_unit {T T' T'' : Scheme.{u}} (h : T' ⟶ T)
    (g : T'' ⟶ T') (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)]
    (M : tateModules T R) (U : T.ProEt) (x : M.val.obj (op U)) :
    ((tatePullbackComp h g R).hom.app M).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))
      (((proEtaleRingModuleAdjunction (g ≫ h)
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T'' R)
        (asIso (proEtaleCoefficientInverseImageMap (g ≫ h) R))).unit.app M).val.app
          (op U) x) =
    ((proEtaleRingModulePullback g
        (proEtaleConstantRing T' R)
        (proEtaleConstantRing T'' R)
        (asIso (proEtaleCoefficientInverseImageMap g R))).obj
      ((proEtaleRingModulePullback h
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
          (((proEtaleRingModuleAdjunction g
        (proEtaleConstantRing T' R)
        (proEtaleConstantRing T'' R)
        (asIso (proEtaleCoefficientInverseImageMap g R))).unit.app
            ((proEtaleRingModulePullback h
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))).obj M)).val.app
              (op ((proEtaleBaseChange h).obj U))
                (((proEtaleRingModuleAdjunction h
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app
                  (op U) x)) := by
  exact exchangeComposition_identified_unit h g
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (proEtaleConstantRing T'' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))
        (asIso (proEtaleCoefficientInverseImageMap g R))
        (asIso (proEtaleCoefficientInverseImageMap (g ≫ h) R))
    (proEtaleConstantRingCompositeCoefficients_eq g h R).symm
    (tatePullbackComp h g R) (tatePullbackComp_eq h g R) M U x
private theorem tatePullbackComp_post_unit {T T' T'' : Scheme.{u}}
    (h : T' ⟶ T) (g : T'' ⟶ T') (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)]
    (M : tateModules T R) (M' : tateModules T' R) (M'' : tateModules T'' R)
    (ch : (tatePullback h R).obj M ⟶ M') (cg : (tatePullback g R).obj M' ⟶ M'')
    (U : T.ProEt) (x : M.val.obj (op U)) :
    (((tatePullbackComp h g R).hom.app M ≫ (tatePullback g R).map ch ≫ cg).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U))) (((proEtaleRingModuleAdjunction (g ≫ h)
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T'' R)
        (asIso (proEtaleCoefficientInverseImageMap (g ≫ h) R))).unit.app M).val.app (op U) x) =
    M''.val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
      (cg.val.app (op ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj U)))
        (((proEtaleRingModuleAdjunction g (proEtaleConstantRing T' R)
          (proEtaleConstantRing T'' R)
          (asIso (proEtaleCoefficientInverseImageMap g R))).unit.app M').val.app
            (op ((proEtaleBaseChange h).obj U))
          (ch.val.app (op ((proEtaleBaseChange h).obj U)) (((proEtaleRingModuleAdjunction h
            (proEtaleConstantRing T R)
            (proEtaleConstantRing T' R)
            (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x)))) := by
  let V := (proEtaleBaseChange h).obj U
  let W := (proEtaleBaseChange g).obj V
  let Wc := (proEtaleBaseChange (g ≫ h)).obj U
  let s := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U
  have hcR := tatePullbackComp_unit h g R M U x
  have hnR := PresheafOfModules.naturality_apply ((tatePullback g R).map ch).val s.op
    (tateUnit g R ((tatePullback h R).obj M) V (tateUnit h R M U x))
  have hngR := PresheafOfModules.naturality_apply cg.val s.op
    ((((tatePullback g R).map ch).val.app (op W))
      (tateUnit g R ((tatePullback h R).obj M) V (tateUnit h R M U x)))
  have huR := tateUnit_naturality g R ((tatePullback h R).obj M) M' ch V
    (tateUnit h R M U x)
  exact (congrArg (fun v ↦ cg.val.app (op Wc)
    ((((tatePullback g R).map ch).val.app (op Wc)) v)) hcR).trans
      ((congrArg (fun v ↦ cg.val.app (op Wc) v) hnR).trans
        (hngR.trans (congrArg (fun v ↦ M''.val.map s.op (cg.val.app (op W) v)) huR)))

/-- Identity law for the limit comparison, relative to the canonical identity identification.
Source: finite Kummer-level blueprint proof, final sentence
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the assumed identity law for β makes the coordinate projections of the two
maps equal. The uniqueness clause of the limit universal property proves equality.
This is the identity case of proof step 4. -/
theorem tateLimitMap_id (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F)
    (β : F ⋙ tatePullback (𝟙 T) (ULift.{u} (PadicInt l)) ≅ F)
    (hβ : ∀ r : ℕ, β.hom.app (op r) =
      (tatePullbackId T (ULift.{u} (PadicInt l))).hom.app (F.obj (op r))) :
    tateLimitMap (𝟙 T) _ F F β =
      (tatePullbackId T (ULift.{u} (PadicInt l))).hom.app (limit F) := by
  have hu := (tateInverseLimitBaseChange l (𝟙 T) F F hF hF β).2
  symm
  apply hu
  intro r
  rw [hβ r]
  exact ((tatePullbackId T (ULift.{u} (PadicInt l))).hom.naturality
    (limit.π F (op r))).symm

/-- Composition law for the limit comparison with the canonical inverse-image compositor.
Source: finite Kummer-level blueprint proof, final sentence
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: compose each side with p_r. Naturality of the compositor, the defining equations
for c_h and c_g, and the assumed composition law for β give the same coordinate map.
Joint monicity of the projections proves equality. This is proof step 4. -/
theorem tateLimitMap_comp (l : ℕ) [Fact l.Prime]
    {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap g (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (F'' : ℕᵒᵖ ⥤ tateModules T'' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F') (hF'' : TateTowerKilled l F'')
    (βh : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F')
    (βg : F' ⋙ tatePullback g (ULift.{u} (PadicInt l)) ≅ F'')
    (βgh : F ⋙ tatePullback (g ≫ h) (ULift.{u} (PadicInt l)) ≅ F'')
    (hβ : ∀ r : ℕ, βgh.hom.app (op r) =
      (tatePullbackComp h g (ULift.{u} (PadicInt l))).hom.app (F.obj (op r)) ≫
        (tatePullback g _).map (βh.hom.app (op r)) ≫ βg.hom.app (op r)) :
    tateLimitMap (g ≫ h) _ F F'' βgh =
      (tatePullbackComp h g (ULift.{u} (PadicInt l))).hom.app (limit F) ≫
        (tatePullback g _).map (tateLimitMap h _ F F' βh) ≫
          tateLimitMap g _ F' F'' βg := by
  apply limit.hom_ext
  intro j
  rcases j with ⟨r⟩
  rw [(tateInverseLimitBaseChange l (g ≫ h) F F'' hF hF'' βgh).1 r]
  rw [Category.assoc, Category.assoc,
    (tateInverseLimitBaseChange l g F' F'' hF' hF'' βg).1 r]
  rw [← (tatePullback g _).map_comp_assoc,
    (tateInverseLimitBaseChange l h F F' hF hF' βh).1 r,
    (tatePullback g _).map_comp]
  rw [hβ r]
  have hn := (tatePullbackComp h g (ULift.{u} (PadicInt l))).hom.naturality
    (limit.π F (op r))
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (fun k ↦ k ≫ (tatePullback g _).map (βh.hom.app (op r)) ≫
      βg.hom.app (op r)) hn

/-- Tensoring preserves the canonical identity law, in particular for b_id.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply the pure-tensor normalization of the tensor comparison and the
unit-normalized identity comparison. Both sides act identically on the pulled back
pure tensors; these locally generate the source. This is the identity case of step 7. -/
theorem tateTensorMap_id (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) A)] (M : tateModules T R) :
    tateTensorMap (𝟙 T) φ M M ((tatePullbackId T R).hom.app M) =
      (tatePullbackId T A).hom.app (tateTensor T φ M) := by
  apply (tateTensorMap_existsUnique (𝟙 T) φ M M
    ((tatePullbackId T R).hom.app M)).unique
  · exact tensorMap_apply (𝟙 T) φ M M ((tatePullbackId T R).hom.app M)
  · intro U a x
    have hA : IsTatePullbackId T A (tatePullbackId T A) :=
      pullbackId_normalized T A
    have hR : IsTatePullbackId T R (tatePullbackId T R) :=
      pullbackId_normalized T R
    erw [hA (tateTensor T φ M) U (tateTmul φ M U a x), hR M U x]
    have hr : tateRingUnit (𝟙 T) A U a =
        (proEtaleConstantRing T A).obj.map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op a := by
      unfold tateRingUnit
      rw [tateRingUnit_id]
      rfl
    rw [hr]
    exact tateTmul_map φ M _ a x

private theorem ringUnit_one {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] (U : T.ProEt) : tateRingUnit h A U 1 = 1 :=
  map_one ((proEtaleCoefficientDirectImageMap h A).hom.app (op U)).hom

private theorem tensorMap_one {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') (U : T.ProEt) (x : M.val.obj (op U)) :
    (tateTensorMap h φ M M' c).val.app (op ((proEtaleBaseChange h).obj U))
      (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T A)
        (proEtaleConstantRing T' A)
        (asIso (proEtaleCoefficientInverseImageMap h A))).unit.app
      (tateTensor T φ M)).val.app (op U) (tateTmul φ M U 1 x)) =
    tateTmul φ M' ((proEtaleBaseChange h).obj U) 1
      (c.val.app (op ((proEtaleBaseChange h).obj U)) (((proEtaleRingModuleAdjunction h
        (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x)) := by
  exact (tensorMap_apply h φ M M' c U 1 x).trans
    (congrArg (fun a ↦ tateTmul φ M' ((proEtaleBaseChange h).obj U) a
      (c.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x)))
        (ringUnit_one h A U))

private theorem tensorMap_one_post {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') (U : T.ProEt) (x : M.val.obj (op U))
    (y : M'.val.obj (op ((proEtaleBaseChange h).obj U)))
    (hc : c.val.app (op ((proEtaleBaseChange h).obj U))
      (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R)
        (proEtaleConstantRing T' R)
        (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x) = y) :
    (tateTensorMap h φ M M' c).val.app (op ((proEtaleBaseChange h).obj U))
      (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T A)
        (proEtaleConstantRing T' A)
        (asIso (proEtaleCoefficientInverseImageMap h A))).unit.app
          (tateTensor T φ M)).val.app (op U) (tateTmul φ M U 1 x)) =
    tateTmul φ M' ((proEtaleBaseChange h).obj U) 1 y := by
  exact (tensorMap_one h φ M M' c U x).trans
    (congrArg (tateTmul φ M' ((proEtaleBaseChange h).obj U) 1) hc)

private theorem tensorComp_right_unit {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    [IsIso (proEtaleCoefficientInverseImageMap g A)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) A)]
    (M : tateModules T R) (M' : tateModules T' R) (M'' : tateModules T'' R)
    (ch : (tatePullback h R).obj M ⟶ M') (cg : (tatePullback g R).obj M' ⟶ M'')
    (U : T.ProEt) (x : M.val.obj (op U)) :
    (((tatePullbackComp h g A).hom.app (tateTensor T φ M) ≫
      (tatePullback g A).map (tateTensorMap h φ M M' ch) ≫
        tateTensorMap g φ M' M'' cg).val.app
      (op ((proEtaleBaseChange (g ≫ h)).obj U)))
      (((proEtaleRingModuleAdjunction (g ≫ h) (proEtaleConstantRing T A)
        (proEtaleConstantRing T'' A)
        (asIso (proEtaleCoefficientInverseImageMap (g ≫ h) A))).unit.app
          (tateTensor T φ M)).val.app (op U) (tateTmul φ M U 1 x)) =
    tateTmul φ M'' ((proEtaleBaseChange (g ≫ h)).obj U) 1
      (M''.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U).op
        (cg.val.app (op ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj U)))
          (((proEtaleRingModuleAdjunction g (proEtaleConstantRing T' R)
            (proEtaleConstantRing T'' R)
            (asIso (proEtaleCoefficientInverseImageMap g R))).unit.app M').val.app
              (op ((proEtaleBaseChange h).obj U))
            (ch.val.app (op ((proEtaleBaseChange h).obj U)) (((proEtaleRingModuleAdjunction h
              (proEtaleConstantRing T R)
              (proEtaleConstantRing T' R)
              (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U)
                x))))) := by
  let V := (proEtaleBaseChange h).obj U
  let W := (proEtaleBaseChange g).obj V
  let Wc := (proEtaleBaseChange (g ≫ h)).obj U
  let s := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U
  let bh := tateTensorMap h φ M M' ch
  let bg := tateTensorMap g φ M' M'' cg
  have hr := tatePullbackComp_post_unit h g A
    (tateTensor T φ M) (tateTensor T' φ M') (tateTensor T'' φ M'') bh bg
    U (tateTmul φ M U 1 x)
  have hh := tensorMap_one h φ M M' ch U x
  have hg := tensorMap_one g φ M' M'' cg V
    (ch.val.app (op V) (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R)
              (proEtaleConstantRing T' R)
              (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x))
  have ht := (congrArg (fun v ↦ bg.val.app (op W)
    (tateUnit g A (tateTensor T' φ M') V v)) hh).trans hg
  have hr' := hr.trans (congrArg ((tateTensor T'' φ M'').val.map s.op) ht)
  have hmap := tateTmul_map φ M'' s 1
    (cg.val.app (op W) (tateUnit g R M' V
      (ch.val.app (op V) (((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R)
              (proEtaleConstantRing T' R)
              (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x))))
  simp only [map_one] at hmap
  have hr'' := hr'.trans hmap
  exact hr''

/-- Tensoring preserves the canonical composition law, in particular for b_h and b_g.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the compositor's conjugate is fibre-product pasting, so by the unit equations of
the normalized adjunctions it carries a pulled back pure tensor to the iterated one.
Apply the pure-tensor formula for
the two tensor maps. Both sides apply c_h, then c_g, to the first factor, and preserve
the coefficient factor. Constant-section maps compose by the same normalization.
Local generation gives equality. With step 4 this is proof step 7 for the b maps. -/
theorem tateTensorMap_comp {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    [IsIso (proEtaleCoefficientInverseImageMap g A)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) A)]
    (M : tateModules T R) (M' : tateModules T' R) (M'' : tateModules T'' R)
    (ch : (tatePullback h R).obj M ⟶ M') (cg : (tatePullback g R).obj M' ⟶ M'') :
    tateTensorMap (g ≫ h) φ M M''
        ((tatePullbackComp h g R).hom.app M ≫ (tatePullback g R).map ch ≫ cg) =
      (tatePullbackComp h g A).hom.app (tateTensor T φ M) ≫
        (tatePullback g A).map (tateTensorMap h φ M M' ch) ≫
          tateTensorMap g φ M' M'' cg := by
  apply tensorPullback_unit_ext_raw (g ≫ h) φ M (tateTensor T'' φ M'')
  intro U x
  have hc := tatePullbackComp_post_unit h g R M M' M'' ch cg U x
  have hl := tensorMap_one_post (g ≫ h) φ M M''
    ((tatePullbackComp h g R).hom.app M ≫ (tatePullback g R).map ch ≫ cg) U x _ hc
  exact hl.trans (tensorComp_right_unit h g φ M M' M'' ch cg U x).symm

/-- Every killed Z_l-algebra has its unique finite quotient action, with no extra data.
Source: Stacks Tag 03EK; PadicInt.toZModPow and its kernel
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the kernel of reduction to Z/l^N is the ideal generated by l^N.
The given algebra map kills this ideal because l^N is zero in A. Factor through
the quotient and its standard identification with Z/l^N. Surjectivity of reduction
gives uniqueness. Universe lifts transport this unique map without changing it. -/
theorem tateFiniteAlgebraMap_existsUnique (l n : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0) :
    ∃! a : ULift.{u} (ZMod (l ^ (n + 1))) →+* A,
      a.comp (tatePadicReduction l n) =
        (algebraMap (PadicInt l) A).comp ULift.ringEquiv.toRingHom := by
  let q : PadicInt l →+* ZMod (l ^ (n + 1)) := PadicInt.toZModPow (n + 1)
  have hq : Function.Surjective q := ZMod.ringHom_surjective q
  have hk : RingHom.ker q ≤ RingHom.ker (algebraMap (PadicInt l) A) := by
    rw [PadicInt.ker_toZModPow]
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simpa using hA
  let b := q.liftOfSurjective hq ⟨algebraMap (PadicInt l) A, hk⟩
  refine ⟨b.comp ULift.ringEquiv.toRingHom, ?_, ?_⟩
  · ext x
    exact q.liftOfSurjective_comp_apply hq
      ⟨algebraMap (PadicInt l) A, hk⟩ x.down
  · intro a ha
    apply RingHom.ext
    intro x
    obtain ⟨y, hy⟩ := hq x.down
    have he := DFunLike.congr_fun ha (ULift.up y)
    change a (ULift.up (q y)) = algebraMap (PadicInt l) A y at he
    change a x = b x.down
    rw [← hy, q.liftOfSurjective_comp_apply]
    simpa only [hy, ULift.up_down] using he

/-- The canonical finite scalar action of Z/l^N on the killed algebra A.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteAlgebraMap (l n : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0) : ULift.{u} (ZMod (l ^ (n + 1))) →+* A :=
  (tateFiniteAlgebraMap_existsUnique l n A hA).exists.choose

/-- The actual α_S, with the canonical quotient actions and the coordinate projection p_N.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EK
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTowerReduction (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    tateTensor T ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
        (limit F) ⟶
      tateTensor T (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F hF) :=
  tateReduction (tatePadicReduction l n) (tateFiniteAlgebraMap l n A hA)
    (limit F) (F.obj (op n)) (tateFiniteModule l n F hF) (tateFiniteModuleIso l n F hF)
    (limit.π F (op n))

/-- The canonical finite tensor square, with no quotient presentations assumed as data.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply the finite tensor square above to the quotient actions uniquely fixed
by tateFinitePresentation_exists and tateFiniteAlgebraMap_existsUnique. Its pure-tensor
equations are exactly α_S(x ⊗ a) = p_N(x) ⊗ a and d_h = β_N ⊗ 1. The limit
projection equation proves the commuting square. Tensor β_N inverse to invert d_h;
if α_T and α_T' are invertible, solve the square for b_h to obtain an isomorphism.
These are proof steps 5--6 and 8. Identity and composition for b_h follow from
steps 4 and 7, stated as tateLimitMap_id/comp and tateTensorMap_id/comp. -/
theorem tateInverseLimitCanonicalFiniteTensorBaseChange (l n : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (ZMod (l ^ (n + 1)))))]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F') :
    ∃ d : (tatePullback h A).obj
        (tateTensor T (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F hF)) ⟶
      tateTensor T' (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F' hF'),
      IsTateFiniteTensorMap h (tatePadicReduction l n) (tateFiniteAlgebraMap l n A hA)
        (F.obj (op n)) (F'.obj (op n))
        (tateFiniteModule l n F hF) (tateFiniteModule l n F' hF')
        (tateFiniteModuleIso l n F hF) (tateFiniteModuleIso l n F' hF')
        (β.app (op n)) d ∧ IsIso d ∧
      tateTensorMap h ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
          (limit F) (limit F') (tateLimitMap h _ F F' β) ≫
          tateTowerReduction l n A hA F' hF' =
        (tatePullback h A).map (tateTowerReduction l n A hA F hF) ≫ d ∧
      (IsIso (tateTowerReduction l n A hA F hF) →
        IsIso (tateTowerReduction l n A hA F' hF') →
        IsIso (tateTensorMap h
          ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
          (limit F) (limit F') (tateLimitMap h _ F F' β))) := by
  exact tateInverseLimitFiniteTensorBaseChange l n h A hA
    (tateFiniteAlgebraMap l n A hA)
    (tateFiniteAlgebraMap_existsUnique l n A hA).exists.choose_spec
    F F' hF hF' β (tateFiniteModule l n F hF) (tateFiniteModule l n F' hF')
    (tateFiniteModuleIso l n F hF) (tateFiniteModuleIso l n F' hF')

end AlgebraicGeometry.Scheme
