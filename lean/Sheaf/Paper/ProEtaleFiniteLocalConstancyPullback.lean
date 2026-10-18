/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Finite local constancy under inverse image

Source: Stacks Project, Modules on Sites, Tag 093R;
Etale Cohomology, Tag 095I (common stratifications).
(blueprint: lem-pur-proetale-finite-local-constancy-pullback).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A constant module presheaf is left adjoint to evaluation at a terminal object.
Source: the constant-sheaf universal property, Stacks Tag 0H7J. -/
private noncomputable def constantPresheafHomEquiv (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (F : PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    (proEtaleConstantModulePresheaf Y.ProEt A M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          change (a.unop ≫ hT.from U.unop).op = _
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl
/-- The same universal property after simultaneous ring and module sheafification.
Source: Stacks Tag 0H7J and the module sheafification adjunction. -/
private noncomputable def constantModuleHomEquiv (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} A))))) :
    (proEtaleConstantModuleSheaf Y A M ⟶ F) ≃
      (M ⟶ ((PresheafOfModules.restrictScalars
        (Functor.whiskerRight (toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj F.val).obj (op T)) := by
  haveI := (proEtaleConstantRingUnit_locallyBijective Y A).1
  haveI := (proEtaleConstantRingUnit_locallyBijective Y A).2
  exact (PresheafOfModules.sheafificationHomEquiv (F := F)
    (P := proEtaleConstantModulePresheaf Y.ProEt A M)
    (Functor.whiskerRight (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).trans (constantPresheafHomEquiv Y A T hT M _)


private noncomputable def constantPF (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤ PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  obj M := proEtaleConstantModulePresheaf Y.ProEt A M
  map f := { app _ := f, naturality := by intros; ext x; rfl }
  map_id _ := by apply PresheafOfModules.hom_ext; intro U; rfl
  map_comp _ _ := by apply PresheafOfModules.hom_ext; intro U; rfl

private noncomputable def constantPFAdj (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T) :
    constantPF Y A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv Y A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private noncomputable def ringUnit (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  Functor.whiskerRight (toSheafify (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private noncomputable def constantMF (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A) :=
  haveI : Presheaf.IsLocallyInjective (ProEt.topology Y) (ringUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).1
  haveI : Presheaf.IsLocallySurjective (ProEt.topology Y) (ringUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).2
  constantPF Y A ⋙ PresheafOfModules.sheafification.{u + 1} (ringUnit Y A)

private noncomputable def constantGlobal (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (ringUnit Y A) ⋙
    PresheafOfModules.evaluation _ (op T)

private noncomputable def constantMFAdj (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T) : constantMF Y A ⊣ constantGlobal Y A T := by
  haveI : Presheaf.IsLocallyInjective (ProEt.topology Y) (ringUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).1
  haveI : Presheaf.IsLocallySurjective (ProEt.topology Y) (ringUnit Y A) :=
    (proEtaleConstantRingUnit_locallyBijective Y A).2
  exact (constantPFAdj Y A T hT).comp (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A))
    (ringUnit Y A))
theorem proEtaleConstantModulePullback_rho_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

theorem proEtaleConstantModulePullback_ring_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        proEtaleCoefficientDirectImageMap f A := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap f A)

private noncomputable def constAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] : proEtaleConstantModulePullbackFunctor f A ⊣
      proEtaleConstantModuleDirectImage f A := by
  have := constantComparison_isIso f A
  let adj := proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A)
    (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap f A))
  change proEtaleConstantModulePullbackFunctor f A ⊣ _ at adj
  dsimp only [proEtaleRingModuleDirectImage] at adj
  rw [proEtaleConstantModulePullback_ring_direct] at adj
  exact adj
private noncomputable def globalDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (T : Y.ProEt) :
    proEtaleConstantModuleDirectImage f A ⋙ constantGlobal Y A T ≅
      constantGlobal X A ((proEtaleBaseChange f).obj T) :=
  NatIso.ofComponents (fun N ↦ by
    let e : (constantGlobal Y A T).obj
        ((proEtaleConstantModuleDirectImage f A).obj N) ≃ₗ[ULift.{u + 1} A]
          (constantGlobal X A ((proEtaleBaseChange f).obj T)).obj N :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a n
          let B := (proEtaleConstantRing X A).obj.obj
            (op ((proEtaleBaseChange f).obj T))
          let z : N.val.obj (op ((proEtaleBaseChange f).obj T)) := n
          let s : B := (proEtaleCoefficientDirectImageMap f A).hom.app (op T)
            ((toSheafify (ProEt.topology Y)
              ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
                (op T) a)
          let t : B := (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
              (op ((proEtaleBaseChange f).obj T)) a
          change s • z = t • z
          have h : s = t := congrArg (fun h ↦ h a)
            (proEtaleConstantModulePullback_rho_unit f A (op T))
          exact congrArg (fun c : B ↦ c • z) h }
    exact e.toModuleIso)
    (by intros; ext x; rfl)

/-- Pullback preserves the actual constant module construction and scalar action.
Source: Stacks Tags 0H7J and 03D2, via the canonical module adjunction. -/
private noncomputable def constantModulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (T : Y.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} A)) :
    proEtaleConstantModulePullback f A (proEtaleConstantModuleSheaf Y A M) ≅
      proEtaleConstantModuleSheaf X A M := by
  let ac := ((constantMFAdj Y A T hT).comp (constAdj f A)).ofNatIsoRight
    (globalDirectIso f A T)
  let ax := constantMFAdj X A ((proEtaleBaseChange f).obj T)
    (hT.isTerminalObj (proEtaleBaseChange f) T)
  exact (ac.leftAdjointUniq ax).app M

/-- Inverse image preserves finite local constancy of a module sheaf.

Source: Stacks Project, Modules on Sites, Tag 093R,
lemma-pullback-locally-constant, applied to pro-etale module inverse image.
(blueprint: lem-pur-proetale-finite-local-constancy-pullback).

Proof: pull a trivializing cover on Y back along b. Base change preserves its
covering property. The helper constantModuleHomEquiv proves the constant-module
universal property from constant presheaf evaluation and module sheafification.
The helper constantModulePullbackIso proves preservation of these constant models:
compose their actual adjunction with the inverse-image adjunction. The proved
coefficient-unit formula identifies terminal sections with their scalar actions,
and uniqueness of left adjoints supplies the module isomorphism. Equivalently, the inverse image
of a constant module sheaf is the constant
module sheaf with the same value: inverse image preserves coproducts and the
terminal sheaf, hence constant set sheaves, and preserves their addition and scalar
action. For a geometric point of X, compose with b;
the stalk inverse-image formula identifies the new stalk with the stalk on Y
at the composite geometric point. Hence it is finite. Empty schemes and empty
cover members require no geometric points. -/
theorem proEtale_finiteLocalConstancy_pullback
    {Y X : Scheme.{u}} (b : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)) :
    IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback b A F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback b A F)) := by
  sorry

end AlgebraicGeometry.Scheme
