/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
import Mathlib.CategoryTheory.Whiskering

/-!
# Stratum pullback and scalar-extension comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md,
  proof paragraph (2), expanded constant-module pullback and stratum tensor comparison
(blueprint: lem-sp-stratum-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The map of constant coefficient rings induced by a unital map of rings.
Source: the coefficient comparison in the scalar-extension proof (blueprint:
`lem-sp-stratum-scalar-extension`). -/
noncomputable def proEtaleConstantRingMap {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift α))

/-- The constant section represented by an element of the module, using the actual
simultaneous module sheafification unit.
Source: scalar-extension proof paragraph (2), constant module operations
(blueprint: lem-sp-stratum-scalar-extension). -/
noncomputable def stratumConstantModuleSection (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (U : T.ProEtᵒᵖ) (m : M) :
    (proEtaleConstantModuleSheaf T A M).val.obj U :=
  (CategoryTheory.toSheafify (ProEt.topology T)
    (proEtaleConstantModulePresheaf T.ProEt A M).presheaf).app U m

/-- The local unit `m ↦ 1 ⊗ m` of scalar extension, followed by sheafification.
Source: scalar-extension proof paragraph (2), termwise tensor comparison
(blueprint: lem-sp-stratum-scalar-extension). -/
noncomputable def stratumScalarExtensionUnitSection {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B)
    (N : proEtaleRingModules T (proEtaleConstantRing T A)) (U : T.ProEtᵒᵖ)
    (m : N.val.obj U) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (proEtaleConstantRingMap (T := T) α) N).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B))
      (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) α) N)).app U)
          ((1 : (proEtaleConstantRing T B).obj.obj U) ⊗ₜ[_,
            ((proEtaleConstantRingMap (T := T) α).hom.app U).hom] m)


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
private theorem stratum_rho_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
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

private theorem stratum_ring_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        proEtaleCoefficientDirectImageMap f A := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap f A)

private noncomputable def globalDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (T : Y.ProEt) :
    proEtaleConstantRingPushforward A f ⋙ constantGlobal Y A T ≅
      constantGlobal X A ((proEtaleBaseChange f).obj T) :=
  NatIso.ofComponents (fun N ↦ by
    let e : (constantGlobal Y A T).obj
        ((proEtaleConstantRingPushforward A f).obj N) ≃ₗ[ULift.{u + 1} A]
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
          change (proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
            (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).hom.app (op T)
              ((toSheafify (ProEt.topology Y)
                ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
                  (op T) a) • z = t • z
          rw [show proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
            (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
              proEtaleCoefficientDirectImageMap f A from stratum_ring_direct f A]
          change s • z = t • z
          have h : s = t := congrArg (fun h ↦ h a)
            (stratum_rho_unit f A (op T))
          exact congrArg (fun c : B ↦ c • z) h }
    exact e.toModuleIso)
    (by intros; ext x; rfl)


section ScalarComparison

variable (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)

private noncomputable def scalarPresheafFunctor :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      PresheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (proEtaleConstantRing X B)).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (proEtaleConstantRingMap (T := X) α)
  map a :=
    { app := fun U ↦ (ModuleCat.extendScalars
        ((proEtaleConstantRingMap (T := X) α).hom.app U).hom).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ _ a }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp a b := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private noncomputable def scalarFunctor :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X B) :=
  scalarPresheafFunctor X α ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (proEtaleConstantRing X B)).obj)

private noncomputable def scalarAdjunction :
    scalarFunctor X α ⊣ proEtaleCoefficientRestrictScalars X α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α)
      homEquiv_naturality_left_symm := by
        intro M M' N k h
        apply (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N).injective
        change (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N)
          ((SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N).symm
            (k ≫ h)) =
          (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N)
            (SheafOfModules.changeOfRingsHom (proEtaleConstantRingMap (T := X) α) M k ≫
              (SheafOfModules.changeHomEquiv
                (proEtaleConstantRingMap (T := X) α) M' N).symm h)
        exact (Equiv.apply_symm_apply _ _).trans
          ((SheafOfModules.changeHomEquiv_naturality_left
            (proEtaleConstantRingMap (T := X) α) M M' N k
            ((SheafOfModules.changeHomEquiv
              (proEtaleConstantRingMap (T := X) α) M' N).symm h)).trans
                (congrArg (fun z ↦ k ≫ z) (Equiv.apply_symm_apply _ _))).symm
      homEquiv_naturality_right := fun h k ↦
        SheafOfModules.changeHomEquiv_naturality_right _ _ _ _ k h }

private theorem scalarAdjunction_apply
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (N : proEtaleRingModules X (proEtaleConstantRing X B))
    (h : (scalarFunctor X α).obj M ⟶ N) (U : X.ProEtᵒᵖ) (m : M.val.obj U) :
    (((scalarAdjunction X α).homEquiv M N) h).val.app U m =
      h.val.app U (stratumScalarExtensionUnitSection α M U m) := by
  rw [scalarAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl


section
variable {T S : Scheme.{u}} (i : S ⟶ T) (A B : Type u)
  [CommRing A] [CommRing B] [Finite A] [Finite B] (α : A →+* B)

private theorem coefficient_direct (X₀ : Scheme.{u}) (X₁ : Scheme.{u})
    (f : X₀ ⟶ X₁) (R : Type u) [CommRing R] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing X₁ R) (proEtaleConstantRing X₀ R)
      (proEtaleConstantRingComparison f R) = proEtaleCoefficientDirectImageMap f R := by
  exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private noncomputable def directImageIso (R : Type u) [CommRing R] :
    proEtaleConstantRingPushforward R i ≅ proEtaleConstantModuleDirectImage i R :=
  SheafOfModules.pushforwardCongr (by rw [coefficient_direct])

/-- Pullback commutes with underived scalar extension, naturally and on tensor units.
Source: the fourth step of stratum scalar extension, Stacks Tags 03D2 and 03EL.
(blueprint: lem-sp-stratum-scalar-extension)

Proof: identify the inverse-image constant rings by their canonical comparisons.
For a map A to B the coefficient square commutes: its adjoint sends each constant
scalar a to the same scalar alpha(a). Module pullback followed by change of rings
and change of rings followed by module pullback are therefore left adjoints to
canonically isomorphic right functors. The right-functor isomorphism is identity
on sections and is linear by the coefficient square. Uniqueness of left adjoints
gives the family beta and naturality. The unit equation for that uniqueness
isomorphism, and the change-of-rings Hom correspondence evaluated at 1 tensor m,
give exactly the displayed normalization on every base-change object. No flatness
of B over A or immersion hypothesis is used. -/
private theorem stratumScalarExtensionModuleComparison :
    (∃ β : ∀ N : proEtaleRingModules T (proEtaleConstantRing T A),
        proEtaleConstantModulePullback i B
          (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
            (proEtaleConstantRingMap (T := T) α) N) ≅
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) (proEtaleConstantModulePullback i A N),
      (∀ (N N' : proEtaleRingModules T (proEtaleConstantRing T A)) (f : N ⟶ N'),
        proEtaleConstantModulePullbackMap i B
            (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
              (proEtaleConstantRingMap (T := T) α) N f) ≫
          (β N').hom =
        (β N).hom ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) _ (proEtaleConstantModulePullbackMap i A f)) ∧
      (∀ (N : proEtaleRingModules T (proEtaleConstantRing T A))
          (U : T.ProEtᵒᵖ) (m : N.val.obj U),
        (((proEtaleConstantRingAdjunction B i).homEquiv _ _ (β N).hom).val.app U)
            (stratumScalarExtensionUnitSection α N U m) =
          stratumScalarExtensionUnitSection α (proEtaleConstantModulePullback i A N)
            ((proEtaleBaseChange i).op.obj U)
            (((proEtaleConstantRingAdjunction A i).unit.app N).val.app U m))) := by
  obtain ⟨d₀, hd, _⟩ := proEtaleCoefficientDirectImageComparison_existsUnique i α
  let d := Functor.isoWhiskerRight (directImageIso i B) (proEtaleCoefficientRestrictScalars T α) ≪≫
    d₀ ≪≫ Functor.isoWhiskerLeft (proEtaleCoefficientRestrictScalars S α) (directImageIso i A).symm
  let a := ((scalarAdjunction T α).comp (proEtaleConstantRingAdjunction B i)).ofNatIsoRight d
  let b := (proEtaleConstantRingAdjunction A i).comp (scalarAdjunction S α)
  let e := a.leftAdjointUniq b
  refine ⟨fun N ↦ e.app N, ?_, ?_⟩
  · intro N N' f
    exact e.hom.naturality f
  · intro N U m
    have he := a.homEquiv_leftAdjointUniq_hom_app b N
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply] at he
    have hx := congrArg (fun h ↦ h.val.app U m) he
    change (d.hom.app _).val.app U
      (((scalarAdjunction T α).homEquiv N _
        ((proEtaleConstantRingAdjunction B i).homEquiv _ _ (e.app N).hom)).val.app U m) = _ at hx
    have hdi (Q : proEtaleRingModules S (proEtaleConstantRing S B))
        (z : Q.val.obj ((proEtaleBaseChange i).op.obj U)) :
        (d.hom.app Q).val.app U z = z := by
      change (d₀.hom.app Q).val.app U z = z
      exact hd Q U z
    rw [hdi] at hx
    rw [scalarAdjunction_apply] at hx
    exact hx

end
end ScalarComparison

set_option maxHeartbeats 600000 in
-- The composite adjunction and dependent module transports require extra elaboration steps.
/-- Pullback of a finite constant module, scalar extension, K-flatness and cohomology
commute with an immersed stratum.  The proof follows the six steps in the blueprint
proof. First identify the coefficient ring via the constant-section comparison and
use exactness of coefficient pullback. Second, the constant-sheaf/global-sections
adjunction and uniqueness of left adjoints identify inverse image of constant sets,
with adjunct sending each constant section to itself. Third, naturality at addition,
negation, zero and the action, together with finite-product preservation, makes this
an isomorphism of module sheaves; the displayed adjunct equation fixes this canonical
isomorphism. Fourth, ringed-topos module tensor pullback, followed by the constant-B
comparison, gives the B-linear family β. On units it sends the pullback of `1 ⊗ m` to
`1 ⊗` the pullback unit of m, as displayed. Naturality in a module map gives the stated
square; apply it to every differential to get the displayed family of complex
isomorphisms with components β. Applied to each component of any cochain map the same square gives
naturality of this complex comparison. Fifth, ringed-topos K-flat pullback preserves
K-flatness and flat terms under the two hypotheses. Sixth, exact functor cohomology
identifies every cohomology object with pullback of the original cohomology object.
The cited dependency nodes provide the inverse-image, locally constant,
K-flat, flatness, tensor, and cohomology notions used here.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md,
  proof paragraph (2) (blueprint: lem-sp-stratum-scalar-extension). -/
theorem stratumScalarExtension
    {T S : Scheme.{u}} (i : S ⟶ T) [IsImmersion i]
    (hi : Topology.IsConstructible (Set.range i)) (A B : Type u)
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (α : A →+* B)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) [Finite M]
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat P)
    (hflat : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T)
        (R := proEtaleConstantRing T A) (P.X n))
    (K : DerivedCategory (proEtaleRingModules T (proEtaleConstantRing T A)))
    (hK : ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheaf S A
        (proEtaleConstantModulePullback i A
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing S A)
          (proEtaleConstantModulePullback i A
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))))) :
    IsIso (proEtaleCoefficientInverseImageMap i A) ∧
    (∃ e : proEtaleConstantModulePullback i A
        (proEtaleConstantModuleSheaf T A M) ≅ proEtaleConstantModuleSheaf S A M,
      ∀ (U : T.ProEtᵒᵖ) (m : M),
        (((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val.app U)
          (stratumConstantModuleSection T A M U m) =
        stratumConstantModuleSection S A M ((proEtaleBaseChange i).op.obj U) m) ∧
    CochainComplex.IsAcyclicTensorKFlat
      (((proEtaleConstantRingPullback A i).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ∧
    (∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology S)
        (R := proEtaleConstantRing S A)
        (HomologicalComplex.X (((proEtaleConstantRingPullback A i).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) n)) ∧
    (∃ β : ∀ N : proEtaleRingModules T (proEtaleConstantRing T A),
        proEtaleConstantModulePullback i B
          (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
            (proEtaleConstantRingMap (T := T) α) N) ≅
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) (proEtaleConstantModulePullback i A N),
      (∀ (N N' : proEtaleRingModules T (proEtaleConstantRing T A)) (f : N ⟶ N'),
        proEtaleConstantModulePullbackMap i B
            (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
              (proEtaleConstantRingMap (T := T) α) N f) ≫
          (β N').hom =
        (β N).hom ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) _ (proEtaleConstantModulePullbackMap i A f)) ∧
      (∀ (N : proEtaleRingModules T (proEtaleConstantRing T A))
          (U : T.ProEtᵒᵖ) (m : N.val.obj U),
        (((proEtaleConstantRingAdjunction B i).homEquiv _ _ (β N).hom).val.app U)
            (stratumScalarExtensionUnitSection α N U m) =
          stratumScalarExtensionUnitSection α (proEtaleConstantModulePullback i A N)
            ((proEtaleBaseChange i).op.obj U)
            (((proEtaleConstantRingAdjunction A i).unit.app N).val.app U m)) ∧
      (∃ e : ∀ Q : CochainComplex
          (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
          ((proEtaleConstantRingPullback B i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (SheafOfModules.changeOfRingsComplex.{u + 1, u}
              (proEtaleConstantRingMap (T := T) α) Q) ≅
          SheafOfModules.changeOfRingsComplex.{u + 1, u} (proEtaleConstantRingMap (T := S) α)
            (((proEtaleConstantRingPullback A i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q),
        ∀ (Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
          (n : ℤ), (e Q).hom.f n = (β (Q.X n)).hom)) ∧
    (∀ q : ℤ, Nonempty (
      (DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S A)) q).obj
        ((proEtaleConstantRingDerivedPullback A i).obj K) ≅
      (proEtaleConstantRingPullback A i).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))) := by
  have _ := hi
  have _ := hK
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists i (proEtaleConstantRing T A)
  have : PreservesFiniteLimits (proEtaleSheafInverseImage i (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage i (𝟙 T)).2.2.2.1
  let C := proEtaleRingModules T (proEtaleConstantRing T A)
  let D := proEtaleRingModules S
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (proEtaleConstantRing T A))
  let c := proEtaleCoefficientInverseImageMap i A
  have hmap' (F : C ⥤ D) (h : I.modules = F) {N N' : C} (f : N ⟶ N') :
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c (F.obj N) (F.map f) =
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj N)) h.symm) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          c (I.modules.obj N) (I.modules.map f) ≫
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj N')) h.symm).symm := by
    subst F
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hpull := SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage i (Type (u + 1)))
    (proEtaleSheafDirectImage i (Type (u + 1)))
    (proEtaleSheafAdjunction i (Type (u + 1))) I
    (proEtaleCoefficientInverseImageMap i A) (proEtaleConstantRingPullback A i)
    (by
      intro N
      exact congrArg (fun F :
          proEtaleRingModules T (proEtaleConstantRing T A) ⥤
            proEtaleRingModules S
              ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
                (proEtaleConstantRing T A)) ↦
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (proEtaleCoefficientInverseImageMap i A) (F.obj N)) hI.symm)
    (by
      intro N N' f
      exact hmap' _ hI f) P hP hflat
  refine ⟨inferInstance, ?_, hpull.1, hpull.2, ?_, ?_⟩
  · let Z := ⊤_ T.ProEt
    let hZ : IsTerminal Z := terminalIsTerminal
    let ac := ((constantMFAdj T A Z hZ).comp (proEtaleConstantRingAdjunction A i)).ofNatIsoRight
      (globalDirectIso i A Z)
    let ax := constantMFAdj S A ((proEtaleBaseChange i).obj Z)
      (hZ.isTerminalObj (proEtaleBaseChange i) Z)
    let e := (ac.leftAdjointUniq ax).app M
    refine ⟨e, ?_⟩
    have he := ac.homEquiv_leftAdjointUniq_hom_app ax M
    simp only [ac, Adjunction.homEquiv_ofNatIsoRight_apply] at he
    have h0 (m : M) :
        (((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val.app (op Z))
          (stratumConstantModuleSection T A M (op Z) m) =
        stratumConstantModuleSection S A M (op ((proEtaleBaseChange i).obj Z)) m := by
      exact congrArg (fun h ↦ h m) he
    intro U m
    let a := (hZ.from U.unop).op
    have hc (Y : Scheme.{u}) (U V : Y.ProEtᵒᵖ) (a : U ⟶ V) :
        (proEtaleConstantModuleSheaf Y A M).val.map a
          (stratumConstantModuleSection Y A M U m) =
        stratumConstantModuleSection Y A M V m := by
      exact (congrArg (fun h ↦ h m)
        ((toSheafify (ProEt.topology Y)
          (proEtaleConstantModulePresheaf Y.ProEt A M).presheaf).naturality a)).symm
    have hn := PresheafOfModules.naturality_apply
      (((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val) a
      (stratumConstantModuleSection T A M (op Z) m)
    change (((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val.app U)
        ((proEtaleConstantModuleSheaf T A M).val.map a
          (stratumConstantModuleSection T A M (op Z) m)) =
      (proEtaleConstantModuleSheaf S A M).val.map ((proEtaleBaseChange i).op.map a)
        ((((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val.app (op Z))
          (stratumConstantModuleSection T A M (op Z) m)) at hn
    rw [hc T _ _ a, h0 m] at hn
    exact hn.trans (hc S _ _ ((proEtaleBaseChange i).op.map a))
  · obtain ⟨β, hβ, hu⟩ := stratumScalarExtensionModuleComparison i A B α
    refine ⟨β, hβ, hu, ?_⟩
    refine ⟨fun Q ↦ HomologicalComplex.Hom.isoOfComponents (fun n ↦ β (Q.X n)) ?_, ?_⟩
    · intro n m hnm
      exact (hβ _ _ (Q.d n m)).symm
    · intro Q n
      rfl
  · intro q
    exact ⟨((proEtaleConstantRingPullback A i).mapDerivedCategoryHomologyFunctorIso q).symm.app K⟩

end AlgebraicGeometry.Scheme
