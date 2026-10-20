/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.FibreFunctorBasepointTransportData
import Sheaf.Paper.FibreFunctorLinearTransport
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Quotient

/-! # Integral fibre paths from finite level evaluation

Source: Weil II (1.1.1) b), p.146.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The integral part of adic path transport, including its finite-level normalization.
Source: Weil II (1.1.1) b), p.146.
(blueprint: new-e5-integral-fibre-path-construction). -/
structure IntegralFibrePathTransport (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] where
  linear : ∀ E : Padic.FiniteCoefficientFields l Q,
    LinearFibrePathFamily Y (LisseIntegralSheaf l E.val Y)
      (Padic.coefficientExtensionIntegers l E.val)
      (fun y ↦ lisseIntegralFiberFunctor l E.val Y y)
  evaluation : ∀
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (E : Padic.FiniteCoefficientFields l Q)
    (F : LisseIntegralSheaf l E.val Y) (n : ℕ),
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
      (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))),
      ∀ x : (lisseIntegralFiberFunctor l E.val Y y).obj F,
      pathUnderlyingStalk z (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))
        (limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber) (op n)
          (((linear E).map y z t).hom.app F x)) =
      t.hom.app (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n)) h)
        (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))
          (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) x))

variable {Y : Scheme.{u}}

private theorem finite_of_annihilated {R : Type (u + 1)} [CommRing R]
    (I : Ideal R) [Finite (R ⧸ I)] (M : Type (u + 1)) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (h : I • (⊤ : Submodule R M) = ⊥) : Finite M := by
  let : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let : Finite (M ⧸ (I • (⊤ : Submodule R M))) := Module.finite_of_finite (R ⧸ I)
  exact Finite.of_equiv _ ((I • (⊤ : Submodule R M)).quotEquivOfEqBot h).toEquiv

private theorem finite_integral_level (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (F : LisseIntegralSheaf l E Y) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
        (F.obj.obj (op n))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let p := (pointSmallEtale y).ulift.{u + 1}
  let G := F.obj.obj (op n)
  let M := p.sheafFiber.obj G
  let : Finite (R ⧸ I) := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have hfg := (F.property.1 n).toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω y
  let : Module.Finite R (((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj G) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp hfg
  let : Module.Finite R M := Module.Finite.equiv
    (((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} R)).app G).toLinearEquiv.symm
  apply finite_of_annihilated I M
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro r hr x _
  obtain ⟨U, ξ, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := G.obj) x
  have hkill : r • s = 0 := by
    have hmem : r • s ∈ I • (⊤ : Submodule R (G.obj.obj (op U))) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    have hi : I • (⊤ : Submodule R (G.obj.obj (op U))) = ⊥ := F.property.2.1 n U
    rw [hi, Submodule.mem_bot] at hmem
    exact hmem
  change r • p.toPresheafFiber U ξ G.obj s = 0
  rw [← map_smul, hkill, map_zero]

private theorem integral_level_lisse (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (F : LisseIntegralSheaf l E Y) (n : ℕ) : IsLisseModuleSheaf (F.obj.obj (op n)) :=
  isLisseModuleSheaf_of_locallyConstant_of_finite_stalk _ _
    (F.property.1 n).toIsLocallyConstantSheaf (fun _ _ _ y ↦ finite_integral_level l E F n y)

private def integralLisseDiagram (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    LisseIntegralSheaf l E Y ⥤
      (ℕᵒᵖ ⥤ LisseModuleSheafCategory Y (Padic.coefficientExtensionIntegers l E)) where
  obj F :=
    { obj n := ⟨F.obj.obj n, integral_level_lisse l E F n.unop⟩
      map f := ObjectProperty.homMk (F.obj.map f)
      map_id n := by
        apply ObjectProperty.hom_ext
        exact F.obj.map_id n
      map_comp f g := by
        apply ObjectProperty.hom_ext
        exact F.obj.map_comp f g }
  map f :=
    { app n := ObjectProperty.homMk (f.hom.app n)
      naturality := by
        intro n m g
        apply ObjectProperty.hom_ext
        exact f.hom.naturality g }
  map_id F := by
    apply NatTrans.ext
    funext n
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    rfl

private def integralPathWhiskering (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :
    (LisseModuleSheafCategory Y (Padic.coefficientExtensionIntegers l E) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⥤
    (LisseIntegralSheaf l E Y ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  Functor.whiskeringRight _ _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj lim ⋙
      (Functor.whiskeringLeft _ _ _).obj (integralLisseDiagram l E Y)

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber pathUnderlyingStalk

set_option backward.isDefEq.respectTransparency false in
private def integralFamily (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (d : LinearFibrePathFamily Y
      (LisseModuleSheafCategory Y (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ pathModuleFiber y (Padic.coefficientExtensionIntegers l E))) :
    LinearFibrePathFamily Y (LisseIntegralSheaf l E Y)
      (Padic.coefficientExtensionIntegers l E)
      (fun y ↦ lisseIntegralFiberFunctor l E Y y) where
  map := by
    intro Ωy _ _ y Ωz _ _ z t
    exact (integralPathWhiskering l E Y).mapIso (d.map y z t)
  identity := by
    intro Ω _ _ y
    exact (congrArg (fun t ↦ (integralPathWhiskering l E Y).mapIso t) (d.identity y)).trans
      (Functor.mapIso_refl _ _)
  composition := by
    intro Ωy _ _ y Ωz _ _ z Ωq _ _ q t s
    exact (congrArg (fun t ↦ (integralPathWhiskering l E Y).mapIso t)
      (d.composition y z q t s)).trans (Functor.mapIso_trans _ _ _)
  conjugation := by
    intro Ωy _ _ y Ωz _ _ z t g
    have h := congrArg (fun t ↦ (integralPathWhiskering l E Y).mapIso t)
      (d.conjugation y z t g)
    simpa only [Functor.mapIso_trans, Functor.mapIso_symm] using h
  change := by
    intro Ωy _ _ y Ωz _ _ z t s
    exact (congrArg (fun t ↦ (integralPathWhiskering l E Y).mapIso t)
      (d.change y z t s)).trans (Functor.mapIso_trans _ _ _)

/-- Finite-level evaluation extends uniquely to integral inverse-limit fibres.
Source: Deligne, Weil II (1.1.1) b), p.146.
(blueprint: new-e5-integral-fibre-path-construction).
Proof: each level has finitely generated stalks, killed by the recorded ideal power.
They are finite modules over a finite coefficient quotient, hence finite sets. Local
constancy therefore gives finite constant module models. Apply the normalized linear
path family to the level diagram and then apply the limit functor. Its projection
formula is the defining naturality formula for the limit map. Every path law follows
by applying this functor to the corresponding law on the finite-level family. -/
theorem integral_fibre_path_transport_exists (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] :
    Nonempty (IntegralFibrePathTransport l Y Q) := by
  let d := fun E : Padic.FiniteCoefficientFields l Q ↦
    lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E.val)
  let linear : ∀ E : Padic.FiniteCoefficientFields l Q,
      LinearFibrePathFamily Y (LisseIntegralSheaf l E.val Y)
        (Padic.coefficientExtensionIntegers l E.val)
        (fun y ↦ lisseIntegralFiberFunctor l E.val Y y) :=
    fun E ↦ integralFamily l E.val Y (d E)
  refine ⟨⟨linear, ?_⟩⟩
  intro Ωy _ _ y Ωz _ _ z t E F n
  let R := Padic.coefficientExtensionIntegers l E.val
  let Fₙ : LisseModuleSheafCategory Y R :=
    ⟨F.obj.obj (op n), integral_level_lisse l E.val F n⟩
  have hn := @lisseLinearFibrePathFamily_evaluation Y R inferInstance
    Ωy inferInstance inferInstance y Ωz inferInstance inferInstance z t Fₙ
  obtain ⟨h, hh⟩ := hn
  refine ⟨h, ?_⟩
  intro x
  have hπ : ((integralFamily l E.val Y (d E)).map y z t).hom.app F ≫
      limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber) (op n) =
    limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
      ((d E).map y z t).hom.app Fₙ := by
    exact limMap_π _ (op n)
  have hπx := ConcreteCategory.congr_hom hπ x
  exact (congrArg (pathUnderlyingStalk z R Fₙ.obj) hπx).trans (hh _)

end AlgebraicGeometry.Scheme
