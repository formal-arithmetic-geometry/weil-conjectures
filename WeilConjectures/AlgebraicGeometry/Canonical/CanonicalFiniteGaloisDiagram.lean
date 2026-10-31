/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorLinearTransport

/-! # Canonical finite-level Galois actions on integral stalk towers

Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9.
(blueprint: new-e7-canonical-finite-galois-diagram).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  (c : GaloisLisseFiniteCorrespondence y G)

private noncomputable def integralLevelObject (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    LisseModuleSheafCategory Y (Padic.coefficientExtensionIntegers l E) :=
  ⟨F.obj.obj (op n), integral_level_lisse l E F n⟩

private noncomputable def integralFiniteAction (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    Representation (Padic.coefficientExtensionIntegers l E) G
      ((pathModuleFiber y (Padic.coefficientExtensionIntegers l E)).obj
        (integralLevelObject l E F n)) where
  toFun g :=
    (((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
      y y (c.γ g)).hom.app (integralLevelObject l E F n)).hom
  map_one' := by
    change (((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
      y y (c.γ 1)).hom.app (integralLevelObject l E F n)).hom = LinearMap.id
    rw [map_one]
    change (((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
      y y (Iso.refl (flcFiber y))).hom.app (integralLevelObject l E F n)).hom = _
    rw [(lisseLinearFibrePathFamily Y _).identity]
    rfl
  map_mul' g h := by
    ext x
    change ((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
        y y (c.γ (g * h))).hom.app (integralLevelObject l E F n) x =
      ((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
        y y (c.γ g)).hom.app (integralLevelObject l E F n)
          (((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
            y y (c.γ h)).hom.app (integralLevelObject l E F n) x)
    rw [map_mul]
    change ((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
        y y ((c.γ h) ≪≫ (c.γ g))).hom.app (integralLevelObject l E F n) x = _
    rw [(lisseLinearFibrePathFamily Y _).composition]
    rfl

private noncomputable def canonicalFiniteDiagram (F : LisseIntegralSheaf l E Y) :
    ℕᵒᵖ ⥤ Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G where
  obj j := Rep.of (integralFiniteAction l E y G c F j.unop)
  map {j k} f := Rep.ofHom
    { toLinearMap := (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map (F.obj.map f)).hom
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact (ConcreteCategory.congr_hom
          (((lisseLinearFibrePathFamily Y (Padic.coefficientExtensionIntegers l E)).map
            y y (c.γ g)).hom.naturality
              (ObjectProperty.homMk (F.obj.map f) :
                integralLevelObject l E F j.unop ⟶ integralLevelObject l E F k.unop)) x).symm }
  map_id j := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    change (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map
      (F.obj.map (𝟙 j))).hom = LinearMap.id
    simp
  map_comp f g := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    change (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map
      (F.obj.map (f ≫ g))).hom = _
    simp only [Functor.map_comp]
    rfl

private noncomputable def canonicalFiniteComparison (F : LisseIntegralSheaf l E Y) :
    canonicalFiniteDiagram l E y G c F ⋙
        forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
      F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)

private theorem canonicalFiniteAction_evaluation (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    ∃ h : IsLisseEtaleSheafOfSets
      (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))),
    ∀ (g : G) (x : (canonicalFiniteDiagram l E y G c F).obj (op n)),
      pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
        ((canonicalFiniteComparison l E y G c F).hom.app (op n)
          (((canonicalFiniteDiagram l E y G c F).obj (op n)).ρ g x)) =
      (c.γ g).hom.app
        (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)) h)
        (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
          ((canonicalFiniteComparison l E y G c F).hom.app (op n) x)) := by
  obtain ⟨h, _⟩ := lisseLinearFibrePathFamily_evaluation
    (Padic.coefficientExtensionIntegers l E) y y (c.γ 1) (integralLevelObject l E F n)
  refine ⟨h, ?_⟩
  intro g x
  obtain ⟨h, he⟩ := lisseLinearFibrePathFamily_evaluation
    (Padic.coefficientExtensionIntegers l E) y y (c.γ g) (integralLevelObject l E F n)
  exact he x

/-- Finite stalk actions normalized by the supplied finite evaluation automorphism.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, integral stage.
(blueprint: new-e7-canonical-finite-galois-diagram).

The existing integral fibre-path construction proves that every level is lisse:
its stalks are finite modules annihilated by a positive uniformizer power, hence
finite sets over the finite coefficient quotient; local constancy then gives
finite constant module models over the integer ring.
Apply the existing linear fibre-path family to c.γ at every level. The identity and
composition laws give representations on the actual module stalks. Naturality makes
all transition maps equivariant, so these representations form a diagram whose
underlying module comparison is the identity. The path family's evaluation theorem
identifies its action with c.γ. Its canonical underlying-stalk comparison preserves
every germ, giving both required normalizations. -/
theorem canonical_finite_galois_diagram
    {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : LisseIntegralSheaf l E Y) :
    ∃ V : ℕᵒᵖ ⥤ Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G,
    ∃ α : V ⋙ forget₂ (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
      F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber,
    ∀ n : ℕ,
      ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
        (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))),
      (∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
          (z : (F.obj.obj (op n)).obj.obj (op U)),
        pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
            ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩
              (F.obj.obj (op n)).obj z) =
          (pointSmallEtale y).toPresheafFiber U x
            (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E)
              (F.obj.obj (op n))).obj z) ∧
      ∀ (g : G) (z : (V.obj (op n)).V),
        pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
            ((α.hom.app (op n)) ((V.obj (op n)).ρ g z)) =
          (c.γ g).hom.app (galoisUnderlyingFLC
            (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)) h)
            (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))
              ((α.hom.app (op n)) z)) := by
  refine ⟨canonicalFiniteDiagram l E y G c F, canonicalFiniteComparison l E y G c F, ?_⟩
  intro n
  obtain ⟨h, he⟩ := canonicalFiniteAction_evaluation l E y G c F n
  exact ⟨h, pathUnderlyingStalk_germ y _ (F.obj.obj (op n)), he⟩

end AlgebraicGeometry.Scheme
