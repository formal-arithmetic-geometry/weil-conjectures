/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
public import Mathlib.CategoryTheory.Endomorphism

/-! # Isomorphisms to tensor powers of cubical rigidified lines

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I §2 and I 5.5.
(blueprint: def-sfb-cubical-tensor-power-iso)

Tensor powers use the existing sheaf tensor powers. Their rigidification and cube
section are characterized in tensor frames, including exponent zero. This expresses
preservation of the actual tensor cube section without choosing any cube comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.CubicalLine

/-- Tensor a map to the unit n times, using the canonical unit multiplication.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-tensor-power-iso). -/
noncomputable def powerToUnit {T : Scheme.{u}} {A : T.Modules}
    (f : A ⟶ 𝟙_ T.Modules) : (n : ℕ) → A.tensorPow n ⟶ 𝟙_ T.Modules
  | 0 => 𝟙 _
  | n + 1 => (f ⊗ₘ powerToUnit f n) ≫ (λ_ _).hom

/-- Tensor a map from the unit n times, using the canonical unit comultiplication.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-tensor-power-iso). -/
noncomputable def powerFromUnit {T : Scheme.{u}} {A : T.Modules}
    (f : 𝟙_ T.Modules ⟶ A) : (n : ℕ) → 𝟙_ T.Modules ⟶ A.tensorPow n
  | 0 => 𝟙 _
  | n + 1 => (λ_ _).inv ≫ (f ⊗ₘ powerFromUnit f n)

/-- The tensor product rigidification, with the unit rigidification at exponent zero.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-tensor-power-iso). -/
noncomputable def powerUnitIso (T : Scheme.{u}) :
    (n : ℕ) → (𝟙_ T.Modules).tensorPow n ≅ 𝟙_ T.Modules
  | 0 => Iso.refl _
  | n + 1 => (Iso.refl _ ⊗ᵢ powerUnitIso T n) ≪≫ λ_ _

/-- Tensor frames transported through the given underlying line isomorphism.
The maps are required to be inverse only at the finite list of factors under test.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-tensor-power-iso). -/
noncomputable def powerIsoFrame {Y T : Scheme.{u}} {L M : Y.Modules}
    (n : ℕ) (f : M ≅ L.tensorPow n) (b : Frame T L) : Frame T M :=
  fun a ↦
    ⟨(Scheme.Modules.tensorPullback a).map f.hom ≫
        (Scheme.Modules.boundaryPullbackPowIso a L n).hom ≫ powerToUnit (b a).1 n,
      powerFromUnit (b a).2 n ≫ (Scheme.Modules.boundaryPullbackPowIso a L n).inv ≫
        (Scheme.Modules.tensorPullback a).map f.inv⟩

end AlgebraicGeometry.CubicalLine
namespace AlgebraicGeometry.CubicalRigidifiedLine

/-- An underlying isomorphism identifies M with the tensor power of L as a rigidified
cubical line precisely when it respects the tensor rigidification and its cube values
are the nth powers of the cube values of L in tensor frames. Testing on all schemes
and finite valid frames detects equality of the actual sheaf sections, including on
nonreduced schemes. No compatibility condition is imposed on a freely chosen map.
Source: Moret-Bailly I §2 and I 5.5
(blueprint: def-sfb-cubical-tensor-power-iso). -/
def IsTensorPowerIso {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    (L M : CubicalRigidifiedLine G) (n : ℕ) (f : M.line ≅ L.line.tensorPow n) : Prop :=
  (Scheme.Modules.tensorPullback (η[G]).left).mapIso f ≪≫
      Scheme.Modules.boundaryPullbackPowIso (η[G]).left L.line n ≪≫
      Scheme.Modules.boundaryTensorPowIso L.rigidification n ≪≫
      CubicalLine.powerUnitIso S n = M.rigidification ∧
    ∀ (T : Over S) (x : Fin 3 → (T ⟶ G)) (b : CubicalLine.Frame T.left L.line),
      CubicalLine.Framed T x b →
      CubicalLine.value M.sectionIso T x (CubicalLine.powerIsoFrame n f b) =
        End.asHom (End.of (CubicalLine.value L.sectionIso T x b) ^ n)

end AlgebraicGeometry.CubicalRigidifiedLine
