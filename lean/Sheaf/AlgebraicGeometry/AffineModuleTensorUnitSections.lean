/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings
import Sheaf.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-! # Affine tensor unit on sections

Source: Stacks Project, Morphisms, Lemma 01SB, key algebra observation.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

set_option hygiene false in
local notation "fV" V => (Opens.map f.base).op.obj V

/-- The tensor unit comparison is bijective on the indicated affine sections.
Source: Stacks Project, Morphisms, Lemma 01SB, last two paragraphs.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-sections).

Proof: On V put D = O_X(V), C = O_U(f⁻¹V), and N = G(V).
The structure algebra f_*O_U is quasi-coherent by affine pushforward. Scalar restriction
therefore makes G quasi-coherent over O_X. The affine pullback section formula identifies
its pullback sections with C tensor_D N, compatibly with the adjunction unit.
The pushout identifies B on the affine preimage with C tensor_D C, with ε multiplication.
The affine change-of-rings section formula then identifies H(G)(f⁻¹V) with
C tensor_(C tensor_D C) (C tensor_D N). The κ-unit and γ equations, together with the
formula homEquiv(γ) = unit ≫ pushforward(γ), identify β on V with
n ↦ 1 tensor (1 tensor n). The inverse is c tensor (d tensor n) ↦ cd n,
where C acts on N through its A(V)-module structure. The action of a ⊗ b in C tensor_D C on d ⊗
n is ad ⊗ bn, whereas its action on the outer C is multiplication by ab. Thus the proposed
inverse sends both balanced representatives to cabd n. In the tensor quotient, balancing first
with d ⊗ 1 and then with 1 ⊗ cd gives c ⊗ (d ⊗ n) = cd ⊗ (1 ⊗ n) = 1 ⊗ (1 ⊗ (cd)n). Together
with (1 · 1)n = n, these are the inverse identities on pure tensors.
Additivity and tensor induction extend these identities to all sections. Hence β_V is
bijective, including the empty affine open and the zero module. -/
theorem affine_module_tensor_unit_sections_bijective [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
     (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hH : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent))
     (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R)
    (hcomp : ∀ G : SheafOfModules.{u} (𝓡 A),
      (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G))
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    Function.Bijective ((β.app G).val.app (op V)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
