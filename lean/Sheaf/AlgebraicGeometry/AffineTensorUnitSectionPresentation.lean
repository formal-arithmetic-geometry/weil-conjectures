/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings
import Sheaf.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-! # Affine tensor-unit section presentation

Source: Stacks Project, Morphisms, Lemma 01SB, key algebra observation.
(blueprint: lem-weil-pbc-affine-tensor-unit-section-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct

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

/-- Affine sections of the two tensor operations are the quotient of the first tensor
product by the diagonal-action relations. The map on unit tensors is canonical.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h and key algebra observation.
(blueprint: lem-weil-pbc-affine-tensor-unit-section-presentation).

Proof: Put D = O_X(V), C = O_U(f⁻¹V), and N = G(V). Affineness makes f⁻¹V affine.
The unit module of O_U has quasi-coherent affine pushforward, so the algebra f_*O_U
is quasi-coherent over O_X. Scalar restriction makes G quasi-coherent over O_X.
The affine pullback section formula identifies the first pullback with C tensor_D N,
with its unit n mapped to 1 tensor n. The ring-sheaf pushout and the same affine
formula identify B(f⁻¹V) with C tensor_D C. The equations for epsilon identify its
map to C with multiplication. The underlying O_U-module of P(G) is quasi-coherent by
kappa and the pullback formula. Quasi-coherent algebra change of rings therefore
identifies H(G)(f⁻¹V) with C tensor_(C tensor_D C) (C tensor_D N).
Send c tensor n to 1 tensor (c tensor n) in this last tensor product, and transport
along hobj and these affine identifications. Every outer scalar can be moved to
the scalar of the inner tensor using the element c tensor 1 of C tensor_D C, proving
surjectivity. Balancing with 1 tensor c then gives c tensor n = 1 tensor (c n).
These generate all relations: define the inverse from the double tensor product
to their quotient by a tensor (c tensor n) mapped to the class of ac tensor n.
The two C factors give the same class under this formula by the displayed relations;
D-balancing, additivity, and tensor induction give inverse quotient maps. Thus the
kernel is exactly the D-submodule spanned by the stated differences. Finally hP's
unit formula and hH's gamma formula identify the image of 1 tensor n with gamma
of the pullback unit. No beta or adjoint-comparison equation is used. All formulas
apply to the zero module, the zero ring, and the empty affine open.
-/
theorem affine_tensor_unit_section_presentation [IsAffineHom f]
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
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) Γ(H.obj G, f ⁻¹ᵁ V) :=
      Module.compHom _ (f.app V).hom
    ∃ q : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) →ₗ[Γ(X, V)]
        Γ(H.obj G, f ⁻¹ᵁ V),
      Function.Surjective q ∧
      LinearMap.ker q = Submodule.span Γ(X, V)
        {z | ∃ (c : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
          z = c ⊗ₜ[Γ(X, V)] n - (1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] (c • n)} ∧
      ∀ n : G.val.obj (op V),
        q ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (γ.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
