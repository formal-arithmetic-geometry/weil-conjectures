/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
/-! # Scalar compatibility of the affine tensor counit

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-smul).
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
/-- Scalar compatibility of the transported pullback counit.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-counit-smul).

Proof: Write q for κ followed by the canonical pullback counit, an O_U-linear map.
The inverse-image module adjunction supplies an IA-linear counit v : I(RF) → F,
where IA acts on F through e₀. The tensor evaluation c ⊗ s ↦ ε(c) • v(s) is balanced
because t ≫ ε = e₀. Its sectionwise B-linear maps commute with restriction, so the
sheafification universal property supplies a B-linear evaluation d on P(RF),
using pobj. By the inverse-image triangle, d sends the sheafification of
1 ⊗ η(g) to g. The hP unit formula and the tensor-pullback triangle show that
q has the same value on these sections. On an arbitrary open, inverse-image
sections are locally represented by sections g over opens of X. The pushout
identifies the restriction of B ⊗_{IA} I(RF) with
O_U ⊗_{f⁻¹O_X} I(RF); hence O_U multiples of these unit sections locally generate
its sheafification. Restrict d along b. Its O_U-linearity follows from b ≫ ε = 1.
Thus this restriction of d equals q, first on the generating local sections,
then on every section by additivity and the sheaf separatedness axiom.
The displayed identity follows from B-linearity of d. For c = 0 or p = 0 both
sides vanish; zero rings and the empty open satisfy the same identities. -/
theorem affine_module_tensor_counit_smul
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t)
    (hb : b ≫ ε = 𝟙 U.sheaf) (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP :
        (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app ((Opens.map f.base).op.obj V))
            ((κ.inv.app G).val.app ((Opens.map f.base).op.obj V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                ((Opens.map f.base).op.obj V)
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V))
                  ⊗ₜ[(IA).obj.obj ((Opens.map f.base).op.obj V),(t.hom.app
                    ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g)))) :
    ∀ (F : U.Modules) (W : (Opens U)ᵒᵖ) (c : B.obj.obj W)
      (p : (P.obj ((R).obj F)).val.obj W),
      ((adj₀).counit.app F).val.app W ((κ.hom.app ((R).obj F)).val.app W (c • p)) =
        (ε.hom.app W c) •
          ((adj₀).counit.app F).val.app W ((κ.hom.app ((R).obj F)).val.app W p) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
