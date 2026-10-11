/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Quasi-coherent modules along an affine morphism

Source: Stacks Project, Morphisms, Lemma 01SB
(blueprint: lem-weil-pbc-affine-module-correspondence).

The algebra `B = u^* A` is specified by its tensor-product universal property: the pushout
of `u⁻¹ O_X → O_U` and `u⁻¹ O_X → u⁻¹ A` in commutative ring sheaves. The functor `P`
is extension of scalars from `u⁻¹ A` to `B`; `κ` identifies its underlying module with the
recorded tensor pullback. Its formula on the pullback unit fixes this identification.
Thus the action is `(b ⊗ a)(b' ⊗ g) = bb' ⊗ ag`. The functor `H` is extension of
scalars along the multiplication counit `ε : B → O_U`, with the target scalar first
in the tensor notation. No alternative pullback or tensor product is defined here.
-/

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

/-- For an affine morphism, pushforward gives the equivalence of quasi-coherent modules
with quasi-coherent modules over its direct-image algebra. Quasi-coherence is unchanged
by restriction to the structure sheaf. The inverse is the two tensor operations in 01SB,
and the canonical counit-induced `α` and adjoint `β` are isomorphisms.
Source: Stacks Project, Morphisms, Lemma 01SB
(blueprint: lem-weil-pbc-affine-module-correspondence).

Proof:
1. The direct-image algebra is quasi-coherent by affine relative Spec
   (`lem-weil-pbc-affine-morphism-relative-spec`). Apply quasi-coherence under scalar
   restriction (`lem-weil-pbc-quasi-coherence-scalar-restriction`) to obtain clause (1).
2. Pushforward has the sectionwise algebra action and sends quasi-coherent modules to
   quasi-coherent modules (`lem-weil-pbc-affine-pushforward-base-change`).
3. Form the pulled-back algebra by the tensor pushout, and the pulled-back module by
   extension of scalars. Associativity of tensor products gives `κ`, with its stated
   formula. The counit is multiplicative and induces `ε`, hence the second extension
   of scalars `H`. Pullback and change of rings preserve quasi-coherence
   (`lem-weil-pbc-module-pullback-quasi-coherent`,
   `lem-weil-pbc-quasi-coherent-algebra-change-of-rings`). The tensor unit gives `γ`.
   The ordinary counit factors uniquely through it to give `α`; its adjoint gives `β`.
4. On an affine open `V` with inverse image `W`, the affine-sections pullback formula
   (`lem-weil-pbc-module-pullback-affine-sections`) identifies `H(G)(W)` with
   `(N ⊗_R B) ⊗_(B ⊗_R B) B`, where `N = G(V)`. The balanced map
   `(n ⊗ b) ⊗ c ↦ bc n` has inverse `n ↦ (n ⊗ 1) ⊗ 1`: move `b` and `c`
   through the balancing relation. Both are linear for the last-factor action.
5. Under this identification `α` is the balanced map and `β` its inverse. Their
   components are bijections on the affine covers. Apply
   `lem-weil-pbc-quasi-coherent-iso-on-affine-cover` to get isomorphisms. The maps
   are natural, and `β` is algebra-linear (check on affine opens, then glue).
6. Restrict these functors and natural isomorphisms to the full quasi-coherent
   subcategories, obtaining the asserted equivalence with inverse `H`. -/
theorem affine_module_correspondence [IsAffineHom f] :
    (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent ↔ ((S).obj G).IsQuasicoherent) ∧
    (∀ F : U.Modules, F.IsQuasicoherent → ((R).obj F).IsQuasicoherent) ∧
    ∃ (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf),
      IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀ ∧
      ∃ (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f),
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
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V)) ⊗ₜ[
                  (IA).obj.obj ((Opens.map f.base).op.obj V),
                  (t.hom.app ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))) ∧
        ∃ (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H),
          (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W, (ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent) ∧
          ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
            (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) ∧
            (∀ F : U.Modules, F.IsQuasicoherent → IsIso (α.app F)) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → IsIso (β.app G)) ∧
            ∃ E : (qU).FullSubcategory ≌ (qA).FullSubcategory,
              Nonempty (E.functor ⋙ (qA).ι ≅ (qU).ι ⋙ R) ∧
              Nonempty (E.inverse ⋙ (qU).ι ≅ (qA).ι ⋙ H) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
