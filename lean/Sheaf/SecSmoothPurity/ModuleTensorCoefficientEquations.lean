/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Sheaf.SecSmoothPurity.ModuleTensorExtensionEquation

/-! # Tensor squares for module coefficient change

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-coefficient-equations)
-/

@[expose] public section

universe w uC vC uD vD uE vE u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

private theorem mate_pair
    {A : Type u} [Category.{v} A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
    (L : A ⥤ B) (U : B ⥤ A) (adj : L ⊣ U)
    (mu : ∀ X Y : A, L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hn : ∀ {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y'),
      L.map (a ⊗ₘ b) ≫ mu X' Y' = mu X Y ≫ (L.map a ⊗ₘ L.map b))
    (X Y : A) (P Q : B) (a : X ⟶ U.obj P) (b : Y ⟶ U.obj Q) :
    (a ⊗ₘ b) ≫ adj.homEquiv _ _
      (mu (U.obj P) (U.obj Q) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q)) =
      adj.unit.app (X ⊗ Y) ≫ U.map
        (mu X Y ≫ ((L.map a ≫ adj.counit.app P) ⊗ₘ
          (L.map b ≫ adj.counit.app Q))) := by
  rw [Adjunction.homEquiv_unit, ← Category.assoc, ← adj.unit_naturality]
  rw [Category.assoc, ← U.map_comp, ← Category.assoc, hn]
  simp only [Category.assoc, tensorHom_comp_tensorHom]

private theorem transition_square
    {A : Type u} [Category.{v} A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
    (L : A ⥤ B) (U : B ⥤ A) (adj : L ⊣ U)
    (mu : ∀ X Y : A, L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hn : ∀ {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y'),
      L.map (a ⊗ₘ b) ≫ mu X' Y' = mu X Y ≫ (L.map a ⊗ₘ L.map b))
    (X Y Z : A) (P Q W : B)
    (bP : P ≅ L.obj X) (bQ : Q ≅ L.obj Y) (bW : W ≅ L.obj Z)
    (alpha : Z ⟶ X ⊗ Y) (nu : W ⟶ P ⊗ Q)
    (h : nu ≫ (bP.hom ⊗ₘ bQ.hom) = bW.hom ≫ L.map alpha ≫ mu X Y) :
    alpha ≫ ((adj.unit.app X ≫ U.map bP.inv) ⊗ₘ
      (adj.unit.app Y ≫ U.map bQ.inv)) ≫ adj.homEquiv _ _
        (mu (U.obj P) (U.obj Q) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q)) =
      (adj.unit.app Z ≫ U.map bW.inv) ≫ U.map nu := by
  have hp : L.map (adj.unit.app X ≫ U.map bP.inv) ≫ adj.counit.app P = bP.inv := by
    exact (adj.homEquiv _ _).symm_apply_apply bP.inv
  have hq : L.map (adj.unit.app Y ≫ U.map bQ.inv) ≫ adj.counit.app Q = bQ.inv := by
    exact (adj.homEquiv _ _).symm_apply_apply bQ.inv
  rw [mate_pair L U adj mu hn, hp, hq]
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← U.map_comp]
  simp only [Category.assoc, ← U.map_comp]
  congr 1
  apply congrArg U.map
  apply (cancel_epi bW.hom).1
  apply (cancel_mono (bP.hom ⊗ₘ bQ.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom,
    Iso.inv_hom_id, id_tensorHom_id, Category.comp_id]
  exact h.symm

/-- The scalar-association and restricted-transition tensor squares for modules.
Source: Stacks 03EL, change of rings and the tensor pullback comparison.
(blueprint: lem-pur-module-tensor-coefficient-equations).

Proof: for the first equation use generalized pure tensors with outside
scalar s' and original generators x,y. The source coefficient scalar can
be moved outside by balancing, using d.square and d.inverseImageMap_graph.
The defining IsScalarAssociation equation fixes kappa on those generators.
Both routes send s' tensor ((x tensor y) tensor 1) to
((1 tensor x) tensor s') tensor ((1 tensor y) tensor 1).
For the second equation, expand transitionModule as the extension unit
followed by restricted inverse scalar association. The extension unit sends
x to 1 tensor x. The restrictionTensorModule is the adjunction mate of
the extension comparison followed by its two counits; the triangle identity
therefore makes its pure-tensor formula x tensor y mapped to x tensor y.
Both routes send s tensor (x tensor y) to
(bar(s) tensor (x tensor 1)) tensor (1 tensor (y tensor 1)).
These are equal S-linear maps after the indicated scalar restriction.
The tensor universal property, scalar-extension linearity and sheafification
extend both equations from generators to all sections. No inverse to the
transition is used; quotient maps and zero coefficient rings are included. -/
theorem cochainModuleTensorCoefficients (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    (∀ M N : Modules R,
      (changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
          (k'.mu ((extensionFunctor d.sourceMap).obj M)
            ((extensionFunctor d.sourceMap).obj N)).hom ≫
          ((scalarAssociation f k d k').hom.app M ⊗ₘ
            (scalarAssociation f k d k').hom.app N) =
        (scalarAssociation f k d k').hom.app (M ⊗ N) ≫
          (extensionFunctor d.targetMap).map (k.mu M N).hom ≫
          ((extensionComparison d.targetMap).mu (f.L.obj M) (f.L.obj N)).hom) ∧
    (∀ M N : Modules R,
      (k.mu M N).hom ≫
          ((transitionModule f k d k').app M ⊗ₘ (transitionModule f k d k').app N) ≫
          restrictionTensorModule d.targetMap
            ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj M))
            ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj N)) =
        (transitionModule f k d k').app (M ⊗ N) ≫ (restrictionFunctor d.targetMap).map
          ((changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
            (k'.mu ((extensionFunctor d.sourceMap).obj M)
              ((extensionFunctor d.sourceMap).obj N)).hom)) := by
  have h := cochainModuleTensorExtensionCoefficient f k d k'
  refine ⟨h, ?_⟩
  intro M N
  let b := scalarAssociation f k d k'
  simpa only [transitionModule, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, restrictionTensorModule,
    b, Iso.app_inv, Functor.id_obj] using
    transition_square (extensionFunctor d.targetMap) (restrictionFunctor d.targetMap)
      (extensionAdjunction d.targetMap)
      (fun X Y ↦ ((extensionComparison d.targetMap).mu X Y).hom)
      (extensionComparison d.targetMap).naturality
      (f.L.obj M) (f.L.obj N) (f.L.obj (M ⊗ N))
      ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj M))
      ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj N))
      ((changed f d).L.obj ((extensionFunctor d.sourceMap).obj (M ⊗ N)))
      (b.app M) (b.app N) (b.app (M ⊗ N)) (k.mu M N).hom
      ((changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
        (k'.mu ((extensionFunctor d.sourceMap).obj M)
          ((extensionFunctor d.sourceMap).obj N)).hom)
      (by simpa only [b, Category.assoc, Iso.app_hom] using h M N)

end CategoryTheory.CochainPullback
