/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.NativeWeilComponentCycle
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLiftOfStr
public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.NativeLisseCoefficients

/-! # The actual functor of first-return restriction

Source: Deligne, Weil II (1.1.12), the cyclic component argument.
(blueprint: def-dl-a1-native-weil-return-functor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

attribute [local irreducible] CondensedRing.upperStar

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]
variable (ell : ℕ) [Fact ell.Prime]

private theorem isoChain_natural {C : Type v} [Category.{w} C]
    (P : ℕ → C ⥤ C) {X Y : C} (f : X ⟶ Y)
    {iX : (P 0).obj X ≅ X} {iY : (P 0).obj Y ≅ Y}
    {sX : ∀ n, (P (n + 1)).obj X ≅ (P n).obj X}
    {sY : ∀ n, (P (n + 1)).obj Y ≅ (P n).obj Y}
    (hi : (P 0).map f ≫ iY.hom = iX.hom ≫ f)
    (hs : ∀ n, (P (n + 1)).map f ≫ (sY n).hom = (sX n).hom ≫ (P n).map f)
    (n : ℕ) :
    (P n).map f ≫
        (WeilConjectures.CondensedModule.isoChain (fun n ↦ (P n).obj Y) Y iY sY n).hom =
      (WeilConjectures.CondensedModule.isoChain (fun n ↦ (P n).obj X) X iX sX n).hom ≫ f := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change (P (n + 1)).map f ≫ ((sY n).hom ≫
      (WeilConjectures.CondensedModule.isoChain (fun n ↦ (P n).obj Y) Y iY sY n).hom) =
      ((sX n).hom ≫
        (WeilConjectures.CondensedModule.isoChain (fun n ↦ (P n).obj X) X iX sX n).hom) ≫ f
    rw [← Category.assoc, hs n, Category.assoc, ih, Category.assoc]

private theorem evaluateStep_natural {C : Type v} [Category.{w} C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) {X Y : C} (f : X ⟶ Y)
    (θX : G.obj X ≅ X) (θY : G.obj Y ≅ Y)
    (hθ : G.map f ≫ θY.hom = θX.hom ≫ f) :
    H.map f ≫ (WeilConjectures.CondensedModule.evaluateStep F G H c Y θY).hom =
      (WeilConjectures.CondensedModule.evaluateStep F G H c X θX).hom ≫ F.map f := by
  simp only [WeilConjectures.CondensedModule.evaluateStep, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, c.hom.naturality, Category.assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hθ, Functor.map_comp, Category.assoc]

private theorem evaluateInitial_natural {C : Type v} [Category.{w} C]
    (F G : C ⥤ C) (c : F ≅ G) {X Y : C} (f : X ⟶ Y)
    (θX : G.obj X ≅ X) (θY : G.obj Y ≅ Y)
    (hθ : G.map f ≫ θY.hom = θX.hom ≫ f) :
    F.map f ≫ (WeilConjectures.CondensedModule.evaluateInitial F G c Y θY).hom =
      (WeilConjectures.CondensedModule.evaluateInitial F G c X θX).hom ≫ f := by
  simp only [WeilConjectures.CondensedModule.evaluateInitial, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, c.hom.naturality, Category.assoc, hθ, Category.assoc]

/-- The normalized pullback square for the first return on the component.
Source: the equality returnIso.hom ≫ inclusion = inclusion ≫ Phi^(n+1).
(blueprint: def-dl-a1-native-weil-return-functor). -/
def componentReturnSquare (A : Geometry D U₀ t G) (B : ComponentCycle D U₀ t G A) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) B.returnIso.hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
          (WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom B.n) ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell)
    B.returnIso.hom A.inclusion).symm ≪≫
  CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ell) B.square ≪≫
  CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) A.inclusion
    (WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom B.n)

private def lifted_return_forget
    {C E : Type v} [Category.{w} C] [Category.{w} E]
    {F : C ⥤ C} (G : C ⥤ C)
    (φ : ∀ K : Endofunctor.IsoAlgebra F, G.obj K.carrier ≅ K.carrier)
    (hφ : ∀ {K K' : Endofunctor.IsoAlgebra F} (f : K ⟶ K'),
      G.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)
    {G' : E ⥤ E} {L : C ⥤ E} (e : L ⋙ G' ≅ G ⋙ L)
    (P : ObjectProperty (Endofunctor.IsoAlgebra F))
    (Q : ObjectProperty (Endofunctor.IsoAlgebra G'))
    (hQ : ∀ M : P.FullSubcategory,
      Q ((Endofunctor.IsoAlgebra.liftOfStr G φ hφ ⋙
        Endofunctor.IsoAlgebra.mapOfNatIso e).obj M.obj)) :
    ObjectProperty.lift Q
      (P.ι ⋙ (Endofunctor.IsoAlgebra.liftOfStr G φ hφ ⋙
        Endofunctor.IsoAlgebra.mapOfNatIso e)) hQ ⋙
        (Q.ι ⋙ Endofunctor.IsoAlgebra.forget G') ≅
      P.ι ⋙ Endofunctor.IsoAlgebra.forget F ⋙ L := Iso.refl _

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
