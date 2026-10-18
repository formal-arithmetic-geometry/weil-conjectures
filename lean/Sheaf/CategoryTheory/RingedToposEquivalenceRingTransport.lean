/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.CategoryTheory.RingedToposRingData
public import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Sheaf.CategoryTheory.AdjunctionRingOperations

/-!
# Transporting one ring sheaf across an equivalence

Source: Stacks Project, Sites, Section 00YR, rings as sextuples; Modules on Sites, 03CR.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The five operations of a ring sheaf, with all diagrams checked on sections. -/
@[instance_reducible] private def sourceRingStructure
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{u}) :
    CommRingObj ((sheafCompose J (forget CommRingCat.{u})).obj A) where
  zero := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U))
             naturality := by
               intro X Y f
               ext x
               change (0 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_zero _).symm }⟩
  add := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 + x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 + (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 + x.2)
              exact (map_add _ _ _).symm }⟩
  neg := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U ↦ -x)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X at x
              change -(A.obj.map f).hom x = (A.obj.map f).hom (-x)
              exact (map_neg _ _).symm }⟩
  one := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : A.obj.obj U))
            naturality := by
               intro X Y f
               ext x
               change (1 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_one _).symm }⟩
  mul := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 * x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 * (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 * x.2)
              exact (map_mul _ _ _).symm }⟩
  zero_add := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (0 : A.obj.obj U) + x.2 = x.2
    exact zero_add x.2
  add_zero := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) + 0 = x.1
    exact add_zero x.1
  add_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc x.1.1 x.1.2 x.2
  left_neg := by
    ext U x
    change A.obj.obj U at x
    change -(x : A.obj.obj U) + x = 0
    exact neg_add_cancel x
  right_neg := by
    ext U x
    change A.obj.obj U at x
    change (x : A.obj.obj U) + -x = 0
    exact add_neg_cancel x
  add_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) + x.1 = x.1 + x.2
    exact add_comm x.2 x.1
  one_mul := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (1 : A.obj.obj U) * x.2 = x.2
    exact one_mul x.2
  mul_one := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) * 1 = x.1
    exact mul_one x.1
  mul_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) * x.1.2 * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc x.1.1 x.1.2 x.2
  mul_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) * x.1 = x.1 * x.2
    exact mul_comm x.2 x.1
  mul_add := by
    ext U x
    change A.obj.obj U × (A.obj.obj U × A.obj.obj U) at x
    change (x.1 : A.obj.obj U) * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
    exact mul_add x.1 x.2.1 x.2.2
  add_mul := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change ((x.1.1 : A.obj.obj U) + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
    exact add_mul x.1.1 x.1.2 x.2


private theorem reconstructed_constant
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (Y : CommRingObjCat (Sheaf K (Type u))) (A' : Sheaf K CommRingCat.{u})
    (q : Y.X ≅ (sheafCompose K (forget CommRingCat)).obj A')
    (o : 𝟙_ (Sheaf K (Type u)) ⟶ Y.X)
    (c : ∀ U : Dᵒᵖ, A'.obj.obj U)
    (ho : ∀ U t, q.hom.hom.app U (o.hom.app U t) = c U)
    (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget CommRingCat)).obj A')
    (hz : ∀ U t, z.hom.app U t = c U) :
    z ≫ q.inv = toUnit T ≫ o := by
  apply (cancel_mono q.hom).mp
  simp only [Category.assoc, q.inv_hom_id, Category.comp_id]
  ext U t
  exact (hz U t).trans (ho U ((toUnit T).hom.app U t)).symm

private theorem reconstructed_binary
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (Y : CommRingObjCat (Sheaf K (Type u))) (A' : Sheaf K CommRingCat.{u})
    (q : Y.X ≅ (sheafCompose K (forget CommRingCat)).obj A')
    (o : Y.X ⊗ Y.X ⟶ Y.X)
    (c : ∀ U : Dᵒᵖ, A'.obj.obj U → A'.obj.obj U → A'.obj.obj U)
    (ho : ∀ U a b, q.hom.hom.app U (o.hom.app U (a,b)) =
      c U (q.hom.hom.app U a) (q.hom.hom.app U b))
    {T : Sheaf K (Type u)}
    (x y z : T ⟶ (sheafCompose K (forget CommRingCat)).obj A')
    (hz : ∀ U t, z.hom.app U t = c U (x.hom.app U t) (y.hom.app U t)) :
    z ≫ q.inv = lift (x ≫ q.inv) (y ≫ q.inv) ≫ o := by
  apply (cancel_mono q.hom).mp
  simp only [Category.assoc, q.inv_hom_id, Category.comp_id]
  ext U t
  change z.hom.app U t = q.hom.hom.app U
    (o.hom.app U (q.inv.hom.app U (x.hom.app U t), q.inv.hom.app U (y.hom.app U t)))
  rw [ho]
  have hx := congrArg (fun k ↦ k.hom.app U (x.hom.app U t)) q.inv_hom_id
  have hy := congrArg (fun k ↦ k.hom.app U (y.hom.app U t)) q.inv_hom_id
  change q.hom.hom.app U (q.inv.hom.app U (x.hom.app U t)) = x.hom.app U t at hx
  change q.hom.hom.app U (q.inv.hom.app U (y.hom.app U t)) = y.hom.app U t at hy
  rw [hx, hy]
  exact hz U t

/-- Transport one ring sheaf along an equivalence, with its counit structural map.

Source: Stacks Project, Sites, Proposition 00YV (rings as sextuples), and Modules
on Sites, Tag 03CR, transport of the structure sheaves;
(blueprint: lem-weil-pbc-ringed-topos-equivalence-ring-transport).

Proof in words: regard A as an internal commutative ring by the algebraic-sheaf
correspondence. Apply the finite-product ring functor for G.functor: the underlying
object is G.functor(|A|), with binary operations obtained by inverse product
comparisons, constants by the inverse terminal comparison, and negation by G.
Convert this ring object back to a commutative ring sheaf A'. The equality of
underlying functors gives a:|A'|≅G.functor(|A|). Set the inverse and direct images
to G.inverse and G.functor, take the equivalence adjunction, and set the structural
map to G.inverse(a.hom) followed by its counit. A natural transformation between
finite-product-preserving functors commutes with product comparisons: compose
with each projection and use naturality, and use uniqueness for the terminal
comparison. Apply this to the counit at zero, one, addition and multiplication.
It says exactly that the structural map satisfies the four generalized-element
ring identities. Both a and the counit are invertible, so the structural map is
invertible. These specified transported operations determine the ring structure;
no unspecified data are chosen from mere existence. -/
theorem ringedTopos_equivalenceRingTransport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u})
    (G : Sheaf J (Type u) ≌ Sheaf K (Type u)) :
    ∃ (A' : Sheaf K CommRingCat.{u})
      (g : RingedToposMorphism.RingData
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj A'))
      (a : (sheafCompose K (forget CommRingCat)).obj A' ≅
        g.direct.obj ((sheafCompose J (forget CommRingCat)).obj A)),
      g.inverse = G.inverse ∧ g.direct = G.functor ∧
      g.ringMap = g.inverse.map a.hom ≫
        g.adj.counit.app ((sheafCompose J (forget CommRingCat)).obj A) ∧
      IsIso g.ringMap := by
  let X : CommRingObjCat (Sheaf J (Type u)) :=
    { X := (sheafCompose J (forget CommRingCat)).obj A
      commRingObj := sourceRingStructure J A }
  obtain ⟨FF, hFF, hops⟩ := Adjunction.finiteProductRingFunctor G.functor
  let Y := FF.obj X
  let : CommRingObj X.X := X.commRingObj
  let : CommRingObj Y.X := Y.commRingObj
  let d : Y.X ≅ G.functor.obj X.X :=
    (eqToIso hFF).app X
  obtain ⟨A', hq, hqops⟩ := sheafRingObject_sectionwise_reconstruction K Y
  let q : Y.X ≅ (sheafCompose K (forget CommRingCat)).obj A' := eqToIso hq
  let a := q.symm ≪≫ d
  let L := G.inverse
  let adj : L ⊣ G.functor := G.symm.toAdjunction
  let r := L.map a.hom ≫ adj.counit.app X.X
  have hconst (o : 𝟙_ (Sheaf J (Type u)) ⟶ X.X)
      (o' : 𝟙_ (Sheaf K (Type u)) ⟶ Y.X)
      (hc : o' ≫ d.hom = (preservesTerminalIso G.functor).inv ≫ G.functor.map o)
      (c : ∀ U : Dᵒᵖ, A'.obj.obj U)
      (ho : ∀ U t, q.hom.hom.app U (o'.hom.app U t) = c U)
      (T : Sheaf K (Type u))
      (z : T ⟶ (sheafCompose K (forget CommRingCat)).obj A')
      (hz : ∀ U t, z.hom.app U t = c U) :
      L.map z ≫ r = toUnit (L.obj T) ≫ o := by
    have hqz := reconstructed_constant Y A' q o' c ho T z hz
    have ha : z ≫ a.hom =
        toUnit T ≫ (preservesTerminalIso G.functor).inv ≫ G.functor.map o := by
      change z ≫ (q.inv ≫ d.hom) = _
      rw [← Category.assoc, hqz, Category.assoc, hc]
    change L.map z ≫ L.map a.hom ≫ adj.counit.app X.X = _
    rw [← Category.assoc, ← L.map_comp, ha]
    exact adj.counit_constant o T
  have hbinary (o : X.X ⊗ X.X ⟶ X.X) (o' : Y.X ⊗ Y.X ⟶ Y.X)
      (hc : o' ≫ d.hom = (d.hom ⊗ₘ d.hom) ≫
        (prodComparisonIso G.functor X.X X.X).inv ≫ G.functor.map o)
      (c : ∀ U : Dᵒᵖ, A'.obj.obj U → A'.obj.obj U → A'.obj.obj U)
      (ho : ∀ U x y, q.hom.hom.app U (o'.hom.app U (x,y)) =
        c U (q.hom.hom.app U x) (q.hom.hom.app U y))
      (T : Sheaf K (Type u))
      (x y z : T ⟶ (sheafCompose K (forget CommRingCat)).obj A')
      (hz : ∀ U t, z.hom.app U t = c U (x.hom.app U t) (y.hom.app U t)) :
      L.map z ≫ r = lift (L.map x ≫ r) (L.map y ≫ r) ≫ o := by
    have hqz := reconstructed_binary Y A' q o' c ho x y z hz
    have ha : z ≫ a.hom = lift (x ≫ a.hom) (y ≫ a.hom) ≫
        (prodComparisonIso G.functor X.X X.X).inv ≫ G.functor.map o := by
      change z ≫ (q.inv ≫ d.hom) = _
      rw [← Category.assoc, hqz, Category.assoc, hc]
      simp only [lift_map_assoc]
      rfl
    change L.map z ≫ L.map a.hom ≫ adj.counit.app X.X = _
    rw [← Category.assoc, ← L.map_comp, ha]
    simpa only [r, Functor.map_comp, Category.assoc] using
      adj.counit_binary o (x ≫ a.hom) (y ≫ a.hom)
  let g : RingedToposMorphism.RingData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj A') :=
    { inverse := L
      direct := G.functor
      adj := adj
      leftExact := inferInstance
      ringMap := r
      ring_zero := by
        intro T z hz U t
        have hh := hconst (AddMonObj.zero (X := X.X)) (AddMonObj.zero (X := Y.X))
          (hops X).2.1 (fun W ↦ (0 : A'.obj.obj W)) (fun W ↦ (hqops W).2.1) T z hz
        exact congrArg (fun k ↦ k.hom.app U t) hh
      ring_one := by
        intro T z hz U t
        have hh := hconst (MonObj.one (X := X.X)) (MonObj.one (X := Y.X))
          (hops X).2.2.2.2 (fun W ↦ (1 : A'.obj.obj W))
          (fun W ↦ (hqops W).2.2.2.2) T z hz
        exact congrArg (fun k ↦ k.hom.app U t) hh
      ring_add := by
        intro T x y z hz U t
        have hh := hbinary (AddMonObj.add (X := X.X)) (AddMonObj.add (X := Y.X))
          (hops X).1 (fun W ↦ @Add.add (A'.obj.obj W) inferInstance)
          (fun W ↦ (hqops W).1) T x y z hz
        exact congrArg (fun k ↦ k.hom.app U t) hh
      ring_mul := by
        intro T x y z hz U t
        have hh := hbinary (MonObj.mul (X := X.X)) (MonObj.mul (X := Y.X))
          (hops X).2.2.2.1 (fun W ↦ @Mul.mul (A'.obj.obj W) inferInstance)
          (fun W ↦ (hqops W).2.2.2.1) T x y z hz
        exact congrArg (fun k ↦ k.hom.app U t) hh }
  refine ⟨A', g, a, rfl, rfl, rfl, ?_⟩
  change IsIso (L.map a.hom ≫ adj.counit.app X.X)
  infer_instance

end CategoryTheory
