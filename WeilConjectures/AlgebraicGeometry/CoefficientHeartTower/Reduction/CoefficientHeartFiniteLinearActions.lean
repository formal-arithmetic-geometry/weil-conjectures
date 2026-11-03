/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.CoefficientHeartFiniteGerms
import Mathlib.CategoryTheory.Galois.GaloisObjects

/-! # Linearity of the prescribed finite stalk actions

Source: coefficient-heart proof (1), the finite Galois actions on quotient stalks.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}}
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
variable {pi : A} {M : Modules A X}

private def setSectionMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (U : X.Etale) (z : F.obj.obj (op U)) :
    X.smallEtaleTopology.uliftYoneda.{u + 1}.obj U ⟶ (etaleSet A X).obj F :=
  ⟨{ app V := ↾fun f ↦ F.obj.map f.down.op z
     naturality {V W} k := by
       ext f
       change F.obj.map (k.unop ≫ f.down).op z =
         F.obj.map k (F.obj.map f.down.op z)
       rw [op_comp, F.obj.map_comp]
       rfl }⟩

/-- Each prescribed finite action is induced by a deck map on a pointed Galois cover.
Source: coefficient-heart proof (1), the finite Galois correspondence.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: the automorphism sends the marked representable stalk element to another fibre
point of the Galois cover. Transitivity supplies a deck map carrying the marked point to
that point. Naturality for the Yoneda morphism associated to any module section identifies
the action on its germ with restriction along this deck map. The canonical forgetful
comparison gives the same equality in the module stalk. -/
theorem Reduction.finiteAction_deck (R : Reduction A X pi M)
    [ConnectedSpace X] (v : Spec (.of Ω) ⟶ X) (n : ℕ)
    (B : X.FiniteEtale) [IsGalois B]
    (b : (Scheme.FiniteEtale.fiber v).obj B) (g : Aut (Scheme.flcFiber v)) :
    ∃ σ : Aut B, ∀ z : (R.etale.obj (op n)).obj.obj (op B.obj),
      R.finiteAction A v g n (pointedEtaleGerm (R.etale.obj (op n)) v B.obj b z) =
        pointedEtaleGerm (R.etale.obj (op n)) v B.obj b
          ((R.etale.obj (op n)).obj.map σ.hom.hom.op z) := by
  classical
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let Φ := Scheme.pointSmallEtale v
  let F := R.etale.obj (op n)
  let H : X.FLC := ⟨(etaleSet A X).obj F, R.finiteLocallyConstant n⟩
  let J := (Scheme.FiniteEtale.toFLC X).obj B
  let d := (Scheme.FiniteEtale.toFLCCompSheafFiberIso v).app B
  let a := Φ.toPresheafFiber B.obj b J.obj.obj (ULift.up (𝟙 B.obj))
  have ha : d.hom a = ULift.up b := by
    exact (finiteEtale_germ v B B.obj b (𝟙 B.obj)).trans (by simp)
  obtain ⟨σ, hσ⟩ := evaluation_aut_surjective_of_isGalois
    (Scheme.FiniteEtale.fiber v) B b (d.hom (g.hom.app J a)).down
  have hg : g.hom.app J a =
      Φ.toPresheafFiber B.obj b J.obj.obj (ULift.up σ.hom.hom) := by
    apply d.toEquiv.injective
    change d.hom (g.hom.app J a) = d.hom _
    exact ((ULift.up_down (d.hom (g.hom.app J a))).symm.trans
      (congrArg ULift.up hσ.symm)).trans
        (finiteEtale_germ v B B.obj b σ.hom.hom).symm
  refine ⟨σ, ?_⟩
  intro z
  let q : J ⟶ H := ObjectProperty.homMk (setSectionMap F B.obj z)
  have hq (f : B.obj ⟶ B.obj) : Φ.sheafFiber.map q.hom
      (Φ.toPresheafFiber B.obj b J.obj.obj (ULift.up f)) =
      Φ.toPresheafFiber B.obj b H.obj.obj (F.obj.map f.op z) := by
    exact Φ.toPresheafFiber_naturality_apply q.hom.hom B.obj b
      (ULift.up f : ULift.{u + 1} (B.obj ⟶ B.obj))
  have hn := ConcreteCategory.congr_hom (g.hom.naturality q) a
  change g.hom.app H (Φ.sheafFiber.map q.hom a) =
    Φ.sheafFiber.map q.hom (g.hom.app J a) at hn
  have hqa : Φ.sheafFiber.map q.hom a = Φ.toPresheafFiber B.obj b H.obj.obj z := by
    have hh := hq (𝟙 B.obj)
    have hid : F.obj.map (𝟙 B.obj).op = 𝟙 _ :=
      (congrArg F.obj.map (op_id : (𝟙 B.obj).op = 𝟙 (op B.obj))).trans (F.obj.map_id _)
    rw [hid] at hh
    exact hh
  rw [hqa, hg, hq] at hn
  let c := (Φ.sheafFiberCompIso (forget (ModuleCat.{u + 1} A))).app F
  have hc (x : F.obj.obj (op B.obj)) :
      c.hom (Φ.toPresheafFiber B.obj b H.obj.obj x) = pointedEtaleGerm F v B.obj b x :=
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (forget (ModuleCat.{u + 1} A)) B.obj b F.obj) x
  change c.hom (g.hom.app H (c.inv (pointedEtaleGerm F v B.obj b z))) = _
  have hcancel := ConcreteCategory.congr_hom c.hom_inv_id
    (Φ.toPresheafFiber B.obj b H.obj.obj z)
  change c.inv (c.hom (Φ.toPresheafFiber B.obj b H.obj.obj z)) =
    Φ.toPresheafFiber B.obj b H.obj.obj z at hcancel
  rw [← hc z, hcancel, hn, hc]

/-- The underlying finite stalk action is A-linear.
Source: coefficient-heart proof (1), linear finite representations.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: choose a pointed Galois representative of the underlying finite sheaf. Its germ is
an A-linear isomorphism. The deck transformation formula expresses the action as this
isomorphism conjugating a restriction map, which is A-linear. -/
theorem Reduction.finiteAction_linear (R : Reduction A X pi M) [ConnectedSpace X]
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) (g : Aut (Scheme.flcFiber v)) :
    ∃ f : (R.fibres A v).obj (op n) ⟶ (R.fibres A v).obj (op n),
      ∀ p, f p = R.finiteAction A v g n p := by
  classical
  obtain ⟨P, e, _⟩ := exists_etaleRepresentative (R.etale.obj (op n))
    (R.finiteLocallyConstant n) v
  obtain ⟨B, b, hB, hb⟩ := exists_galois_representative (Scheme.FiniteEtale.fiber v) P
  let := hB
  let F := R.etale.obj (op n)
  let q := pointedEtaleGerm F v B.obj b
  let := etaleGerm_isIso_of_representative F v P B e.some b hb
  obtain ⟨σ, hσ⟩ := R.finiteAction_deck v n B b g
  refine ⟨inv q ≫ F.obj.map σ.hom.hom.op ≫ q, ?_⟩
  intro p
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso q).surjective p
  change q (F.obj.map σ.hom.hom.op (inv q (q z))) = _
  have he := ConcreteCategory.congr_hom (IsIso.hom_inv_id q) z
  change inv q (q z) = z at he
  rw [he]
  exact (hσ z).symm

/-- The prescribed finite actions preserve the identity element.
Source: identity natural automorphism of the finite fibre functor.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: conjugating the identity by the canonical forgetful stalk comparison is identity. -/
theorem Reduction.finiteAction_one (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) (p : (R.fibres A v).obj (op n)) :
    R.finiteAction A v 1 n p = p := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let c := ((Scheme.pointSmallEtale v).sheafFiberCompIso
    (forget (ModuleCat.{u + 1} A))).app (R.etale.obj (op n))
  change c.hom (c.inv p) = p
  exact ConcreteCategory.congr_hom c.inv_hom_id p

/-- The prescribed finite actions respect group multiplication.
Source: multiplication of natural automorphisms of the finite fibre functor.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: cancel the intervening forgetful stalk comparison and apply the component formula
for composition of the two natural automorphisms. -/
theorem Reduction.finiteAction_mul (R : Reduction A X pi M)
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) (g k : Aut (Scheme.flcFiber v))
    (p : (R.fibres A v).obj (op n)) :
    R.finiteAction A v (g * k) n p =
      R.finiteAction A v g n (R.finiteAction A v k n p) := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let c := ((Scheme.pointSmallEtale v).sheafFiberCompIso
    (forget (ModuleCat.{u + 1} A))).app (R.etale.obj (op n))
  let H : X.FLC := ⟨(etaleSet A X).obj (R.etale.obj (op n)),
    R.finiteLocallyConstant n⟩
  have hc := ConcreteCategory.congr_hom c.hom_inv_id (k.hom.app H (c.inv p))
  change c.inv (c.hom (k.hom.app H (c.inv p))) = k.hom.app H (c.inv p) at hc
  change c.hom (g.hom.app H (k.hom.app H (c.inv p))) =
    c.hom (g.hom.app H (c.inv (c.hom (k.hom.app H (c.inv p)))))
  rw [hc]

/-- The normalized finite stalk representation by actual linear automorphisms.
Source: coefficient-heart proof (1), finite fundamental-group representations.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: the deck-map argument supplies a linear morphism with the prescribed underlying
function for each group element. The inverse group element supplies its inverse. The
underlying action identities prove the two inverse equations and the monoid-hom laws. -/
def Reduction.finiteLinearAction (R : Reduction A X pi M) [ConnectedSpace X]
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) :
    Aut (Scheme.flcFiber v) →* Aut ((R.fibres A v).obj (op n)) := by
  classical
  choose f hf using R.finiteAction_linear v n
  exact {
    toFun g := {
      hom := f g
      inv := f g⁻¹
      hom_inv_id := by
        ext p
        change f g⁻¹ (f g p) = p
        rw [hf, hf, ← R.finiteAction_mul, inv_mul_cancel, R.finiteAction_one]
      inv_hom_id := by
        ext p
        change f g (f g⁻¹ p) = p
        rw [hf, hf, ← R.finiteAction_mul, mul_inv_cancel, R.finiteAction_one] }
    map_one' := by
      apply Iso.ext
      ext p
      exact (hf 1 p).trans (R.finiteAction_one v n p)
    map_mul' g k := by
      apply Iso.ext
      ext p
      change f (g * k) p = f g (f k p)
      rw [hf, hf, hf, R.finiteAction_mul] }

/-- The constructed representation has precisely the prescribed underlying finite action.
Source: coefficient-heart proof (1), fixed canonical action.
(blueprint: lem-sfb-coefficient-heart-finite-linear-actions)
Proof: this is the normalization of the chosen linear morphism in its construction. -/
theorem Reduction.finiteLinearAction_apply (R : Reduction A X pi M) [ConnectedSpace X]
    (v : Spec (.of Ω) ⟶ X) (n : ℕ) (g : Aut (Scheme.flcFiber v))
    (p : (R.fibres A v).obj (op n)) :
    (R.finiteLinearAction v n g).hom p = R.finiteAction A v g n p := by
  classical
  exact (Classical.choose_spec (R.finiteAction_linear v n g)) p

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
