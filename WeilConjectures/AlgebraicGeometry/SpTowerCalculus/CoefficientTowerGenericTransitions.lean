/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def quotientDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (SpTowerShriek.R l E n.unop)
  map f := CommRingCat.ofHom (quotient l E (leOfHom f.unop))
  map_id n := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The generic sequence-site coefficient map is the actual ideal quotient map.
Source: Zheng 4.1; blueprint coefficient convention.
Proof: identity components compare the adjacent-map sequence with the recorded
coefficient diagram. Naturality identifies its map at every interval, and the
section-coordinate coefficient equality identifies this with the ideal quotient.
(blueprint: lem-sp-tower-generic-coefficient-map). -/
theorem genericCoefficientMap_eq (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h =
      proEtaleConstantRingMap (T := T) (quotient l E h) := by
  let : HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  let L : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
    { obj := fun A ↦ CommRingCat.of (ULift.{u + 1} A)
      map := fun f ↦ CommRingCat.ofHom (RingHom.ulift f.hom) }
  let G : CommRingCat.{u} ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
    L ⋙ constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology T) CommRingCat.{u + 1}
  let t : SemilinearSections.rings (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⟶ quotientDiagram l E ⋙ G := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 _) ?_
    intro n
    simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
      Functor.comp_map, Category.comp_id, Category.id_comp]
    dsimp only [G, L, Functor.comp_map]
    unfold SpTowerShriek.tau spCoefficientCommRings
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  exact (Category.comp_id _).symm.trans
    ((t.naturality (homOfLE h).op).trans (Category.id_comp _))

/-- The actual generic strict transition, in intrinsic restriction coordinates.
Source: Zheng 4.1 (blueprint: lem-sp-tower-generic-coefficient-map). -/
def genericIntrinsicTransitions (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.Ev l E T n ⟶ SpTowerShriek.Ev l E T m ⋙
      scalarRestriction (quotient l E h) T :=
  SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h ≫
    Functor.whiskerLeft (SpTowerShriek.Ev l E T m)
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg SemilinearSections.res (genericCoefficientMap_eq l E T h)))).hom

end AlgebraicGeometry.ProEtale.SpTowerCalculus
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
