/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints

/-!
# The derivation given by a mixed infinitesimal coefficient

Source: Milne, Algebraic Groups (2017), Chapter 10, infinitesimal points and commutators.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- A point trivial on both axes has a relative derivation as its mixed coefficient.

Source: Milne, Algebraic Groups (2017), Chapter 10, infinitesimal points and commutators.
(blueprint: lem-ag-mixed-coefficient-derivation)

Proof: write each section image as a + εb + δc + εδd. Reduction along the two axes is
constant, so b = c = 0 and a is the pullback along the reduced point g. Additivity and
naturality of d follow by extracting the mixed coefficient of the ring maps and their
restriction squares. Extracting that coefficient from the product gives
 d(xy) = g♯(x)d(y) + g♯(y)d(x), since the two cross terms b(x)c(y) and c(x)b(y) vanish.
Finally functions pulled back from the base have only a constant coefficient, because z
is a morphism over S. Thus d kills the image of the base presheaf. These three calculations
supply the additive maps, the Leibniz law, restriction compatibility and base annihilation
of the relative presheaf derivation. The displayed formula determines every component of D,
so the theorem postpones only the verification of this particular derivation. -/
theorem exists_mixedCoefficientDerivation {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (z : Scheme.dualNumbers₂Over S ⟶ G)
    (hε : Scheme.dualNumbersιεOver S ≫ z = 1)
    (hδ : Scheme.dualNumbersιδOver S ≫ z = 1) :
    ∃ D : ((Scheme.Modules.pushforward
        (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.left)).obj
          (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom,
      ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)),
        D.d a = (z.left.app V.unop a).snd.snd := by
  have hzε (U : G.left.Opens) (a : Γ(G.left, U)) : (z.left.app U a).fst.snd = 0 := by
    have h := congrArg (fun f ↦ f.left) hε
    have he := congrArg snd (ConcreteCategory.congr_hom (Scheme.Hom.congr_app h U) a)
    simp only [Over.comp_left, Scheme.Hom.comp_app, CommRingCat.comp_apply] at he
    simp only [Hom.one_def, Over.comp_left, Over.toUnit_left,
      Scheme.Hom.comp_app, CommRingCat.comp_apply] at he
    let i : z.left ⁻¹ᵁ U ⟶ unitSection G ⁻¹ᵁ U :=
      eqToHom (congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U)
        (congrArg (fun f ↦ f.base) h))
    change (z.left.app U a).fst.snd =
      (DualNumber.mapRingHom (S.presheaf.map i.op).hom
        (inl ((unitSection G).app U a))).snd at he
    simpa only [DualNumber.snd_mapRingHom, snd_inl, map_zero] using he
  have hzδ (U : G.left.Opens) (a : Γ(G.left, U)) : (z.left.app U a).snd.fst = 0 := by
    have h := congrArg (fun f ↦ f.left) hδ
    have he := congrArg snd (ConcreteCategory.congr_hom (Scheme.Hom.congr_app h U) a)
    simp only [Over.comp_left, Scheme.Hom.comp_app, CommRingCat.comp_apply] at he
    simp only [Hom.one_def, Over.comp_left, Over.toUnit_left,
      Scheme.Hom.comp_app, CommRingCat.comp_apply] at he
    let i : z.left ⁻¹ᵁ U ⟶ unitSection G ⁻¹ᵁ U :=
      eqToHom (congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U)
        (congrArg (fun f ↦ f.base) h))
    change (DualNumber.mapRingHom
      (fstHom Γ(S, z.left ⁻¹ᵁ U) Γ(S, z.left ⁻¹ᵁ U)
        Γ(S, z.left ⁻¹ᵁ U)).toRingHom (z.left.app U a)).snd =
      (DualNumber.mapRingHom (S.presheaf.map i.op).hom
        (inl ((unitSection G).app U a))).snd at he
    simp only [DualNumber.snd_mapRingHom, snd_inl, map_zero] at he
    exact he
  let D : ((Scheme.Modules.pushforward
      (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.left)).obj
        (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom :=
    { d := fun {V} ↦
        { toFun := fun a ↦ (z.left.app V.unop a).snd.snd
          map_zero' := by rw [map_zero]; rfl
          map_add' := fun a b ↦ by rw [map_add]; rfl }
      d_mul := fun {V} a b ↦ by
        change (z.left.app V.unop (a * b)).snd.snd =
          (z.left.app V.unop a).fst.fst * (z.left.app V.unop b).snd.snd +
            (z.left.app V.unop b).fst.fst * (z.left.app V.unop a).snd.snd
        rw [map_mul]
        change ((z.left.app V.unop a).fst.fst * (z.left.app V.unop b).snd.snd +
          (z.left.app V.unop a).fst.snd * (z.left.app V.unop b).snd.fst) +
          ((z.left.app V.unop a).snd.fst * (z.left.app V.unop b).fst.snd +
          (z.left.app V.unop a).snd.snd * (z.left.app V.unop b).fst.fst) = _
        rw [hzε, hzδ, hzδ]
        simp only [zero_mul, mul_zero, add_zero, zero_add]
        rw [mul_comm (z.left.app V.unop a).snd.snd]
      d_map := fun {X Y} f a ↦ by
        have h := ConcreteCategory.congr_hom (z.left.c.naturality f) a
        have h' := congrArg (fun x ↦ x.snd.snd) h
        simp only [CommRingCat.comp_apply] at h'
        change (z.left.app Y.unop (G.left.presheaf.map f a)).snd.snd =
          (DualNumber.mapRingHom
            (DualNumber.mapRingHom
              (S.presheaf.map ((TopologicalSpace.Opens.map z.left.base).map f.unop).op).hom)
              (z.left.app X.unop a)).snd.snd at h'
        rw [DualNumber.snd_mapRingHom, DualNumber.snd_mapRingHom] at h'
        exact h'
      d_app := fun {X} a ↦ by
        let α : CommRingCat.dualNumber ⋙ CommRingCat.dualNumber ⟶
            CommRingCat.dualNumber ⋙ CommRingCat.dualNumber :=
          Functor.whiskerLeft CommRingCat.dualNumber CommRingCat.dualNumberFst ≫
            CommRingCat.dualNumberFst ≫ CommRingCat.dualNumberInl ≫
              Functor.whiskerLeft CommRingCat.dualNumber CommRingCat.dualNumberInl
        let ε₀ := Functor.whiskerLeft
          ((TopologicalSpace.Opens.map z.left.base).op ⋙ S.presheaf) α
        have key : (G.hom.pullbackPresheafHom ≫ z.left.c) ≫ ε₀ =
            G.hom.pullbackPresheafHom ≫ z.left.c := by
          simp only [Scheme.Hom.pullbackPresheafHom,
            ← Adjunction.homEquiv_naturality_right_symm]
          congr 1
          ext U b
          change inl (inl ((z.left ≫ G.hom).app U b).fst.fst) =
            (z.left ≫ G.hom).app U b
          rw [Scheme.Hom.congr_app (Over.w z) U]
          let i : (z.left ≫ G.hom) ⁻¹ᵁ U ⟶ U :=
            eqToHom (congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U)
              (congrArg (fun f ↦ f.base) (Over.w z)))
          change inl (inl (DualNumber.mapRingHom
            (DualNumber.mapRingHom (S.presheaf.map i.op).hom) (inl (inl b))).fst.fst) =
              DualNumber.mapRingHom
                (DualNumber.mapRingHom (S.presheaf.map i.op).hom) (inl (inl b))
          apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext <;> simp
        have h := ConcreteCategory.congr_hom (congr_app key X) a
        have h' := congrArg (fun x ↦ x.snd.snd) h
        change (inl (inl _ : DualNumber _) : DualNumber (DualNumber _)).snd.snd =
          (z.left.app X.unop (G.hom.pullbackPresheafHom.app X a)).snd.snd at h'
        exact h'.symm.trans rfl }
  exact ⟨D, fun a ↦ rfl⟩

end AlgebraicGeometry.GrpObj
