/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.HaarIntegralSections
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Fibrewise `ℓ`-adic Haar integration is `ℤ_[ℓ]̲`-linear

Let `G` be a compact totally disconnected group all of whose open normal subgroups have index
invertible in `ℤ_[ℓ]`, and let `Λ := C(-, ℤ_[ℓ])` be the condensed ring `ℤ_[ℓ]̲`. The constant
functions `ℤ_[ℓ] → C(G, ℤ_[ℓ])` induce a morphism of ring objects
`Λ ⟶ C(-, C(G, ℤ_[ℓ]))`, along which the regular module `C(-, C(G, ℤ_[ℓ]))` becomes a
`Λ`-module object. This file shows that the Haar integration
`Profinite.haarIntegralCondensedMap : C(-, C(G, ℤ_[ℓ])) ⟶ Λ` is `Λ`-linear: on sections over
`S`, `∫ (a(s) • f(s, ·)) = a(s) • ∫ f(s, ·)` for `a : C(S, ℤ_[ℓ])`.

The general mechanism is the following. For a morphism of sheaves of rings `φ : S ⟶ T` and a
morphism `ψ : T ⟶ S` of the underlying abelian sheaves which is `S`-linear on sections, the
square `(φ ▷ T ≫ μ[T]) ≫ ψ = S ◁ ψ ≫ μ[S]` of abelian sheaves commutes
(`CategoryTheory.Sheaf.sheafCompose_map_whiskerRight_mul_comp`). It is checked on presheaves,
where the tensor product is objectwise, and transported through sheafification.

## Main results

* `Profinite.haarIntegralCondensedMap_linear`: the commutative square
  `(φ ▷ C(-, C(G, ℤ_[ℓ])) ≫ μ) ≫ ∫ = Λ ◁ ∫ ≫ μ[Λ]`, for `φ` the constant functions.
* `Profinite.haarIntegralModHom`: the Haar integration as a morphism of `Λ`-module objects
  from the restriction of scalars of the regular module `C(-, C(G, ℤ_[ℓ]))` to the regular
  module `Λ`.
* `Profinite.constModHom_comp_haarIntegralModHom`: it is a retraction of the `Λ`-linear map
  induced by the constant functions.
-/

@[expose] public section

universe w u v

open CategoryTheory MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.MonObj

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The image of a "linearity square" `(φ ▷ Q ≫ μ) ≫ ψ = P ◁ ψ ≫ μ` under a lax monoidal
functor is again a linearity square. -/
lemma map_whiskerRight_mul_comp {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {P Q : C} [MonObj P] [MonObj Q] (φ : P ⟶ Q) (ψ : Q ⟶ P)
    (h : (φ ▷ Q ≫ μ) ≫ ψ = P ◁ ψ ≫ μ) :
    (F.map φ ▷ F.obj Q ≫ μ) ≫ F.map ψ = F.obj P ◁ F.map ψ ≫ μ := by
  simp only [Category.assoc] at h
  simp only [Functor.obj.μ_def, Category.assoc, μ_natural_left_assoc, μ_natural_right_assoc,
    ← F.map_comp, h]

/-- A linearity square `(φ ▷ Q ≫ μ) ≫ ψ = P ◁ ψ ≫ μ` is invariant under conjugation by
isomorphisms of monoid objects. -/
lemma whiskerRight_mul_comp_conj {P Q P' Q' : C} [MonObj P] [MonObj Q] [MonObj P'] [MonObj Q']
    (eP : P ≅ P') (eQ : Q ≅ Q') [IsMonHom eP.hom] [IsMonHom eQ.hom] (φ : P ⟶ Q) (ψ : Q ⟶ P)
    (h : (φ ▷ Q ≫ μ) ≫ ψ = P ◁ ψ ≫ μ) :
    ((eP.inv ≫ φ ≫ eQ.hom) ▷ Q' ≫ μ) ≫ eQ.inv ≫ ψ ≫ eP.hom =
      P' ◁ (eQ.inv ≫ ψ ≫ eP.hom) ≫ μ := by
  rw [← cancel_epi (eP.hom ⊗ₘ eQ.hom)]
  have k₁ : (eP.hom ⊗ₘ eQ.hom) ≫ (eP.inv ≫ φ ≫ eQ.hom) ▷ Q' = φ ▷ Q ≫ (eQ.hom ⊗ₘ eQ.hom) := by
    rw [tensorHom_def', tensorHom_def, Category.assoc, ← comp_whiskerRight,
      Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, whisker_exchange]
  have k₂ : (eP.hom ⊗ₘ eQ.hom) ≫ P' ◁ (eQ.inv ≫ ψ ≫ eP.hom) = P ◁ ψ ≫ (eP.hom ⊗ₘ eP.hom) := by
    rw [tensorHom_def, tensorHom_def', Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange]
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% k₁, reassoc_of% k₂, ← IsMonHom.mul_hom_assoc, ← IsMonHom.mul_hom,
    Iso.hom_inv_id_assoc, reassoc_of% h]

end CategoryTheory.MonObj

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ RingCat.{w}}

/-- For a morphism of functors to rings `φ : P ⟶ Q` and a morphism `ψ : Q ⟶ P` of the underlying
functors to abelian groups which is `P`-linear objectwise, the linearity square
`(φ ▷ Q ≫ μ) ≫ ψ = P ◁ ψ ≫ μ` of monoid objects of `C ⥤ Ab` commutes. -/
lemma whiskerRight_forget₂_mul_comp (φ : P ⟶ Q)
    (ψ : Q ⋙ forget₂ RingCat.{w} Ab.{w} ⟶ P ⋙ forget₂ RingCat.{w} Ab.{w})
    (h : ∀ (X : C) (a : P.obj X) (b : Q.obj X),
      ψ.app X (φ.app X a * b) = a * (show P.obj X from ψ.app X b)) :
    (Functor.whiskerRight φ (forget₂ RingCat.{w} Ab.{w}) ▷ (Q ⋙ forget₂ RingCat.{w} Ab.{w}) ≫
        μ) ≫ ψ = (P ⋙ forget₂ RingCat.{w} Ab.{w}) ◁ ψ ≫ μ := by
  ext X : 2
  exact AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ h X a b)

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- For a morphism of sheaves of rings `φ : S ⟶ T` and a morphism `ψ : T ⟶ S` of the underlying
abelian sheaves which is `S`-linear on sections, the linearity square
`(φ ▷ T ≫ μ[T]) ≫ ψ = S ◁ ψ ≫ μ[S]` of ring objects of abelian sheaves commutes. -/
lemma sheafCompose_map_whiskerRight_mul_comp {S T : Sheaf J RingCat.{w}} (φ : S ⟶ T)
    (ψ : (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj T ⟶
      (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
    (h : ∀ (U : Cᵒᵖ) (a : S.obj.obj U) (b : T.obj.obj U),
      ψ.hom.app U (φ.hom.app U a * b) = a * (show S.obj.obj U from ψ.hom.app U b)) :
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map φ ▷ _ ≫ μ) ≫ ψ = _ ◁ ψ ≫ μ := by
  have hψ : ψ = (sheafifyRingPresheafIso J T).inv ≫ (presheafToSheaf J Ab.{w}).map ψ.hom ≫
      (sheafifyRingPresheafIso J S).hom := by
    rw [Iso.eq_inv_comp]
    exact ((sheafificationAdjunction J Ab.{w}).counit.naturality ψ).symm
  rw [sheafCompose_map_eq, hψ]
  exact MonObj.whiskerRight_mul_comp_conj _ _ _ _
    (MonObj.map_whiskerRight_mul_comp _ _ _
      (Functor.whiskerRight_forget₂_mul_comp φ.hom ψ.hom h))

end CategoryTheory.Sheaf

namespace Profinite

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Sectionwise linearity of the Haar integration.** On sections over `S`,
`∫ (a(s) • f(s, ·)) = a(s) • ∫ f(s, ·)` for `a : C(S, ℤ_[ℓ])` and `f : C(S, C(G, ℤ_[ℓ]))`. -/
lemma haarIntegralCondensedMap_app_mul
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, ℤ_[ℓ]))
    (f : ULift.{u + 1} C(S.unop, C(G, ℤ_[ℓ]))) :
    (haarIntegralCondensedMap hG).hom.app S
        ((show ULift.{u + 1} C(S.unop, C(G, ℤ_[ℓ])) from
          (continuousMapRingSheafMap.{u} (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
            continuous_algebraMap_continuousMap).hom.app S a) * f) =
      a * (show ULift.{u + 1} C(S.unop, ℤ_[ℓ]) from (haarIntegralCondensedMap hG).hom.app S f) :=
  ULift.ext _ _ (ContinuousMap.ext fun s ↦
    (congrArg (ProPGroup.haarIntegralOfIsUnit hG)
      (Algebra.smul_def (a.down s) (f.down s)).symm).trans (map_smul _ _ _))

/-- **The Haar integration is `ℤ_[ℓ]̲`-linear.** With `φ : ℤ_[ℓ]̲ ⟶ C(-, C(G, ℤ_[ℓ]))` induced
by the constant functions, the square `(φ ▷ C(-, C(G, ℤ_[ℓ])) ≫ μ) ≫ ∫ = ℤ_[ℓ]̲ ◁ ∫ ≫ μ`
of condensed abelian groups commutes. -/
lemma haarIntegralCondensedMap_linear
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    (continuousMapRingObjMap.{u} (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
        continuous_algebraMap_continuousMap ▷ continuousMapRingObj C(G, ℤ_[ℓ]) ≫ μ) ≫
      haarIntegralCondensedMap hG =
    continuousMapRingObj ℤ_[ℓ] ◁ haarIntegralCondensedMap hG ≫ μ :=
  Sheaf.sheafCompose_map_whiskerRight_mul_comp (coherentTopology Profinite.{u})
    (continuousMapRingSheafMap _ _) (haarIntegralCondensedMap hG)
    (haarIntegralCondensedMap_app_mul hG)

/-- The constant functions `ℤ_[ℓ] → C(G, ℤ_[ℓ])`, as a morphism of `ℤ_[ℓ]̲`-module objects from
the regular module `ℤ_[ℓ]̲` to the restriction of scalars of the regular module
`C(-, C(G, ℤ_[ℓ]))`. -/
noncomputable def constModHom :
    Mod.regular (continuousMapRingObj.{u} ℤ_[ℓ]) ⟶
      (Mod.comap (continuousMapRingObjMap.{u} (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
        continuous_algebraMap_continuousMap)).obj (Mod.regular (continuousMapRingObj _)) :=
  Mod.Hom.mk' (continuousMapRingObjMap (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
      continuous_algebraMap_continuousMap)
    ((IsMonHom.mul_hom _).trans ((eq_whisker (tensorHom_def' _ _)
      μ[continuousMapRingObj C(G, ℤ_[ℓ])]).trans (Category.assoc _ _ _)))

/-- **The Haar integration as a morphism of `ℤ_[ℓ]̲`-module objects** from the restriction of
scalars of the regular module `C(-, C(G, ℤ_[ℓ]))` to the regular module `ℤ_[ℓ]̲`. -/
noncomputable def haarIntegralModHom
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    (Mod.comap (continuousMapRingObjMap.{u} (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
        continuous_algebraMap_continuousMap)).obj (Mod.regular (continuousMapRingObj _)) ⟶
      Mod.regular (continuousMapRingObj.{u} ℤ_[ℓ]) :=
  Mod.Hom.mk' (haarIntegralCondensedMap hG) (haarIntegralCondensedMap_linear hG)

/-- The underlying morphism of `haarIntegralModHom` is `haarIntegralCondensedMap`. -/
lemma haarIntegralModHom_hom
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    (haarIntegralModHom.{u} hG).hom = haarIntegralCondensedMap hG :=
  rfl

/-- The Haar integration is a retraction, as a morphism of `ℤ_[ℓ]̲`-module objects, of the
morphism induced by the constant functions. -/
lemma constModHom_comp_haarIntegralModHom
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    constModHom.{u} ≫ haarIntegralModHom hG = 𝟙 _ :=
  Mod.hom_ext _ _ (continuousMapRingObjMap_const_comp_haarIntegralCondensedMap hG)

end Profinite
