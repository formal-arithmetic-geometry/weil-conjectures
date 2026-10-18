/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# Restriction of sections of homology sheaves over a strictly henselian local ring

Let `R` be a strictly henselian local ring with closed point `s₀ : Spec κ ⟶ Spec R`, let
`t : Spec Ω ⟶ Spec R` be a geometric point and `K ∈ D⁺((Spec R)_ét, Λ)`. If the pullback to the
closed point of the unit `K ⟶ Rt_* t^* K` is an isomorphism, then for every `q` the restriction
of global sections `Γ(Spec R, Hᵠ(K)) ⟶ Γ(Spec Ω, t^* Hᵠ(K))` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- A separably closed field is a strictly henselian local ring. -/
theorem IsStrictlyHenselianLocalRing.of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] :
    IsStrictlyHenselianLocalRing K :=
  ⟨IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue K)
    ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩)⟩

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The isomorphism `H^n(F(A)[-n]) ≅ F(H^n(A[-n]))` given by
`F.mapDerivedCategoryPlusSingleFunctor` and `F.mapDerivedCategoryPlusHomologyFunctorIso` is
compatible with the identifications `A ≅ H^n(A[-n])`. -/
@[reassoc]
lemma mapDerivedCategoryPlusHomologyFunctorIso_inv_app_singleFunctor (n : ℤ) (A : C) :
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (F.obj A) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        ((F.mapDerivedCategoryPlusSingleFunctor n).inv.app A) ≫
      (F.mapDerivedCategoryPlusHomologyFunctorIso n).inv.app
        ((DerivedCategory.Plus.singleFunctor C n).obj A) =
    F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app A) := by
  rw [← cancel_mono (F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app
    A)), ← F.map_comp, Iso.inv_hom_id_app,
    ← F.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor n A]
  simp [← Functor.map_comp_assoc]

/-- For `i : B ⟶ F(A)` and `β : A[0] ⟶ L`, the morphism `B ⟶ F(H⁰(L))` given by
`B ⟶ F(A) ≅ F(H⁰(A[0])) ⟶ F(H⁰(L))` is the one given by `B ≅ H⁰(B[0])` and `H⁰` of
`B[0] ⟶ F(A)[0] ≅ F(A[0]) ⟶ F(L)`, followed by `H⁰(F(L)) ≅ F(H⁰(L))`. -/
lemma comp_map_singleFunctorCompHomologyFunctorIso_inv_app {A : C} {B : D} (i : B ⟶ F.obj A)
    {L : DerivedCategory.Plus C} (β : (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶ L) :
    i ≫ F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map β) =
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app B ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((DerivedCategory.Plus.singleFunctor D 0).map i ≫
          (F.mapDerivedCategoryPlusSingleFunctor 0).inv.app A ≫ F.mapDerivedCategoryPlus.map β)) ≫
      (F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app L := by
  have n := (F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.naturality β
  rw [Functor.comp_map, Functor.comp_map] at n
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, n, ← mapDerivedCategoryPlusHomologyFunctorIso_inv_app_singleFunctor_assoc]
  have n' := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D) 0).inv.naturality i
  rw [Functor.id_map, Functor.comp_map] at n'
  rw [reassoc_of% n']

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

section DerivedSections

/-- The defining formula of `AlgebraicGeometry.Etale.derivedHomToSections`. -/
lemma Etale.derivedHomToSections_eq {X : Scheme.{u}} (W : X.Etale)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    Etale.derivedHomToSections W L β = Etale.freeSheafHomEquiv Λ W _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((Etale.freeSheaf Λ X).obj W) ≫ (DerivedCategory.Plus.homologyFunctor _ 0).map β) :=
  rfl

/-- Naturality of `AlgebraicGeometry.Etale.derivedHomToSections` in the étale `X`-scheme: for
`v : W' ⟶ W`, the section over `W'` induced by `Λ[W'][0] ⟶ Λ[W][0] ⟶ L` is the restriction
of the section over `W` induced by `Λ[W][0] ⟶ L`. -/
lemma Etale.derivedHomToSections_map {X : Scheme.{u}} {W W' : X.Etale} (v : W' ⟶ W)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    Etale.derivedHomToSections W' L
        ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ X).map v) ≫ β) =
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj L).obj.map v.op
        (Etale.derivedHomToSections W L β) := by
  rw [Etale.derivedHomToSections, Etale.derivedHomToSections, ← Etale.freeSheafHomEquiv_map,
    Functor.map_comp]
  congr 1
  exact ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.naturality_assoc _
    _).symm

/-- The map `AlgebraicGeometry.Etale.derivedHomToSections` is bijective at `W'` as soon as it
is bijective at some `W ≅ W'`. -/
lemma Etale.bijective_derivedHomToSections_of_iso {X : Scheme.{u}} {W W' : X.Etale}
    (v : W' ≅ W) (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : Function.Bijective (Etale.derivedHomToSections W L)) :
    Function.Bijective (Etale.derivedHomToSections W' L) := by
  have key : Etale.derivedHomToSections W' L ∘
      (fun β ↦ (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.freeSheaf Λ X).map v.hom) ≫ β) =
      ⇑(((DerivedCategory.Plus.homologyFunctor _ 0).obj L).obj.map v.hom.op) ∘
        Etale.derivedHomToSections W L :=
    funext fun β ↦ Etale.derivedHomToSections_map v.hom L β
  rw [← Function.Bijective.of_comp_iff _
    ⟨fun _ _ hab ↦ (cancel_epi _).1 hab, fun γ ↦ ⟨inv ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((Etale.freeSheaf Λ X).map v.hom)) ≫ γ, IsIso.hom_inv_id_assoc _ _⟩⟩, key]
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp h

/-- Over a strictly henselian local ring `R`, the sections over the terminal object `⊤_` of the
small étale site of `Spec R` of `H⁰(L)` are the morphisms `Λ[⊤_][0] ⟶ L`. -/
lemma Etale.bijective_derivedHomToSections_terminal (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R]
    (L : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (Etale.derivedHomToSections (⊤_ (Spec (.of R)).Etale) L) :=
  Etale.bijective_derivedHomToSections_of_iso
    (terminalIsTerminal.uniqueUpToIso (Scheme.isTerminalEtaleTerminal R)) L
    (Etale.bijective_derivedHomToSections R L)

/-- The free sheaf `Λ[W ×_X Y]` maps to `h^* Λ[W]` by the inverse of
`AlgebraicGeometry.Etale.upperStarFreeSheafIso`, which is the image of the identity under
`AlgebraicGeometry.Etale.upperStarFreeSheafHomEquiv`. -/
lemma Etale.upperStarFreeSheafIso_inv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (Etale.upperStarFreeSheafIso Λ h W).inv = Etale.upperStarFreeSheafHomEquiv Λ h W _ (𝟙 _) :=
  rfl

/-- Sections over `W ×_X Y` corresponding to morphisms `Λ[W ×_X Y] ⟶ G` under
`AlgebraicGeometry.Etale.upperStarFreeSheafHomEquiv` are those of `h_* G` over `W`
corresponding to the adjoint morphisms `Λ[W] ⟶ h_* G`. -/
lemma Etale.freeSheafHomEquiv_upperStarFreeSheafHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X)
    (W : X.Etale) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) :
    Etale.freeSheafHomEquiv Λ (h.Etale.obj W) G (Etale.upperStarFreeSheafHomEquiv Λ h W G a) =
      Etale.freeSheafHomEquiv Λ W _ ((upperStarLowerStarAdjunction _ h).homEquiv _ _ a) :=
  Equiv.apply_symm_apply _ _

/-- The section over `W` of `h_* h^* G` given by the composite of `a : Λ[W] ⟶ G` with the unit
of `h^* ⊣ h_*` is the section over `W ×_X Y` of `h^* G` given by
`Λ[W ×_X Y] ≅ h^* Λ[W] ⟶ h^* G`. -/
lemma Etale.freeSheafHomEquiv_comp_unit {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W _ (a ≫ (upperStarLowerStarAdjunction _ h).unit.app G) =
      Etale.freeSheafHomEquiv Λ (h.Etale.obj W) _
        ((Etale.upperStarFreeSheafIso Λ h W).inv ≫ (h)^*[ModuleCat.{u + 1} Λ].map a) := by
  rw [Etale.upperStarFreeSheafIso_inv, ← Etale.upperStarFreeSheafHomEquiv_comp, Category.id_comp,
    Etale.freeSheafHomEquiv_upperStarFreeSheafHomEquiv, Adjunction.homEquiv_unit,
    Adjunction.unit_naturality]

/-- The pullback along `m : Y ⟶ X` of the section over `W` of `H⁰(L)` induced by
`β : Λ[W][0] ⟶ L` is the section over `W ×_X Y` of `H⁰(m^* L) ≅ m^* H⁰(L)` induced by
`Λ[W ×_X Y][0] ≅ m^*(Λ[W][0]) ⟶ m^* L`. -/
lemma Etale.upperStarLowerStarAdjunction_unit_app_derivedHomToSections {X Y : Scheme.{u}}
    (m : Y ⟶ X) (W : X.Etale)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) m).unit.app
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)).hom.app (op W)
        (Etale.derivedHomToSections W L β) =
      ((((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
        L).hom.app (op (m.Etale.obj W))
        (Etale.derivedHomToSections _ (D+((m)^*[ModuleCat.{u + 1} Λ]).obj L)
          ((DerivedCategory.Plus.singleFunctor _ 0).map (Etale.upperStarFreeSheafIso Λ m W).inv ≫
            (((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
            D+((m)^*[ModuleCat.{u + 1} Λ]).map β)) := by
  rw [Etale.derivedHomToSections_eq, Etale.derivedHomToSections_eq]
  erw [← Etale.freeSheafHomEquiv_comp, ← Etale.freeSheafHomEquiv_comp]
  rw [Etale.freeSheafHomEquiv_comp_unit,
    Functor.comp_map_singleFunctorCompHomologyFunctorIso_inv_app]

end DerivedSections

/-- **Restriction of sections of homology sheaves to a geometric point of a strictly local
scheme.** Let `R` be a strictly henselian local ring, `t : Spec Ω ⟶ Spec R` a geometric point
and `K ∈ D⁺((Spec R)_ét, Λ)` such that the restriction to the closed point of the unit
`K ⟶ Rt_* t^* K` is an isomorphism. Then for every `q` the pullback of global sections
`Γ(Spec R, Hᵠ(K)) ⟶ Γ(Spec Ω, t^* Hᵠ(K))` is an isomorphism. -/
theorem Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (K : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app K)))
    (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
  sorry

end AlgebraicGeometry
