/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftGeneratorPresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedLiftRelations

/-! # Closed-fibre inputs to the proper/open boundary calculation

Source: the local boundary calculation, Step 2 of
`lem-sp-proetale-proper-open-boundary-test-hypercohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem realization_directImage_sections_epi
    (A : Type u) [CommRing A] [Finite A]
    {B D : Scheme.{u}} (p : B ⟶ D) (W : D.ProEt)
    {M N : Sheaf (ProEt.topology B)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))} (f : M ⟶ N)
    (hf : Function.Surjective
      (f.hom.app ((proEtaleBaseChange p).op.obj (op W)))) :
    Epi ((SheafOfModules.evaluation _ (op W)).map
      ((proEtaleConstantModuleDirectImage p A).map
        ((sfIntrinsicModuleEquivalence B A).functor.map f))) := by
  let V := (proEtaleBaseChange p).op.obj (op W)
  let e := intrinsicUnitIso B A
  let ev := PresheafOfModules.evaluation
    ((Functor.const B.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A))) V
  have hf' : Epi (ev.map ((intrinsicEmbedding B A).map f)) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact hf
  have hn := congrArg ev.map (e.hom.naturality f)
  rw [ev.map_comp, ev.map_comp] at hn
  have : Epi (ev.map (e.hom.app M) ≫
      ev.map (((sfIntrinsicModuleEquivalence B A).functor ⋙ intrinsicRestriction B A).map f)) :=
    hn ▸ inferInstance
  have ht : Epi
      (ev.map (((sfIntrinsicModuleEquivalence B A).functor ⋙ intrinsicRestriction B A).map f)) :=
    epi_of_epi (ev.map (e.hom.app M)) _
  apply (ModuleCat.epi_iff_surjective _).mpr
  have hs := (ModuleCat.epi_iff_surjective
    (ev.map (((sfIntrinsicModuleEquivalence B A).functor ⋙ intrinsicRestriction B A).map f))).mp ht
  exact hs

private theorem lift_map_of_closedLift_relations
    (A : Type u) [CommRing A] {X Z U : Scheme.{u}}
    (z : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion z] [IsOpenImmersion j]
    [QuasiCompact j] (hpair : Set.range j = (Set.range z)ᶜ)
    (Q : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (hrel : Epi (closedLiftGeneratorAugmentation A z
      (kernel (closedLiftGeneratorAugmentation A z Q).hom)).hom)
    (I : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [Injective I]
    (f : (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z).obj Q ⟶
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z).obj I) :
    ∃ g : Q ⟶ I,
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z).map g = f := by
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) z
  let e := closedLiftGeneratorAugmentation A z Q
  let d := closedLiftGeneratorAugmentation A z (kernel e.hom)
  have : Epi d.hom := hrel
  obtain ⟨he, hC⟩ := closedLiftGeneratorPresentation A z j hpair Q
  have : Epi (L.map e.hom) := he
  obtain ⟨t, ht⟩ := (hC I).surjective (L.map e.hom ≫ f)
  change L.map t = L.map e.hom ≫ f at ht
  have hz : L.map (kernel.ι e.hom ≫ t) = 0 := by
    rw [L.map_comp, ht, ← Category.assoc, ← L.map_comp, kernel.condition,
      L.map_zero, zero_comp]
  have hk : kernel.ι e.hom ≫ t = 0 := by
    apply (cancel_epi d.hom).mp
    rw [comp_zero]
    apply ((closedLiftGeneratorPresentation A z j hpair (kernel e.hom)).2 I).injective
    change L.map (d.hom ≫ (kernel.ι e.hom ≫ t)) = L.map 0
    erw [L.map_comp, hz, comp_zero, L.map_zero]
  let tc : image e.hom ⟶ I :=
    (Abelian.coimageIsoImage' e.hom).inv ≫ cokernel.desc _ t hk
  let g : Q ⟶ I := Injective.factorThru tc (image.ι e.hom)
  have hg : e.hom ≫ g = t := by
    calc
      _ = factorThruImage e.hom ≫ image.ι e.hom ≫ g := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ g) (image.fac e.hom).symm
      _ = factorThruImage e.hom ≫ tc := by rw [Injective.comp_factorThru]
      _ = t := by
        dsimp only [tc]
        rw [← Category.assoc, Abelian.factorThruImage_comp_coimageIsoImage'_inv,
          cokernel.π_desc]
  refine ⟨g, (cancel_epi (L.map e.hom)).mp ?_⟩
  rw [← L.map_comp, hg]
  exact ht

/-- Lifting sections of a closed-fibre restriction of an ambient injective.

Source: the degree-zero lifting part of Step 2 of
`lem-sp-proetale-proper-open-boundary-test-hypercohomology`.
(blueprint: lem-sp-proetale-proper-closed-injective-sections).

Proof plan: pull back to P = B times_D W and its complementary closed fibre Z_P.
Weakly etale restriction preserves injectivity. Express a section of the closed
inverse image on affine weakly contractible closed-site objects by its henselian
lifts. On each lift it is a section of the ambient injective. Resolve the gluing
relations by the augmented free-module sheaves of the covering: maps from their
subobjects extend to the free-module sheaf by injectivity. Properness and the
specialization hypothesis ensure that these local lifts cover P: every point of
P specializes to Z_P, since the proper image of its closure is closed. Refining
by the finite principal-open/closed-localization covers makes the lifted maps
agree on their relations. Their extension gives an ambient section restricting
to the original section. Direct-image evaluation is evaluation on P, and the
constant-coefficient equivalence carries its unit to the displayed unit. This
proves surjectivity of its underlying map, equivalently that it is an epimorphism.
The empty closed fibre forces P empty by specialization, so the same argument
includes the empty case. -/
theorem proper_closed_injective_sections_epi
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z)) :
    ∀ (I : Sheaf (ProEt.topology B)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) [Injective I],
      Epi (((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology D)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing D A)) (op W))).map
        ((proEtaleConstantModuleDirectImage p A).map
          ((sfIntrinsicModuleEquivalence B A).functor.map
            ((ProEtale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
                (pullback.fst p i).closedComplement).unit.app I)))) := by
  intro I hI
  apply realization_directImage_sections_epi A p W
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let z := (pullback.fst p i).closedComplement
  let P := (proEtaleBaseChange p).obj W
  let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) B).obj P
  let L := ProEtale.upperStar Λ z
  let a := ProEtale.upperStarLowerStarAdjunction Λ z
  have hpair : Set.range (pullback.fst p i) = (Set.range z)ᶜ := by
    rw [Scheme.Hom.range_closedComplement, compl_compl]
  have hrel := proper_closedLift_relations_generated A p i W hW hspecializes
  intro y
  let s : Q ⟶ (ProEtale.lowerStar Λ z).obj (L.obj I) :=
    (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) P _).symm y
  let f : L.obj Q ⟶ L.obj I := (a.homEquiv Q (L.obj I)).symm s
  obtain ⟨g, hg⟩ := lift_map_of_closedLift_relations A z (pullback.fst p i)
    hpair Q hrel I f
  refine ⟨ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) P I g, ?_⟩
  change (a.unit.app I).hom.app (op P)
    (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) P I g) = y
  refine (ProEtale.freeSheafHomEquiv_comp (ULift.{u + 1, u} A) P
    g (a.unit.app I)).symm.trans ?_
  have he : g ≫ a.unit.app I = s := by
    apply (a.homEquiv Q (L.obj I)).symm.injective
    change L.map (g ≫ a.unit.app I) ≫ a.counit.app (L.obj I) = f
    rw [L.map_comp, Category.assoc,
      a.left_triangle_components, Category.comp_id]
    exact hg
  rw [he]
  exact (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) P _).apply_symm_apply y

end AlgebraicGeometry.Scheme
