/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Algebra.Homology.RingedForgetTensorTranspositionData
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # The Hom representative square for arbitrary source complexes

Source: Stacks 08J9, 070I; steps 5--8 of ringed tensor transposition
(blueprint: lem-sf-ringed-forget-hom-representative).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

-- Reuse the small-site transport directly when elaborating coefficient-ring compositions.
attribute [local instance 1000001] RingedDerivedNative.cachedCompose


section Generic

variable {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{wb} B]
  {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wa} A]
  (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [U.PreservesKInjectiveComplexes] [Abelian.HasKInjectiveResolutions B]
  (HCB : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ)
  (HCA : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex A ℤ)
  (HB : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
  (HA : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
  (ρB : RingedForgetTwoInjective.Representatives HCB HB)
  (ρA : RingedForgetTwoInjective.Representatives HCA HA)
  (chain : HCB ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙ HCA)
  (derived : HB ⋙ U.mapDerivedCategory ≅
    (U.mapDerivedCategory.op.prod U.mapDerivedCategory) ⋙ HA)
  (rep : RingedForgetTwoInjective.DerivedCompatibility U inferInstance
    HCB HCA HB HA ρB ρA chain derived)

include rep

private theorem extend_representative
    (K I : CochainComplex B ℤ) [I.IsKInjective] :
    derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
        HA.map
          (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
          ((U.mapDerivedCategoryFactors.inv.app K).op,
            U.mapDerivedCategoryFactors.hom.app I) ≫
        (ρA.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      U.mapDerivedCategory.map (ρB.iso K I).hom ≫
        U.mapDerivedCategoryFactors.hom.app (HCB.obj (op K, I)) ≫
        DerivedCategory.Q.map (chain.hom.app (op K, I)) := by
  obtain ⟨K', _, a, _, ha⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr ha
  let h := HB.map (X := (op (DerivedCategory.Q.obj K'), DerivedCategory.Q.obj I))
    (Y := (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
    ((DerivedCategory.Q.map a).op, 𝟙 _)
  have : IsIso h := by
    have : IsIso (Prod.mkHom (DerivedCategory.Q.map a).op
        (𝟙 (DerivedCategory.Q.obj I))) :=
      (isIso_prod_iff (f := Prod.mkHom (DerivedCategory.Q.map a).op
        (𝟙 (DerivedCategory.Q.obj I)))).mpr ⟨inferInstance, inferInstance⟩
    exact inferInstanceAs (IsIso (HB.map (Prod.mkHom (DerivedCategory.Q.map a).op
      (𝟙 (DerivedCategory.Q.obj I)))))
  apply (cancel_epi (U.mapDerivedCategory.map h)).mp
  have hr := rep K' I
  have hn := derived.hom.naturality
    (X := (op (DerivedCategory.Q.obj K'), DerivedCategory.Q.obj I))
    (Y := (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
    ((DerivedCategory.Q.map a).op, 𝟙 _)
  have hs := ρB.naturality K' K I I a (𝟙 I)
  have ht := ρA.naturality
    ((U.mapHomologicalComplex (.up ℤ)).obj K') ((U.mapHomologicalComplex (.up ℤ)).obj K)
    ((U.mapHomologicalComplex (.up ℤ)).obj I) ((U.mapHomologicalComplex (.up ℤ)).obj I)
    ((U.mapHomologicalComplex (.up ℤ)).map a) (𝟙 _)
  have hf := U.mapDerivedCategoryFactors.inv.naturality a
  dsimp only [Functor.comp_map] at hf
  have hc := chain.hom.naturality
    (X := (op K', I)) (Y := (op K, I)) (a.op, 𝟙 I)
  let aH := HCB.map
    (X := (op K', I)) (Y := (op K, I)) (a.op, 𝟙 I)
  have hα := U.mapDerivedCategoryFactors.hom.naturality aH
  have hm :
      HA.map (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K')),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
        (Y := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
        ((U.mapDerivedCategory.map (DerivedCategory.Q.map a)).op, 𝟙 _) ≫
      HA.map
        (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
        (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
          DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
        ((U.mapDerivedCategoryFactors.inv.app K).op,
          U.mapDerivedCategoryFactors.hom.app I) =
      HA.map
        (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K')),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
        (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K')),
          DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
        ((U.mapDerivedCategoryFactors.inv.app K').op,
          U.mapDerivedCategoryFactors.hom.app I) ≫
      HA.map
        (X := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K')),
          DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
        (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
          DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
        ((DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map a)).op,
          𝟙 _) := by
    rw [← HA.map_comp, ← HA.map_comp]
    congr 1
    ext
    · simpa only [prod_comp, ← op_comp] using congrArg Quiver.Hom.op hf.symm
    · simp
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hn hs ht hc hα
  simp only [Functor.map_id, Quiver.Hom.unop_op] at hn hs ht hc
  change U.mapDerivedCategory.map h ≫ _ = _ at hn
  rw [reassoc_of% hn, reassoc_of% hm, ht, reassoc_of% hr]
  rw [← DerivedCategory.Q.map_comp, ← hc, DerivedCategory.Q.map_comp]
  rw [← reassoc_of% hα, ← Functor.map_comp_assoc, ← hs, Functor.map_comp_assoc]


private theorem map_to_hom_representative
    (Q K I : CochainComplex B ℤ) [I.IsKInjective] (q : Q ⟶ HCB.obj (op K, I)) :
    U.mapDerivedCategory.map (DerivedCategory.Q.map q ≫ (ρB.iso K I).inv) ≫
        derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
        HA.map
          (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
          ((U.mapDerivedCategoryFactors.inv.app K).op,
            U.mapDerivedCategoryFactors.hom.app I) =
      U.mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map q ≫
          chain.hom.app (op K, I)) ≫
        (ρA.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I)).inv := by
  have h := extend_representative U HCB HCA HB HA ρB ρA chain derived rep K I
  have hh := congrArg (fun z ↦ U.mapDerivedCategory.map (ρB.iso K I).inv ≫ z ≫
    (ρA.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
      ((U.mapHomologicalComplex (.up ℤ)).obj I)).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp] at hh
  have hq := U.mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hq
  simp only [Functor.map_comp, Category.assoc]
  rw [hh, ← Category.assoc _ _ (DerivedCategory.Q.map (chain.hom.app (op K, I)) ≫
    (ρA.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
      ((U.mapHomologicalComplex (.up ℤ)).obj I)).inv), hq]
  simp only [Category.assoc]

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses

set_option maxHeartbeats 1000000 in
-- Cancel a localized K-injective source resolution in the natural representative squares.
/-- The normalized Hom comparison on maps into an arbitrary-source Hom complex.
Source: Stacks 079P and 08J7; step 1 of normalized ringed uncurrying
(blueprint: lem-sf-ringed-forget-hom-representative).

Proof: choose a K-injective resolution a:K to Kprime. The derived Hom map
contravariant in a is invertible. Precompose both desired maps with its image
under the exact derived functor. Naturality of chi, of the localization factor
and of the two representative isomorphisms identifies this equation with the
given representative equation for Kprime and I. Naturality of the chain Hom
comparison supplies the last square. Cancellation gives the representative square
for K. Compose with the inverse source and target representative isomorphisms,
and use naturality of the localization factor on q to obtain the displayed formula. -/
theorem ringed_forget_hom_representative
    (Q K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) [I.IsKInjective]
    (q : Q ⟶ homComplex (R := R) K I) :
    U.mapDerivedCategory.map (DerivedCategory.Q.map q ≫ (χ.source.iso K I).inv) ≫
        χ.derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
        (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').map
          (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
          ((U.mapDerivedCategoryFactors.inv.app K).op,
            U.mapDerivedCategoryFactors.hom.app I) =
      U.mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map q ≫
          χ.chain.hom.app (op K, I)) ≫
        (χ.target.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I)).inv := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  simpa only [homComplex, Functor.uncurry_obj_obj] using map_to_hom_representative U
    (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (Functor.uncurry.obj (homComplexFunctor (R := R')))
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R)
    (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R')
    χ.source.toRepresentatives χ.target.toRepresentatives χ.chain χ.derived
    χ.representative Q K I q

end CategoryTheory.RingedForgetTensorTransposition
