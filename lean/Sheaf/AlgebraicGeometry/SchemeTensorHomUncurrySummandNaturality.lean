/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality of uncurrying on tensor summands
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem uncurry_natural {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A A' T T' N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a : T' ⟶ T) (b : A' ⟶ A) (c : N ⟶ N')
    (f : T ⟶ SheafOfModules.homObj (R := R) A N) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (β_ T' A').hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A' T' N').symm
      (a ≫ f ≫ SheafOfModules.homObjMap (R := R) b c) =
    (a ⊗ₘ b) ≫ ((β_ T A).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) A T N).symm f) ≫ c := by
  have := SheafOfModules.isMonoidal_W R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  apply congrArg ((β_ T' A').hom ≫ ·)
  apply (SheafOfModules.tensorHomEquiv (R := R) A' T' N').injective
  simp only [Equiv.apply_symm_apply, tensorHom_def, Category.assoc,
    SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R),
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R)]
  simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R), Category.comp_id]


-- Move postcomposition outside evaluation, then precompose its free argument.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem uncurry_pre_post {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A T T' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a : T' ⟶ T) (c : N ⟶ N')
    (f : T ⟶ SheafOfModules.homObj (R := R) A N) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    a ▷ A ≫ (β_ T A).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) A T N').symm
        (f ≫ SheafOfModules.homObjMap (R := R) (𝟙 A) c) =
    (β_ T' A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A T' N).symm
      (a ≫ f) ≫ c := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have h₁ := uncurry_natural R A A T T N N' (𝟙 T) (𝟙 A) c f
  have h₂ := uncurry_natural R A A T T' N N a (𝟙 A) (𝟙 N) f
  simp only [tensorHom_id, Category.id_comp, Category.comp_id,
    SheafOfModules.homObjMap_id, id_whiskerRight] at h₁ h₂
  rw [h₁]
  simpa only [Category.assoc] using congrArg (· ≫ c) h₂.symm

-- Keep projection equalities abstract during reassociation and uncurrying.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluation_projection {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A T T' N N' H H' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a : T' ⟶ T) (f : T ⟶ H) (g : H ⟶ H') (c : N ⟶ N')
    (π : H ⟶ SheafOfModules.homObj (R := R) A N)
    (π' : H' ⟶ SheafOfModules.homObj (R := R) A N')
    (h : g ≫ π' = π ≫ SheafOfModules.homObjMap (R := R) (𝟙 A) c) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    a ▷ A ≫ (β_ T A).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) A T N').symm ((f ≫ g) ≫ π') =
    (β_ T' A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A T' N).symm
      (a ≫ f ≫ π) ≫ c := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  rw [Category.assoc, h, ← Category.assoc f]
  exact uncurry_pre_post R A T T' N N' a c (f ≫ π)

-- Projection naturality with a fixed Hom source.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem postcomp_projection {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (P F G : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (g : F ⟶ G) (n r k : ℤ) (h : r + n = k) :
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
    (((homComplexFunctor (R := R)).obj (op P)).map g).f n ≫ π P G n r k h =
      π P F n r k h ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (g.f k) := by
  have hm := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := R))).2.2
      P P F G (𝟙 P) g n r k h
  simp only [op_id, HomologicalComplex.id_f] at hm
  have hid := (homComplexFunctor (R := R)).map_id (op P)
  rw [hid] at hm
  simpa only [NatTrans.id_app, Category.id_comp] using hm

-- The calculation before specializing to a scheme and its resolution functor.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem hom_evaluation {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (K P F G : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (T : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : K ⟶ homComplex (R := R) P F) (g : F ⟶ G)
    (n r k : ℤ) (h : r + n = k) (a : T ⟶ K.X n) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
    a ▷ P.X r ≫ (β_ (K.X n) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) (P.X r) (K.X n) (G.X k)).symm
        ((f ≫ ((homComplexFunctor (R := R)).obj (op P)).map g).f n ≫ π P G n r k h) =
    (β_ T (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) (P.X r) T (F.X k)).symm
        (a ≫ f.f n ≫ π P F n r k h) ≫ g.f k := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
  exact evaluation_projection R (P.X r) (K.X n) T (F.X k) (G.X k)
    ((homComplex (R := R) P F).X n) ((homComplex (R := R) P G).X n)
    a (f.f n) ((((homComplexFunctor (R := R)).obj (op P)).map g).f n)
    (g.f k) (π P F n r k h) (π P G n r k h)
    (postcomp_projection R P F G g n r k h)

set_option maxHeartbeats 1200000 in
-- The concrete tensor-total and resolution instance comparisons require extra heartbeats.
/-- Restricting uncurrying and postcomposition to an arbitrary tensor summand.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, step 3, naturality portion.
(blueprint: lem-pc-scheme-uncurry-summand-naturality).

Proof: Apply schemeTensorHomUncurry_component to the outer inclusion in degrees
n,r,k. Its inverse tensor-Hom expression uses the projection of Hom(P,I(F)).
The naturality equation of homComplex_projections_exists with identity on P and
eta_F on F moves this projection across Hom(P,eta_F). Naturality of uncurrying in
its target moves eta_F to the last factor. Naturality of the symmetric braiding
and of uncurrying in its source then moves the inner tensor inclusion into the
argument of tensorHomEquiv.symm. Reassociate composition to obtain the displayed
formula. Only n+r=k is used for the Hom projection; p+q=n indexes the inclusion.
This argument imposes no boundedness or nonvanishing hypotheses and works for
zero complexes and the empty scheme. -/
theorem schemeTensorHomUncurry_summand_naturality (Y : Scheme.{u})
    (P F V : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F V ⟶ homComplex (R := Y.sheaf) P F)
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F
            (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))).f k =
    (β_ (F.X p ⊗ V.X q) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (F.X p ⊗ V.X q)
        (F.X k)).symm
        (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ≫
          f.f n ≫ π P F n r k (by omega)) ≫ (eta.app F).f k := by
  classical
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  have hc := schemeTensorHomUncurry_component Y (pullbackTensorTotal Y F V) P F
    (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))
    n r k hnr (by omega)
  refine (congrArg (fun t ↦
    HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷
      P.X r ≫ t) hc).trans ?_
  exact hom_evaluation Y.sheaf (pullbackTensorTotal Y F V) P F
    ((schemeHomKInjectiveResolution Y).obj F) (F.X p ⊗ V.X q) f (eta.app F)
    n r k (by omega)
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq)

end AlgebraicGeometry
