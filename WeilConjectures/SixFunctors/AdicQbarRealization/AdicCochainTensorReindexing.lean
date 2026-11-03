/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicTensorReindexing
import WeilConjectures.Algebra.Homology.SixFunctors.SectionwiseTensorComparison
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # Homogeneous tensor comparison for sectionwise adic reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 03EK and 06YN.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.LocallyFiniteAdicRealization.ringSheaf
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u u₁ v₁ u₂ v₂ c v d z w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
private theorem exists_total_tensor_comparison
    {M : Type u₁} [Category.{v₁} M] [Abelian M] [MonoidalCategory M]
    {N : Type u₂} [Category.{v₂} N] [Abelian N] [MonoidalCategory N]
    [MonoidalPreadditive M] [MonoidalPreadditive N]
    [HasCoproducts.{0} M] [HasCoproducts.{0} N]
    (U : M ⥤ N) [U.Additive] [U.IsLeftAdjoint]
    (e : ∀ A B : M, U.obj (A ⊗ B) ≅ U.obj A ⊗ U.obj B)
    (he : ∀ {A A' B B'} (f : A ⟶ A') (h : B ⟶ B'),
      U.map (f ⊗ₘ h) ≫ (e A' B').hom = (e A B).hom ≫ (U.map f ⊗ₘ U.map h)) :
    let F := U.mapHomologicalComplex (.up ℤ)
    let tY := Functor.uncurry.obj (Functor.map₂HomologicalComplex
      (curriedTensor M) (.up ℤ) (.up ℤ) (.up ℤ))
    let tX := Functor.uncurry.obj (Functor.map₂HomologicalComplex
      (curriedTensor N) (.up ℤ) (.up ℤ) (.up ℤ))
    ∃ chain : tY ⋙ F ≅ (F.prod F) ⋙ tX,
      ∀ (P Q : CochainComplex M ℤ) (p q : ℤ),
        U.map (CochainComplex.ιMapBifunctor P Q (curriedTensor M) p q (p + q) rfl) ≫
            (chain.hom.app (P, Q)).f (p + q) =
          (e (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q)
            (curriedTensor N) p q (p + q) rfl := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let tY := Functor.uncurry.obj (Functor.map₂HomologicalComplex
    (curriedTensor M) (.up ℤ) (.up ℤ) (.up ℤ))
  let tX := Functor.uncurry.obj (Functor.map₂HomologicalComplex
    (curriedTensor N) (.up ℤ) (.up ℤ) (.up ℤ))
  have hiso (P Q : CochainComplex M ℤ) :
      IsIso (tensorPullbackTotal U e he P Q) :=
    tensorPullbackTotal_isIso U e he U.rightAdjoint (Adjunction.ofIsLeftAdjoint U) P Q
  let b0 : (F.prod F) ⋙ tX ≅ tY ⋙ F := NatIso.ofComponents
    (fun Z ↦ @asIso _ _ _ _ (tensorPullbackTotal U e he Z.1 Z.2) (hiso Z.1 Z.2)) (by
      intro Z W h
      dsimp only [F, tY, tX, Functor.comp_map, Functor.prod_map]
      simp only [Functor.uncurry_obj_map,
        Functor.map₂HomologicalComplex,
        SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
      exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
        U e he h.1 h.2)
  refine ⟨b0.symm, ?_⟩
  intro P Q p q
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor M)
    p q (p + q) rfl
  let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q)
    (curriedTensor N) p q (p + q) rfl
  let z := (HomologicalComplex.eval N (.up ℤ) (p + q)).mapIso
    (b0.app (P, Q))
  have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ U.map ι := by
    change ι' ≫ tensorPullbackTotalComponent U e P Q (p + q) = _
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q rfl
  have hi : U.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
    apply (cancel_mono z.hom).1
    erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
      Iso.hom_inv_id_assoc]
  exact hi

open WeilConjectures in
private theorem exists_sectionwise_cochain_tensor_comparison
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{z} D]
    [EssentiallySmall.{max c v d z w} C] [EssentiallySmall.{max c v d z w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v d z w} RingCat.{max c v d z w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{max c v d z w} RingCat.{max c v d z w})]
    [HasSheafify J AddCommGrpCat.{max c v d z w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v d z w}]
    [HasSheafify K AddCommGrpCat.{max c v d z w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c v d z w}]
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf J CommRingCat.{max c v d z w}) (S : Sheaf K CommRingCat.{max c v d z w})
    (a : (sheafCompose J (forget₂ CommRingCat.{max c v d z w} RingCat.{max c v d z w})).obj R ≅
      (f.sheafPushforwardContinuous RingCat.{max c v d z w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{max c v d z w} RingCat.{max c v d z w})).obj S))
    [(SheafOfModules.pushforward.{max c v d z w} a.hom).Additive]
    [(SheafOfModules.pushforward.{max c v d z w} a.hom).IsLeftAdjoint] :
    let U := SheafOfModules.pushforward.{max c v d z w} a.hom
    let F := U.mapHomologicalComplex (.up ℤ)
    ∃ chain : coefficientTotalTensor.{max c v d z w, d, z} K S ⋙ F ≅
        (F.prod F) ⋙ coefficientTotalTensor.{max c v d z w, c, v} J R,
      ∀ (P Q : CochainComplex (SheafOfModules.scalarModules K S) ℤ)
        (p q : ℤ) (V : Cᵒᵖ) (x : (P.X p).val.obj (f.op.obj V))
        (y : (Q.X q).val.obj (f.op.obj V)),
        ((chain.hom.app (P, Q)).f (p + q)).val.app V
          (coefficientTensorGenerator.{max c v d z w, d, z} K S
            P Q p q (p + q) rfl (f.op.obj V) x y) =
        coefficientTensorGenerator.{max c v d z w, c, v} J R
          (F.obj P) (F.obj Q) p q (p + q) rfl V x y := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory R
  have := SheafOfModules.cochainModulesPreadditive S
  have := SheafOfModules.cochainModulesPreadditive R
  let U := SheafOfModules.pushforward.{max c v d z w} a.hom
  obtain ⟨e, he, hgen⟩ := SheafOfModules.sectionwiseTensorComparison f R S a
  obtain ⟨chain, hchain⟩ := exists_total_tensor_comparison U e he
  refine ⟨chain, ?_⟩
  intro P Q p q V x y
  change ((chain.hom.app (P, Q)).f (p + q)).val.app V
    ((CochainComplex.ιMapBifunctor P Q (curriedTensor (SheafOfModules.scalarModules K S))
      p q (p + q) rfl).val.app (f.op.obj V)
        (SheafOfModules.ScalarHomOrdinary.pure S (P.X p) (Q.X q) (f.op.obj V) x y)) =
    (CochainComplex.ιMapBifunctor ((U.mapHomologicalComplex (.up ℤ)).obj P)
      ((U.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor (SheafOfModules.scalarModules J R)) p q (p + q) rfl).val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (U.obj (P.X p)) (U.obj (Q.X q)) V x y)
  have hh := congrArg (fun h ↦ h.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure S (P.X p) (Q.X q) (f.op.obj V) x y))
    (hchain P Q p q)
  exact hh.trans (congrArg ((CochainComplex.ιMapBifunctor
    ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
    (curriedTensor (SheafOfModules.scalarModules J R)) p q (p + q) rfl).val.app V)
    (hgen _ _ V x y))

namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- Sectionwise reindexing commutes with the signed total tensor, with the identity
formula on homogeneous pure sections. This asserts no derived comparison, K-flat
preservation or coefficient-unit normalization.
Source: BS Remark 6.8.15; Stacks Tags 03EK and 06YN; steps 1--2 of
lem-sf-adic-tensor-reindexing-models
(blueprint: lem-sf-adic-cochain-tensor-reindexing).

Proof: pull module presheaves back along postcomposition by the scheme isomorphism,
and transport the scalar action by B.iso inverse. The balanced tensor comparison
sends x tensor y to the same two sections, and the inverse coefficient map gives
its inverse. A site equivalence commutes with module sheafification, so this is a
natural isomorphism on the ordinary sheaf tensors. Extend the comparison through
the coproduct inclusions in every total degree. The two differential summands
commute with it by naturality and additivity; the integer sign is preserved. The
inverse ordinary tensor comparison and preservation of coproducts invert the total
map. Evaluating on the homogeneous summand inclusion and its sheafified pure tensor
gives precisely reindexTensorPure. This works for unbounded complexes, zero rings
and empty schemes; no exactness of section evaluation is required. -/
theorem exists_cochain_tensor_reindexing {X Y : Scheme.{u}} (g : X ≅ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g.hom R S) :
    ∃ chain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
        (modulePull l X g.hom B).mapHomologicalComplex (.up ℤ) ≅
      (((modulePull l X g.hom B).mapHomologicalComplex (.up ℤ)).prod
        ((modulePull l X g.hom B).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R),
      reindexTensorPure l X g.hom B chain := by
  classical
  let U := modulePull l X g.hom B
  let f := proEtaleIsoPostcompose g.hom
  have : f.IsEquivalence := (proEtaleIsoPostcompose_equivalence g.hom).1
  have := sectionwisePostcompose_cocontinuous g.hom
  let ci : (isoSectionwiseInverseImage g.hom RingCat.{u + 1}).obj
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)) ≅
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l X R) :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso
  let a := asIso (inv ci.hom)
  have : (SheafOfModules.pushforward.{u + 1} a.hom).Additive :=
    inferInstanceAs U.Additive
  have : (SheafOfModules.pushforward.{u + 1} a.hom).IsLeftAdjoint := inferInstance
  obtain ⟨chain, hpure⟩ :=
    exists_sectionwise_cochain_tensor_comparison.{u + 1, u, u + 1, u, u + 1}
    f (ring l X R) (ring l Y S) a
  exact ⟨chain, hpure⟩

end WeilConjectures.AdicQbarRealization
