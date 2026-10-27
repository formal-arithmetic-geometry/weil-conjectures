/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
import all Sheaf.Paper.PullbackTensorCanonicalShiftUnit

/-! # Naturality of the ambient coefficient specialization

Source: Stacks 07A4 (blueprint: lem-pur-algebra-diagram-theta-naturality).
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v u' v' w
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open SheafOfModules.PullbackTensorCanonical
attribute [local irreducible] DerivedCategory.Q canonicalDerivedTensor Functor.mapDerivedCategory
attribute [local irreducible] Functor.curry SheafOfModules.monoidalCategory
attribute [local irreducible]
  CategoryTheory.AlgebraDiagramPullback.derivedCoefficientIso HomologicalComplex.single
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}

private theorem derived_coefficient_natural
    (f : RingedPullback.{u, u, u, u, u} R S)
    (d d' : CoefficientSquare.{u, u, u, u, u} f)
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    [ExactPullback f]
    (b : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
    (b' : f.L.obj (coefficient d'.sourceMap) ≅ coefficient d'.targetMap)
    (hY : coefficient d.sourceMap ⟶ coefficient d'.sourceMap)
    (hX : coefficient d.targetMap ⟶ coefficient d'.targetMap)
    (hb : f.L.map hY ≫ b'.hom = b.hom ≫ hX) :
    f.L.mapDerivedCategory.map
        (DerivedCategory.Q.map ((HomologicalComplex.single (Modules.{u, u, u} R)
          (.up ℤ) 0).map hY)) ≫ (derivedCoefficientIso f d' b').hom =
      (derivedCoefficientIso f d b).hom ≫ DerivedCategory.Q.map
        ((HomologicalComplex.single (Modules.{u, u, u} S) (.up ℤ) 0).map hX) := by
  simp only [derivedCoefficientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  erw [← Category.assoc,
    f.L.mapDerivedCategoryFactors.hom.naturality]
  simp only [Functor.comp_map]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  apply DerivedCategory.Q.congr_map
  have hn := (HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).hom.naturality hY
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (HomologicalComplex.single (Modules.{u, u, u} S) (.up ℤ) 0).map_comp, hb,
    (HomologicalComplex.single (Modules.{u, u, u} S) (.up ℤ) 0).map_comp]

private theorem ambient_unique
    (f : RingedPullback.{u, u, u, u, u} R S) (k : Comparison.{u, u, u, u, u} f)
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)] [ExactPullback f]
    (a b : Phi f.L.mapDerivedCategory.{w, w} ⟶ Psi f.L.mapDerivedCategory.{w, w})
    (ha : IsNormalized f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom a)
    (hb : IsNormalized f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom b) :
    a = b := by
  obtain ⟨ff⟩ := resolving_fullyFaithful (R := R) (S := S)
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  obtain ⟨⟨P, hp, hf⟩, ⟨Q, hq, hg⟩⟩ := Z
  change a.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    b.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  obtain ⟨hp',hq',hf',hg',ha⟩ := ha P Q hp hq hf hg
  obtain ⟨hp'',hq'',hf'',hg'',hb⟩ := hb P Q hp hq hf hg
  let t := (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} S)).map
    (Prod.mkHom (f.L.mapDerivedCategoryFactors.hom.app P)
      (f.L.mapDerivedCategoryFactors.hom.app Q))
  have ht : IsIso t := by
    dsimp only [t, Functor.uncurry_obj_map]
    infer_instance
  apply (cancel_epi (f.L.mapDerivedCategory.map
    (canonicalRepresentativeIso R P Q hp hq hf hg).hom)).mp
  apply (cancel_mono t).mp
  simpa only [t, Category.assoc] using ha.trans hb.symm

/-- Naturality of the normalized ambient coefficient specialization. The ambient
comparison is uniquely fixed on resolving pairs; its naturality and the derived
coefficient square remain natural after conjugating by scalar tensor presentations.
Source: Stacks 07A4 (blueprint: lem-pur-algebra-diagram-theta-naturality). -/
theorem theta_natural
    (f : RingedPullback.{u, u, u, u, u} R S) (k : Comparison.{u, u, u, u, u} f)
    [IsIso f.coefficient]
    (d d' : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    (k'' : Comparison.{u, u, u, u, u} (changed f d'))
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d'.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d'.S')]
    [ExactPullback f] [ExactPullback (changed f d)] [ExactPullback (changed f d')]
    [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
    [ExactRestriction d'.sourceMap] [ExactRestriction d'.targetMap]
    (q : Coherence f k d k') (q' : Coherence f k d' k'')
    (hY : coefficient d.sourceMap ⟶ coefficient d'.sourceMap)
    (hX : coefficient d.targetMap ⟶ coefficient d'.targetMap)
    (hb : f.L.map hY ≫ q'.beta.hom = q.beta.hom ≫ hX)
    (M : DerivedCategory (Modules.{u, u, u} R)) :
    f.L.mapDerivedCategory.map ((scalarUnderlyingMap q.source q'.source hY).app M) ≫
      q'.theta.hom.app M = q.theta.hom.app M ≫
        (scalarUnderlyingMap q.target q'.target hX).app (f.L.mapDerivedCategory.obj M) := by
  have he := ambient_unique f k q.ambient.hom q'.ambient.hom
    q.ambient_model q'.ambient_model
  have hc := derived_coefficient_natural f d d' q.beta q'.beta hY hX hb
  let TY := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} R)
  let TX := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} S)
  let DY := DerivedCategory.Q.{w}.map
    ((HomologicalComplex.single (Modules.{u, u, u} R) (.up ℤ) 0).map hY)
  let DX := DerivedCategory.Q.{w}.map
    ((HomologicalComplex.single (Modules.{u, u, u} S) (.up ℤ) 0).map hX)
  have hn := q.ambient.hom.naturality (Prod.mkHom (𝟙 M) DY)
  change f.L.mapDerivedCategory.map (TY.map (Prod.mkHom (𝟙 M) DY)) ≫
      q.ambient.hom.app (M, DerivedCategory.Q.obj (coefficientComplex d'.sourceMap)) =
    q.ambient.hom.app (M, DerivedCategory.Q.obj (coefficientComplex d.sourceMap)) ≫
      TX.map (Prod.mkHom (f.L.mapDerivedCategory.map (𝟙 M))
        (f.L.mapDerivedCategory.map DY)) at hn
  have ht : f.L.mapDerivedCategory.map (TY.map (Prod.mkHom (𝟙 M) DY)) ≫
      q.ambient.hom.app (M, DerivedCategory.Q.obj (coefficientComplex d'.sourceMap)) ≫
        TX.map (Prod.mkHom (𝟙 _) (derivedCoefficientIso f d' q'.beta).hom) =
    q.ambient.hom.app (M, DerivedCategory.Q.obj (coefficientComplex d.sourceMap)) ≫
      TX.map (Prod.mkHom (𝟙 _) (derivedCoefficientIso f d q.beta).hom) ≫
        TX.map (Prod.mkHom (𝟙 _) DX) := by
    rw [← Category.assoc, hn]
    simp only [Functor.map_id, Category.assoc]
    rw [← TX.map_comp, ← TX.map_comp]
    congr 2
    ext
    · simp
    · exact hc
  rw [q.theta_ambient, q'.theta_ambient]
  unfold scalarUnderlyingMap
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  simp only [← f.L.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    f.L.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  simp only [scalarTensorComparison, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  rw [← he]
  repeat' erw [Category.id_comp]
  simpa only [TY, TX, DY, DX, Category.assoc, Functor.flip_map_app, Functor.uncurry_obj_map,
    Functor.map_id, Functor.map_comp, NatTrans.id_app, Category.id_comp,
    Category.comp_id] using
    congrArg (fun z ↦ f.L.mapDerivedCategory.map
      (q.source.underlyingIso.hom.app M) ≫ z ≫
        q'.target.underlyingIso.inv.app (f.L.mapDerivedCategory.obj M)) ht
end CategoryTheory.AlgebraDiagramPullback
