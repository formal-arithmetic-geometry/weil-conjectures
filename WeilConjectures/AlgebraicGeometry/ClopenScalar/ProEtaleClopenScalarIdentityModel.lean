/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComputation

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

/-- On a flat-term K-flat complex whose restriction is also flat-term K-flat,
the normalized derived identity square follows from its ordinary multiplication square.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D, the identity
part of the representative calculation in the parent coherence node.
(blueprint: lem-pur-clopen-scalar-identity-model).

Proof: postcompose the desired equation with the canonical restriction-factorization
isomorphism at P. By naturality of the component derived unit, move that
factorization to before the component unit. Insert the Units representative formula
for the component unit at the restricted P, using hiP and hif, and the ambient
Units representative formula at P. Transport along rings.map_id identifies the
two component identity presentations and their computation morphisms. The
comparison representative for the identity coefficient map then identifies the
left side with restriction of the ambient computation followed by Q of the
chain comparison and termwise component multiplication. Naturality of the
restriction factorization identifies the right side with the same computation
followed by Q of restricted termwise ambient multiplication. These cochain maps
agree: their degree-k components are the ordinary identity square hordinary at
P.X k, with hdegree identifying the chain comparison. Apply Q to this equality
and cancel the restriction-factorization isomorphism. This proof uses no density
or extension from models, and includes zero rings and zero complexes. -/
theorem clopen_scalar_identity_model
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (U : Units.{t, u} @p) (V : Units.{t, u} @q)
    (d : Comparison.{t, u} j @p @q)
    (hdegree : d.degree) (hrep : d.representative)
    (hordinary : ∀ (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) (M : Mods.{t, u} R),
    (d.ordinary (𝟙 R)).hom.app M ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_id R)) ≫
        (V.ordinary ((rings.{t, u} j).obj R)).hom.app ((res.{t, u} j R).obj M) =
      (res.{t, u} j R).map ((U.ordinary R).hom.app M))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P : CochainComplex (Mods.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P)
    (hf : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X) (R :=
      R) (P.X k))
    (hiP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R :=
      (rings.{t, u} j).obj R)
      (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))
    (hif : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology Y) (R :=
      (rings.{t, u} j).obj R)
      ((res.{t, u} j R).obj (P.X k))) :
    (d.derived (𝟙 R)).hom.app (DerivedCategory.Q.obj P) ≫
        eqToHom (congrArg (fun f ↦ (extD.{t, u} (Z := Y) (q f)).obj ((resD.{t, u} j R).obj
          (DerivedCategory.Q.obj P)))
          ((rings.{t, u} j).map_id R)) ≫
        (V.derived ((rings.{t, u} j).obj R)).hom.app ((resD.{t, u} j R).obj
          (DerivedCategory.Q.obj P)) =
      (resD.{t, u} j R).map ((U.derived R).hom.app (DerivedCategory.Q.obj P)) := by
  apply (cancel_mono ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P)).1
  have hV := (V.derived ((rings.{t, u} j).obj R)).hom.naturality
    ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P)
  simp only [Functor.id_map, Functor.comp_obj] at hV
  simp only [Category.assoc]
  rw [← hV, V.representative _ _ hiP hif, reassoc_of% (eqToHom_comp_extD_map_comp_computation q
    ((rings.{t, u} j).map_id R) (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P)
    ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P))]
  rw [reassoc_of% (hrep (𝟙 R) P hP hf), U.representative R P hP hf, Functor.map_comp_assoc]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  simp only [← Functor.map_comp]
  congr 2
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun k ↦ ?_)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, hdegree (𝟙 R) P k]
  simp only [id_obj, eqToHom_refl, NatIso.mapHomologicalComplex, mapHomologicalComplexIdIso,
    Iso.trans_hom, NatTrans.comp_app, NatIso.ofComponents_hom_app, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.refl_hom, Category.comp_id, Category.id_comp, map_comp, mapHomologicalComplex_map_f, map_id]
  erw [Category.comp_id]
  have h := hordinary R (P.X k)
  simp only [eqToHom_refl, Category.id_comp] at h
  exact h

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
