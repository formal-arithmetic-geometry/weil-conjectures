/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyPresentationData
public import Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # Geometric complex data for restricted abelian cohomology

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-abelian-complex-data).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The abelian coefficient sheaf pulled back from the fixed scheme W. -/
noncomputable def restrictedOverCoefficient {W : Scheme.{u}}
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) :=
  (upperStar AddCommGrpCat.{u + 1} A.hom).obj F

/-- Integer-degree cohomology on the actual etale fibre product. -/
noncomputable def restrictedOverCohomology {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A : Over W) (U : S.Etale) : AddCommGrpCat.{u + 1} :=
  (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)) q).obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (A.hom ≫ k))).obj
        (restrictedOverCoefficient F A))))

/-- The canonical map is derived pullback followed by the coefficient identification.
It is written explicitly and is not selected from an existence theorem. -/
noncomputable def restrictedOverCohomologyMap {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    restrictedOverCohomology k F q B U ⟶ restrictedOverCohomology k F q A U := by
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by rw [← Category.assoc, Over.w]
  let a := rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k) w U
  let R := (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (B.hom ≫ k))).obj
    (restrictedOverCoefficient F B)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
    (Over.w f).symm).inv.app F
  exact rawAffineComplexPullback q a ((CochainComplex.singleFunctor _ 0).obj R) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)) q).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).hom.app R ≫
          (CochainComplex.singleFunctor _ 0).map
            (rawAffineRestrictedCoefficient f.left (B.hom ≫ k) (A.hom ≫ k) w
              (restrictedOverCoefficient F B) (restrictedOverCoefficient F A) φ U)))

set_option backward.isDefEq.respectTransparency true in
/-- Geometric complex data for restricted abelian cohomology of fixed coefficients.
Source: Stacks Project, Tag 09Z1, affine-object reduction in lemma-relative-colimit;
Tag 0EZM, lemma-colimit-variant-complexes, before invoking continuity.
(blueprint: lem-sbc-restricted-over-abelian-complex-data).

Proof: Base change D and c to U using the pullbacks U times_S D(i). The universal
property of each pullback defines the transition arrows and cone arrows, proves
functoriality, and identifies the resulting cone as limiting. Affineness survives
base change. The maps to affine U are qcqs by base change, so their sources are
compact and quasi-separated. Restrict the sheaves A.hom^*F to these fibre products
and form their degree-zero single complexes. The coefficient identifications are
upperStarComp inverses, restricted using the two comparisons displayed in
rawAffineRestrictedCoefficient. Unit and associativity coherence give the complex
identity and composition equations. The lower bound is zero. On the limiting
scheme these complexes identify with the pullback of F from W, in degree zero.
Take the constant diagram of that complex and its identity cocone. I opposite
is nonempty and connected, so that cocone is colimiting; the composition comparisons
give eG and its map equation. Set p=q and P=rawAffineComplexPullback q. The stage
cohomology is precisely restrictedOverCohomology; compose the single-complex
identifications with e to give eH. Identify the constant cocone point similarly
and compose with e₀ to obtain the apex isomorphism. The definitions of
restrictedOverCohomologyMap and rawAffineRestrictedCoefficient identify the stage
maps with P followed by cohomology of phi, and the cone maps with P followed by
cohomology of the coefficient leg. The assumed squares give hH and hB.
No derived Hom, scalar comparison, or cohomology continuity is used. For q<0
single-complex cohomology vanishes; the identical construction still applies.
For an empty test object the same pullback and zero sheaf constructions apply. -/
theorem restrictedOverAbelianCocone_complex_data
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F₀ : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D₀ : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D₀.map f).left]
    [∀ i, QuasiCompact ((D₀.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D₀.obj i).hom ≫ k)]
    (c₀ : Cone D₀) (hc₀ : IsLimit ((Over.forget W).mapCone c₀))
    [QuasiCompact (c₀.pt.hom ≫ k)] [QuasiSeparated (c₀.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
    (e : ∀ i : I, H.obj (op i) ≅ restrictedOverCohomology k F₀ q (D₀.obj i) U)
    (e₀ : B.pt ≅ restrictedOverCohomology k F₀ q c₀.pt U)
    (he : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (e j).hom =
      (e i).hom ≫ restrictedOverCohomologyMap k F₀ q (D₀.map f) U)
    (he₀ : ∀ i : I, B.ι.app (op i) ≫ e₀.hom =
      (e i).hom ≫ restrictedOverCohomologyMap k F₀ q (c₀.π.app i) U) :
  EtaleComplexCohomologyPresentationData H B := by sorry

end AlgebraicGeometry.Etale
