/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Cohomology of the derived base-change map

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary, order 1752;
Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7
(blueprint: lem-kun-bc-map-on-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Etale

-- Transport the defining resolution equation along the source resolution and the
-- target comparison, using naturality of the two transformations.
private lemma resolution_exchange_formula
    {A B C D E H : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category H]
    {Q : A ⥤ C} {Q' : B ⥤ D} {f : A ⥤ E} {f' : B ⥤ H}
    {fR : C ⥤ E} {fR' : D ⥤ H} {g : E ⥤ H} {g' : C ⥤ D} {u : A ⥤ B}
    {η : f ⟶ Q ⋙ fR} {η' : f' ⟶ Q' ⋙ fR'}
    {φ : Q ⋙ g' ≅ u ⋙ Q'} {δ : fR ⋙ g ⟶ g' ⋙ fR'}
    (I : A) (J : B) {K : C} (s : K ≅ Q.obj I) (j : u.obj I ⟶ J)
    [IsIso (η.app I)] [IsIso (Q'.map j)]
    (e : g.obj (f.obj I) ⟶ f'.obj (u.obj I))
    (hfac : g.map (η.app I) ≫ δ.app (Q.obj I) =
      e ≫ η'.app (u.obj I) ≫ fR'.map (φ.inv.app I)) :
    δ.app K = inv (g.map (η.app I ≫ fR.map s.inv)) ≫ e ≫ f'.map j ≫
      (η'.app J ≫ fR'.map (inv
        (g'.map s.hom ≫ φ.hom.app I ≫ Q'.map j))) := by
  let t := g'.map s.hom ≫ φ.hom.app I ≫ Q'.map j
  have : IsIso t := by dsimp [t]; infer_instance
  have hcancel : Q'.map j ≫ inv t = φ.inv.app I ≫ g'.map s.inv := by
    dsimp [t]
    simp only [IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_inv, IsIso.Iso.inv_hom, NatIso.inv_hom_app]
  have htarget : f'.map j ≫ (η'.app J ≫ fR'.map (inv t)) =
      η'.app (u.obj I) ≫ fR'.map (φ.inv.app I ≫ g'.map s.inv) := by
    have hn := η'.naturality j
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← fR'.map_comp, hcancel]
  apply (cancel_epi (g.map (η.app I ≫ fR.map s.inv))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [htarget]
  have hn := δ.naturality s.inv
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, hfac]
  simp only [Functor.map_comp, Category.assoc]

/-- On a sheaf placed in degree zero, the cohomology of derived exchange is the
usual resolution base-change map. The displayed right side writes out that recipe:
compare the direct image of an injective representative `I` with the derived direct
image using its unit and `s`; apply the underived exchange termwise; apply `f'_*`
to the comparison `j` with the injective representative `J`; finally use the derived
unit and the inverse of the pulled-back resolution to identify the target.
Thus applying cohomology implements the quotient of cycles by boundaries, without
requiring global cycle representatives of sections of the quotient sheaf.
The final clause states vanishing of both higher direct images in negative degrees.

Proof:
1. Choose injective representatives of `F[0]` and of its inverse image. Exactness of
inverse image preserves the resolution quasi-isomorphism (inverse-image-exact and
exact-functor-complex-cohomology). In particular, `j` is a comparison with a new
resolution; no injectivity of inverse image of `I` is assumed.
2. The termwise comparison lemma (derived-exchange-termwise) identifies derived
exchange with the underived exchange followed by `f'_*(j)`, conjugated by the
canonical resolution comparisons written here.
3. Apply degree-`q` cohomology to that equation. Exact-functor-complex-cohomology,
via `mapDerivedCategoryPlusHomologyFunctorIso`, identifies the source cohomology
with inverse image of the higher direct image; direct-image defines the target as
the cohomology of the derived direct image. These comparisons are canonical.
4. The chain-map formula takes a cycle class to the class of its termwise
underived exchange followed by `f'_*(j)`. It preserves boundaries, so induces the
usual quotient-sheaf map. For negative `q`, use nonnegative injective representatives
(dplus-injective-representative); additive direct image leaves their negative terms
zero. Consequently both cohomology sheaves vanish.
Source: Stacks Project, Tags 0736 and 07A7; blueprint order 1752
(blueprint: lem-kun-bc-map-on-cohomology). -/
theorem derivedBaseChangeMapPlus_cohomology_resolution
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    (∀ (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (J : HomotopyCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (_ : ∀ n : ℤ, Injective (I.obj.as.X n))
      (_ : ∀ n : ℤ, Injective (J.obj.as.X n))
      (s : ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≅
          DerivedCategory.Plus.Qh.obj I)
      (j : ((g')^*[AddCommGrpCat.{u + 1}]).mapHomotopyCategoryPlus.obj I ⟶ J),
      ∀ [IsIso (DerivedCategory.Plus.Qh.map j)],
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
        q).map
        ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
            ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F)) =
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
        q).map
        (inv (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit.app I ≫
          (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map s.inv)) ≫
        ((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh.hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus.obj I) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus
            (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app I) ≫
        DerivedCategory.Plus.Qh.map ((f')_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus.map j) ≫
        ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit.app J ≫
          (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map (inv
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map s.hom ≫
          ((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh.hom.app I ≫
          DerivedCategory.Plus.Qh.map j)))) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
            ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))) ∧
    (q < 0 →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsZero ((DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology
        AddCommGrpCat.{u + 1}) q).obj
        ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            (((g')^*[AddCommGrpCat.{u + 1}]).obj F))))) := by
  classical
  constructor
  · intro I J hI hJ s j hj
    have heq := resolution_exchange_formula
      (f := (f)_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (f' := (f')_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (fR := (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus)
      (fR' := (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus)
      (g := ((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus)
      (g' := ((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus)
      (u := ((g')^*[AddCommGrpCat.{u + 1}]).mapHomotopyCategoryPlus)
      (η := (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit)
      (η' := (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit)
      (φ := ((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh)
      (δ := Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
      I J s j
      ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh.hom.app
        ((f)_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus.obj I)) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
            (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app I))
      (by simpa only [Category.assoc] using
        Etale.derivedBaseChangeMapPlus_fac_app AddCommGrpCat.{u + 1} sq.toCommSq I)
    simpa only [Functor.comp_map, Category.assoc] using congrArg
      (fun a ↦
        (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map a ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
            ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
              ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                F))) heq
  · intro hq
    exact ⟨Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      ((f)_*[AddCommGrpCat.{u + 1}]) _ 0 hq,
      Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((f')_*[AddCommGrpCat.{u + 1}]) _ 0 hq⟩

end AlgebraicGeometry
