/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Transition maps of higher direct images

For a commutative triangle `a ≫ h = h'` of schemes, with `a : Y' ⟶ Y` and `h : Y ⟶ X`, there
is a canonical map `Rh_* K ⟶ Rh'_* (a^* K)`, the composite of the unit of `Lh'^* ⊣ Rh'_*`,
the composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and the counit of `Lh^* ⊣ Rh_*`. In degree
`q` it gives the transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images. These
are the maps along which higher direct images are compared when the source scheme varies, as
in the limit theorem `AlgebraicGeometry.Etale.higherDirectImage_limit`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarPlusTransition`: the map `Rh_* K ⟶ Rh'_* (a^* K)`.
- `AlgebraicGeometry.Etale.higherDirectImageTransition`: the map
  `R^q h_* F ⟶ R^q h'_* a^* F`.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImage_limit`: higher direct images commute with limits
  of schemes along affine transition morphisms.

## References

- Stacks Project, Lemma 59.51.7, <https://stacks.math.columbia.edu/tag/09Z1>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transition

variable {X Y Y' : Scheme.{u}}

/-- The transition map `Rh_* K ⟶ Rh'_* (a^* K)` attached to a commutative triangle
`a ≫ h = h'`: the unit of `Lh'^* ⊣ Rh'_*` at `Rh_* K`, followed by `Rh'_*` applied to the
composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and to `La^*` of the counit of
`Lh^* ⊣ Rh_*` at `K`. -/
noncomputable def Etale.lowerStarPlusTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h').unit.app _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      ((eqToIso (by rw [← w]) ≪≫ Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app _ ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app K))

/-- The transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images attached to a
commutative triangle `a ≫ h = h'`: the degree-`q` homology of
`AlgebraicGeometry.Etale.lowerStarPlusTransition` at `F` placed in degree `0`, followed by the
identification `a^*(F[0]) ≅ (a^* F)[0]`. -/
noncomputable def Etale.higherDirectImageTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.higherDirectImage Λ h q F ⟶
      Etale.higherDirectImage Λ h' q (((a)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.lowerStarPlusTransition Λ a h h' w _ ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The transition map of higher direct images along a morphism `φ : U ⟶ V` of schemes over
`W`, for the sheaves pulled back from a fixed sheaf `G` on `W` and the structure morphisms
composed with `k : W ⟶ S`:
`R^q (V → S)_* (G|_V) ⟶ R^q (U → S)_* (G|_U)`. It is
`AlgebraicGeometry.Etale.higherDirectImageTransition` followed by the identification
`φ^*(G|_V) ≅ G|_U`. -/
noncomputable def Etale.higherDirectImageOverMap {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over W}
    (φ : U ⟶ V) :
    Etale.higherDirectImage Λ (V.hom ≫ k) q (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ⟶
      Etale.higherDirectImage Λ (U.hom ≫ k) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) :=
  Etale.higherDirectImageTransition Λ φ.left (V.hom ≫ k) (U.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom (Over.w φ).symm).inv.app
          G)))

end Transition

/-- Blueprint `sbc-lem-higher-direct-image-limit`: Higher direct images and limits of schemes.

Let `W ⟶ S` be a morphism of schemes, `G` a sheaf of `Λ`-modules on `W_ét`, and
`T = lim T_i` a cofiltered limit of schemes over `W` with affine transition morphisms, all
quasi-compact and quasi-separated over `S`. Then `colim_i R^q g_{i,*} (G|_{T_i}) ≅
R^q g_* (G|_T)`, where `g_i : T_i ⟶ S` and `g : T ⟶ S` are the structure morphisms. The
statement is recorded on every geometric stalk, in the form of the two defining properties of
a filtered colimit of modules: every element at the limit comes from some stage, and an element
of a stage dying at the limit already dies at a later stage. This is the case of the blueprint
statement for a system of sheaves pulled back from a fixed scheme. -/
@[stacks 09Z1]
theorem Etale.higherDirectImage_limit {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Over W) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)] (q : ℤ) (s : S) :
    (∀ y : ((S.uliftPointSmallEtale s).sheafFiber.obj (Etale.higherDirectImage Λ
        (c.pt.hom ≫ k) q (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) : ModuleCat.{u + 1} Λ),
      ∃ (i : I) (y' : ((S.uliftPointSmallEtale s).sheafFiber.obj
        (Etale.higherDirectImage Λ ((D.obj i).hom ≫ k) q
          (((D.obj i).hom)^*[ModuleCat.{u + 1} Λ].obj G)) : ModuleCat.{u + 1} Λ)),
        ((S.uliftPointSmallEtale s).sheafFiber.map
          (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = y) ∧
    ∀ (i : I) y', ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = 0 →
      ∃ (j : I) (f : j ⟶ i), ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (D.map f))).hom y' = 0 :=
  sorry

end AlgebraicGeometry
