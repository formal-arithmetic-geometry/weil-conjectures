/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

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
- `AlgebraicGeometry.Etale.higherDirectImagePresheaf`: the presheaf `W ↦ H^q(W ×_X Y, K|)`.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImage_limit`: higher direct images commute with limits
  of schemes along affine transition morphisms.
- `AlgebraicGeometry.Etale.nonempty_presheafToSheaf_higherDirectImagePresheaf_iso`: `R^q h_* K`
  is the sheafification of `W ↦ H^q(W ×_X Y, K|)` for a quasi-compact quasi-separated `h`.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`: higher direct images
  along a quasi-compact quasi-separated morphism commute with filtered colimits of sheaves.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`: the
  higher direct image `R^q h_* (Λ/dΛ)` vanishes as soon as every class of
  `H^q(U ×_X Y, ℤ/e)`, for `e ∣ d` and `U` affine étale over `X`, dies on an étale cover of `U`.

## References

- Stacks Project, Lemma 59.51.7, <https://stacks.math.columbia.edu/tag/09Z1>
- Stacks Project, Lemma 59.51.6, <https://stacks.math.columbia.edu/tag/03Q8>
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

section CohomologyPresheaf

/-- The free sheaf `Λ[W]` of `Λ`-modules on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ Λ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(Λ[W], F)` is the étale cohomology `H^q(W, F|_W)`. -/
noncomputable def Etale.freeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf _ _

/-- The hypercohomology presheaf of an object `K` of `D⁺(Y_ét, Λ)` relative to `h : Y ⟶ X`:
the presheaf on the small étale site of `X` sending `W` to
`Hom(h^* Λ[W], K[q]) = H^q(W ×_X Y, K|)`, the degree-`q` (hyper)cohomology of the restriction
of `K` to `W ×_X Y`; indeed `h^* Λ[W] = Λ[W ×_X Y]`. For a sheaf `K = F[0]` this is the
presheaf `W ↦ H^q(W ×_X Y, F|)`. -/
noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms, for complexes.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `K ∈ D⁺(Y_ét, Λ)`. Then the `q`-th
cohomology sheaf of `Rh_* K` is, as a sheaf of abelian groups, the sheafification of the
presheaf `W ↦ H^q(W ×_X Y, K|)` on the small étale site of `X`
(`AlgebraicGeometry.Etale.higherDirectImagePresheaf`). The isomorphism is stated as a bare
`Nonempty`, as in the blueprint, which does not specify it. -/
theorem Etale.nonempty_presheafToSheaf_higherDirectImagePresheaf_iso {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Etale.higherDirectImagePresheaf Λ h q K) ≅
      (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
  sorry

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `F` an étale sheaf of `Λ`-modules on
`Y`. Then `R^q h_* F` is, as a sheaf of abelian groups, the sheafification of the presheaf
`W ↦ H^q(W ×_X Y, F|)` on the small étale site of `X`. This is the case `K = F[0]` of
`AlgebraicGeometry.Etale.nonempty_presheafToSheaf_higherDirectImagePresheaf_iso`. -/
theorem Etale.nonempty_presheafToSheaf_higherDirectImagePresheaf_single_iso
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Etale.higherDirectImagePresheaf Λ h q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.higherDirectImage Λ h q F)) :=
  Etale.nonempty_presheafToSheaf_higherDirectImagePresheaf_iso Λ h q _

end CohomologyPresheaf

/-- Blueprint `lemma-weil-pbc-direct-image-filtered-colimit`: Filtered colimits and higher
direct image.

For a quasi-compact quasi-separated morphism `h : Y ⟶ X`, the higher direct image
`F ↦ R^q h_* F` commutes with filtered colimits of sheaves of `Λ`-modules on `Y_ét`:
`colim_i R^q h_* F_i ≅ R^q h_* (colim_i F_i)`. The functor is written out as the degree-`q`
homology of the derived pushforward of a sheaf placed in degree `0`, the functor whose value
at `F` is `AlgebraicGeometry.Etale.higherDirectImage`. -/
theorem Etale.preservesColimitsOfShape_higherDirectImage {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ) (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  sorry

/-- Blueprint `sbc-lem-higher-direct-image-presheaf`, in the vanishing form used for constant
coefficients: Higher direct image as a sheafified cohomology presheaf.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated, let `d : ℕ` and `q : ℕ`. Suppose that for
every `e ∣ d`, every affine scheme `U` étale over `X` and every class
`ξ ∈ H^q(Y ×_X U, ℤ/e)` there is an étale covering `{V i ⟶ U}` such that `ξ` dies after
pullback to every `Y ×_X V i`. Then `R^q h_* (Λ/dΛ) = 0`.

By Stacks `03Q8` the abelian sheaf `R^q h_* (ℤ/e)` is the sheafification of
`U ↦ H^q(Y ×_X U, ℤ/e)` on `X_ét`, and the affine `U` form a basis of `X_ét`, so the hypothesis
says that `R^q h_* (ℤ/e) = 0` for every `e ∣ d`. The underlying abelian group of `Λ/dΛ` is the
filtered colimit of its finitely generated subgroups, which are finite direct sums of cyclic
groups `ℤ/e` with `e ∣ d` (and of copies of `ℤ` when `d = 0`); as `h` is quasi-compact and
quasi-separated, `R^q h_*` commutes with filtered colimits, so the underlying abelian sheaf of
`R^q h_* (Λ/dΛ)` vanishes, and the higher direct images of a sheaf of `Λ`-modules are computed
on its underlying abelian sheaf. -/
@[stacks 03Q8]
theorem Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (d q : ℕ)
    (H : ∀ e : ℕ, e ∣ d → ∀ ⦃U : Scheme.{u}⦄ (u : U ⟶ X) [Etale u] [IsAffine U]
      (ξ : Sheaf.H ((pullback h u).constantZMod e) q),
      ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U), (∀ i, Etale (v i)) ∧
        (∀ x : U, ∃ i y, (v i).base y = x) ∧
        ∀ i, Etale.cohomologyMap (pullback.map h (v i ≫ u) h u (𝟙 Y) (v i) (𝟙 X) (by simp)
          (by simp)) _ q ξ = 0) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) :=
  sorry

end AlgebraicGeometry
