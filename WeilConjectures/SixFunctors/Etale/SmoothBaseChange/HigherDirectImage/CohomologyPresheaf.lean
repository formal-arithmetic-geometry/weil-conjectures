/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Higher direct images as sheafified cohomology presheaves

For `h : Y ⟶ X` and `K ∈ D⁺(Y_ét, Λ)`, the `q`-th cohomology sheaf of `Rh_* K` receives a
canonical map from the presheaf `W ↦ H^q(W ×_X Y, K|)` on the small étale site of `X`; for `h`
quasi-compact and quasi-separated it identifies `R^q h_* K` with the sheafification of that
presheaf. Consequences: higher direct images commute with filtered colimits of sheaves, and a
vanishing criterion for `R^q h_* (Λ/dΛ)`.

## Main definitions

- `AlgebraicGeometry.Etale.higherDirectImagePresheaf`: the presheaf `W ↦ H^q(W ×_X Y, K|)`.
- `AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf`: the canonical map from it to
  `R^q h_* K`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf`: `R^q h_* K` is the
  sheafification of `W ↦ H^q(W ×_X Y, K|)` for a quasi-compact quasi-separated `h`.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`: higher direct images
  along a quasi-compact quasi-separated morphism commute with filtered colimits of sheaves.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`: the
  higher direct image `R^q h_* (Λ/dΛ)` vanishes as soon as every class of
  `H^q(U ×_X Y, ℤ/e)`, for `e ∣ d` and `U` affine étale over `X`, dies on an étale cover of `U`.

## References

- Stacks Project, Lemma 59.51.6, <https://stacks.math.columbia.edu/tag/03Q8>
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

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

/-- Evaluation at the generator: for a sheaf `G` of `Λ`-modules on `X_ét`, the natural map
`Hom(Λ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `Λ[W]` given by
the identity of `W`. -/
noncomputable def Etale.freeSheafSections {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj G ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality X.smallEtaleTopology
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (ModuleCat.free Λ)))
    have h₂ := congr_arg (fun k ↦ k.hom (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))) =
        ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify X.smallEtaleTopology
          (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))

/-- The map `Hom(h^* Fr(W), K[q]) ⟶ Hom(Fr(W), H^q(Rh_* K))`, natural in `W`, for a functor
`Fr : X.Etale ⥤ Sheaf X.smallEtaleTopology A` and a general coefficient category `A`: the
construction of `AlgebraicGeometry.Etale.higherDirectImagePresheafToHom`, which is its value
at the free sheaves. Defining it for a general `A` and instantiating it is much cheaper for the
kernel than writing it out over `ModuleCat Λ`. -/
noncomputable def Etale.higherDirectImagePresheafToHomOfFunctor (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}}
    (Fr : X.Etale ⥤ Sheaf X.smallEtaleTopology A) (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (Fr ⋙ (h)^*[A] ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧) ⟶
      Fr.op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[A]).obj K)) :=
  Functor.whiskerRight (NatTrans.op (Functor.whiskerLeft Fr
    (((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom))
      (preadditiveYoneda.obj (K⟦q⟧)) ≫
  ({ app W := AddCommGrpCat.ofHom
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus A h).homAddEquiv
        _ _).toAddMonoidHom
     naturality W W' g := by
      ext f
      exact (Etale.derivedUpperStarLowerStarAdjunctionPlus A
        h).homEquiv_naturality_left _ _ } :
    (Fr ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
      D+((h)^*[A])).op ⋙ preadditiveYoneda.obj (K⟦q⟧) ⟶
    (Fr ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj (R+((h)_*[A]).obj (K⟦q⟧))) ≫
  ({ app W := AddCommGrpCat.ofHom <|
      (Preadditive.leftComp _
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
        (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
     naturality W W' g := by
      have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := Sheaf X.smallEtaleTopology A) 0).inv.naturality
          (Fr.map g.unop)
      dsimp at hs
      ext f
      revert f
      change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj (Fr.obj W.unop) ⟶
          R+((h)_*[A]).obj (K⟦q⟧),
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
          (DerivedCategory.Plus.homologyFunctor _ 0).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map (Fr.map g.unop) ≫ f) =
        Fr.map g.unop ≫
          (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
            (Fr.obj W.unop) ≫
          (DerivedCategory.Plus.homologyFunctor _ 0).map f
      intro f
      rw [Functor.map_comp, ← reassoc_of% hs] } :
    (Fr ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj (R+((h)_*[A]).obj (K⟦q⟧)) ⟶
    Fr.op ⋙ preadditiveYoneda.obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      (R+((h)_*[A]).obj (K⟦q⟧)))) ≫
  Functor.whiskerLeft Fr.op (preadditiveYoneda.map
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[A]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _))

/-- The map `Hom(h^* Λ[W], K[q]) ⟶ Hom(Λ[W], H^q(Rh_* K))`, natural in `W`: the adjunction
`Lh^* ⊣ Rh_*` (using `Lh^*(Λ[W][0]) ≅ (h^* Λ[W])[0]`), then the degree-`0` homology, using
`H^0(Λ[W][0]) ≅ Λ[W]` and `H^0((Rh_* K)[q]) ≅ H^q(Rh_* K)`. -/
noncomputable def Etale.higherDirectImagePresheafToHom {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.higherDirectImagePresheafToHomOfFunctor _ (Etale.freeSheaf Λ X) h q K

/-- The canonical map from the presheaf `W ↦ H^q(W ×_X Y, K|)` to the sheaf `H^q(Rh_* K)`, of
presheaves of abelian groups on `X_ét`: a class `Λ[W ×_X Y][0] ⟶ K[q]` goes, by adjunction, to
a map `Λ[W][0] ⟶ (Rh_* K)[q]`, then to `Λ[W] ⟶ H^q(Rh_* K)` on degree-`0` homology, and then to
the section of `H^q(Rh_* K)` over `W` that it picks out. On a complex of sheaves this is the map
`H^q(Γ(W ×_X Y, I^•)) ⟶ Γ(W, H^q(h_* I^•))` for an injective resolution `I^•` of `K`. -/
noncomputable def Etale.higherDirectImagePresheafToSheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
  Etale.higherDirectImagePresheafToHom Λ h q K ≫ Etale.freeSheafSections Λ _

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms, for complexes.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `K ∈ D⁺(Y_ét, Λ)`. Then the `q`-th
cohomology sheaf of `Rh_* K` is, as a sheaf of abelian groups, the sheafification of the
presheaf `W ↦ H^q(W ×_X Y, K|)` on the small étale site of `X`
(`AlgebraicGeometry.Etale.higherDirectImagePresheaf`): the canonical map
`AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf` induces an isomorphism from the
sheafification. The hypotheses on `h` are those of the blueprint; the statement holds for any
`h` (Stacks `072W`). -/
theorem Etale.isIso_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q K)) :=
  sorry

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `F` an étale sheaf of `Λ`-modules on
`Y`. Then `R^q h_* F` is, as a sheaf of abelian groups, the sheafification of the presheaf
`W ↦ H^q(W ×_X Y, F|)` on the small étale site of `X`, via the canonical map
`AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf`. This is the case `K = F[0]` of
`AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf`. -/
theorem Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  Etale.isIso_higherDirectImagePresheafToSheaf Λ h q _

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
