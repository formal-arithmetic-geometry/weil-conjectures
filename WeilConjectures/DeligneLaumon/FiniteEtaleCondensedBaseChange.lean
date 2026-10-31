/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Finite étale base change with condensed coefficients

Source: Stacks Project, Tags 0959 and 095B, `etale-cohomology.tex`, and Tag 04HN,
`etale.tex`; the pro-étale internal-module extension in the first paragraph of the latest
blueprint proof of `lem-a1-finite-map-purity`
(blueprint: lem-a1-finite-etale-condensed-base-change).

The exchange is the existing `lowerStarBaseChange`, the mate of
`upperStarSquareComparison`. Its type already includes naturality in the module, and
`lowerStarBaseChange_app_paste` supplies composition of base changes. The chart statement
uses the existing counit-defined `stalkLowerStarProj` for arbitrary test schemes, rather
than only for geometric points. Its two product maps and its projection equations specify
the componentwise finite-product description. The diagram-isomorphism statement records
transport under isomorphisms of all four schemes in a Cartesian diagram.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing


attribute [local irreducible] upperStar lowerStar upperStarComp
  upperStarLowerStarAdjunction lowerStarBaseChange upperStarSquareComparison upperStarCongr

private theorem splitProjection_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y U : Scheme.{u}} (f : X ⟶ Y) (v : U ⟶ Y) (t : U ⟶ X)
    (w : t ≫ f = v)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (((eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t f).hom.app
        ((lowerStar Λ f).obj M) ≫
      (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ f).counit.app M)) =
        stalkLowerStarProj Λ w M := by
  subst v
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  rw [stalkLowerStarProj_eq]
  simp only [upperStarCongr_self, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem isIso_lift_of_components_eq
    {C : Type*} [Category C] {J : Type*} {A : C} {B : J → C} [HasProduct B]
    {p q : ∀ j, A ⟶ B j} (h : ∀ j, p j = q j) (hp : IsIso (Pi.lift p)) :
    IsIso (Pi.lift q) := by
  have he : p = q := funext h
  subst q
  exact hp

private theorem splitProjection_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y U : Scheme.{u}} (f : X ⟶ Y)
    (v : U ⟶ Y) [WeaklyEtale v]
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback f v)
      (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    IsIso (Pi.lift (fun j ↦ stalkLowerStarProj Λ.X (w j) M)) := by
  exact isIso_lift_of_components_eq
    (fun j ↦ splitProjection_eq Λ.X f v (t j) (w j) M)
    (splitProEtaleModuleProductMap_isIso Λ.X f v n t w hc M)


private theorem transport_hom
    {C : Type*} [Category C] {I J : Type*} (P : I → C) (Q : J → C)
    (R : I → J → Prop) (b : ∀ i j, R i j → (P i ⟶ Q j))
    {i₁ i₂ : I} {j₁ j₂ : J} (h₁ : R i₁ j₁) (h₂ : R i₂ j₂)
    (e : i₁ = i₂) (e' : j₁ = j₂) :
    eqToHom (congrArg P e) ≫ b i₂ j₂ h₂ =
      b i₁ j₁ h₁ ≫ eqToHom (congrArg Q e') := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem baseChange_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X}
    (sq₁ : CommSq g₁' f' f g₁) (sq₂ : CommSq g₂' f' f g₂)
    (e : g₁ = g₂) (e' : g₁' = g₂')
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarCongr Λ e).hom.app ((lowerStar Λ f).obj M) ≫
        (lowerStarBaseChange Λ sq₂).app M =
      (lowerStarBaseChange Λ sq₁).app M ≫
        (lowerStar Λ f').map ((upperStarCongr Λ e').hom.app M) := by
  have h := transport_hom
    (fun k : Y' ⟶ Y ↦ (upperStar Λ k).obj ((lowerStar Λ f).obj M))
    (fun k : X' ⟶ X ↦ (lowerStar Λ f').obj ((upperStar Λ k).obj M))
    (fun k k' ↦ CommSq k' f' f k)
    (fun _ _ sq ↦ (lowerStarBaseChange Λ sq).app M) sq₁ sq₂ e e'
  simpa only [upperStarCongr_hom_app_eq_eqToHom, eqToHom_map] using h

private theorem congr_symm_inv_nat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (upperStarCongr Λ e.symm).inv = (upperStarCongr Λ e).hom := by
  subst e
  simp only [upperStarCongr_self, Iso.refl_inv, Iso.refl_hom]

private theorem squareComparison_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    (upperStarSquareComparison Λ sq).inv =
      (upperStarComp Λ g' f).inv ≫
        (upperStarCongr Λ sq.w).hom ≫ (upperStarComp Λ f' g).hom := by
  rw [upperStarSquareComparison_eq]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [congr_symm_inv_nat Λ sq.w]

private theorem cube_mate_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₂ A₃ B B' : D} {R₀ R₁ R₂ R₃ : C}
    (l₁ : A₀ ≅ A₁) (l₂ : A₂ ≅ A₃) (lc : A₀ ≅ A₂)
    (r₁ : R₀ ≅ R₁) (r₂ : R₂ ≅ R₃) (rc : R₀ ≅ R₂)
    (k₁ : A₁ ⟶ B) (k₂ : B ⟶ F.obj R₁)
    (k₃ : A₃ ⟶ B') (k₄ : B' ⟶ F.obj R₃)
    (β₁ : A₀ ⟶ F.obj R₀) (β₂ : A₂ ⟶ F.obj R₂)
    (hp₁ : l₁.hom ≫ k₁ ≫ k₂ = β₁ ≫ F.map r₁.hom)
    (hp₂ : l₂.hom ≫ k₃ ≫ k₄ = β₂ ≫ F.map r₂.hom)
    (he : lc.hom ≫ β₂ = β₁ ≫ F.map rc.hom) :
    k₁ ≫ k₂ ≫ F.map (r₁.inv ≫ rc.hom ≫ r₂.hom) =
      (l₁.inv ≫ lc.hom ≫ l₂.hom) ≫ k₃ ≫ k₄ := by
  apply (cancel_epi l₁.hom).1
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hp₁, ← F.map_comp_assoc, Iso.hom_inv_id,
    F.map_id, Category.id_comp, ← reassoc_of% he, hp₂]

private theorem cube_mate_comparison_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : C ⥤ D) (G : A ⥤ B)
    (L₀ L₁ L₂ L₃ : B ⥤ D) (R₀ R₁ R₂ R₃ : A ⥤ C) (K K' : A ⥤ D)
    (l₁ : L₀ ≅ L₁) (l₂ : L₂ ≅ L₃) (lc : L₀ ≅ L₂)
    (r₁ : R₀ ≅ R₁) (r₂ : R₂ ≅ R₃) (rc : R₀ ≅ R₂)
    (sl : L₁ ≅ L₃) (sr : R₁ ≅ R₃)
    (hl : sl.hom = l₁.inv ≫ lc.hom ≫ l₂.hom)
    (hr : sr.hom = r₁.inv ≫ rc.hom ≫ r₂.hom)
    (k₁ : ∀ M, L₁.obj (G.obj M) ⟶ K.obj M)
    (k₂ : ∀ M, K.obj M ⟶ F.obj (R₁.obj M))
    (k₃ : ∀ M, L₃.obj (G.obj M) ⟶ K'.obj M)
    (k₄ : ∀ M, K'.obj M ⟶ F.obj (R₃.obj M))
    (β₁ : ∀ M, L₀.obj (G.obj M) ⟶ F.obj (R₀.obj M))
    (β₂ : ∀ M, L₂.obj (G.obj M) ⟶ F.obj (R₂.obj M))
    (hp₁ : ∀ M, l₁.hom.app (G.obj M) ≫ k₁ M ≫ k₂ M = β₁ M ≫ F.map (r₁.hom.app M))
    (hp₂ : ∀ M, l₂.hom.app (G.obj M) ≫ k₃ M ≫ k₄ M = β₂ M ≫ F.map (r₂.hom.app M))
    (he : ∀ M, lc.hom.app (G.obj M) ≫ β₂ M = β₁ M ≫ F.map (rc.hom.app M))
    (M : A) : k₁ M ≫ k₂ M ≫ F.map (sr.hom.app M) =
      sl.hom.app (G.obj M) ≫ k₃ M ≫ k₄ M := by
  rw [hl, hr]
  simp only [NatTrans.comp_app]
  exact cube_mate_eq F (l₁.app (G.obj M)) (l₂.app (G.obj M)) (lc.app (G.obj M))
    (r₁.app M) (r₂.app M) (rc.app M) _ _ _ _ _ _ (hp₁ M) (hp₂ M) (he M)

private theorem isIso_of_product_coordinates
    {C : Type _} {D : Type _} [Category C] [Category D]
    {J : Type _} (F : C ⥤ D)
    {A : C} {B S : D} {X : J → C} {Y : J → D}
    [HasProduct X] [HasProduct Y] [HasProduct (fun j ↦ F.obj (X j))]
    [PreservesLimit (Discrete.functor X) F]
    (p : ∀ j, A ⟶ X j) [IsIso (Pi.lift p)]
    (q : ∀ j, B ⟶ Y j) [IsIso (Pi.lift q)]
    (e : S ≅ F.obj A) (r : ∀ j, F.obj (X j) ≅ Y j)
    (k : S ⟶ B)
    (hk : ∀ j, k ≫ q j = e.hom ≫ F.map (p j) ≫ (r j).hom) : IsIso k := by
  have hfac : k ≫ Pi.lift q = e.hom ≫ F.map (Pi.lift p) ≫
      piComparison F X ≫ Limits.Pi.map (fun j ↦ (r j).hom) := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, Pi.lift_π, Pi.map_π, piComparison_comp_π_assoc,
      ← F.map_comp_assoc, Pi.lift_π]
    exact hk j
  have : IsIso (Limits.Pi.map (fun j ↦ (r j).hom)) := by
    change IsIso (limMap (Discrete.natTrans
      (F := Discrete.functor (fun j ↦ F.obj (X j))) (G := Discrete.functor Y)
      (fun j ↦ (r j.as).hom)))
    infer_instance
  have : IsIso (k ≫ Pi.lift q) := by rw [hfac]; infer_instance
  exact IsIso.of_isIso_comp_right k (Pi.lift q)


private theorem isIso_of_chart_arrows
    {C D E : Type*} [Category C] [Category D] [Category E]
    {J : Type*} [HasProductsOfShape J D] [HasProductsOfShape J E]
    (F : D ⥤ E) [PreservesLimitsOfShape (Discrete J) F]
    (P₀ P₁ P₂ P₅ : C ⥤ E) (V : C ⥤ D)
    (X : J → C ⥤ D) (Y : J → C ⥤ E)
    (c₁ : ∀ M, P₀.obj M ⟶ P₁.obj M)
    (cy : ∀ M, P₀.obj M ⟶ P₅.obj M)
    (chv : ∀ M, P₅.obj M ⟶ F.obj (V.obj M))
    (r : ∀ M j, F.obj ((X j).obj M) ⟶ (Y j).obj M)
    (k : ∀ M, P₁.obj M ⟶ P₂.obj M)
    (p : ∀ M j, V.obj M ⟶ (X j).obj M)
    (q : ∀ M j, P₂.obj M ⟶ (Y j).obj M)
    (hc₁ : ∀ M, IsIso (c₁ M)) (hcy : ∀ M, IsIso (cy M))
    (hchv : ∀ M, IsIso (chv M)) (hr : ∀ M j, IsIso (r M j))
    (hp : ∀ M, IsIso (Pi.lift (p M))) (hq : ∀ M, IsIso (Pi.lift (q M)))
    (hc : ∀ M j, c₁ M ≫ k M ≫ q M j = cy M ≫ chv M ≫ F.map (p M j) ≫ r M j)
    (M : C) : IsIso (k M) := by
  let := hc₁ M
  let := hcy M
  let := hchv M
  let := hr M
  let := hp M
  let := hq M
  apply isIso_of_product_coordinates F (p M) (q M)
    ((asIso (c₁ M)).symm ≪≫ asIso (cy M) ≪≫ asIso (chv M))
    (fun j ↦ asIso (r M j))
  intro j
  apply (cancel_epi (c₁ M)).1
  simpa only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc] using hc M j

private theorem splitChart_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Etale f] (y : Y) :
    ∃ (U : Scheme.{u}) (v : U ⟶ Y), Etale v ∧ y ∈ Set.range v ∧
      ∃ (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v),
        Nonempty (IsColimit (Cofan.mk (pullback f v)
          (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j)))) := by
  classical
  obtain ⟨U, v, u, hv, hu, J, V, ι, hJ, hcol, -, he⟩ :=
    finite_etale_etale_local_split f y
  let : Finite J := hJ
  choose e he using he
  obtain ⟨n, ⟨a⟩⟩ := Finite.exists_equiv_fin J
  let k (j : J) := (e j).inv ≫ ι j
  have hk (j : J) : k j ≫ pullback.snd f v = 𝟙 U := by
    simp only [k, Category.assoc, ← he j, Iso.inv_hom_id]
  let t (j : Fin n) := k (a.symm j) ≫ pullback.fst f v
  have w (j : Fin n) : t j ≫ f = v := by
    dsimp only [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, Category.id_comp]
  have hb (j : Fin n) : k (a.symm j) =
      pullback.lift (t j) (𝟙 U) (by simpa using w j) := by
    apply pullback.hom_ext
    · simp only [t, pullback.lift_fst]
    · simp only [hk, pullback.lift_snd]
  have hc₀ : IsColimit (Cofan.mk (pullback f v) k) :=
    (IsColimit.precomposeHomEquiv (Discrete.natIso (F := Discrete.functor (fun _ : J ↦ U))
      (G := Discrete.functor V) (fun j ↦ (e j.as).symm))
      (Cofan.mk (pullback f v) ι)).symm hcol.some
  have hc₁ := (Cofan.isColimitEquivOfEquiv a.symm
    (Cofan.mk (pullback f v) k)) hc₀
  refine ⟨U, v, hv, ⟨u, hu⟩, n, t, w, ⟨IsColimit.ofIsoColimit hc₁ ?_⟩⟩
  refine Cofan.ext (Iso.refl _) (fun j ↦ ?_)
  change k (a.symm j) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact hb j

private theorem splitChart_baseChange
    {X Y X' Y' U U' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
    {v : U ⟶ Y} {v' : U' ⟶ Y'} {h : U' ⟶ U}
    (hs : IsPullback h v' v g)
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback f v)
      (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j))))) :
    ∃ (t' : Fin n → (U' ⟶ X')) (w' : ∀ j, t' j ≫ f' = v'),
      (∀ j, t' j ≫ g' = h ≫ t j) ∧
      Nonempty (IsColimit (Cofan.mk (pullback f' v')
        (fun j ↦ pullback.lift (t' j) (𝟙 U') (by simpa using w' j)))) := by
  let t' (j : Fin n) := hsq.lift (h ≫ t j) v' (by
    rw [Category.assoc, w j, hs.w])
  have w' (j : Fin n) : t' j ≫ f' = v' := hsq.lift_snd _ _ _
  have ht (j : Fin n) : t' j ≫ g' = h ≫ t j := hsq.lift_fst _ _ _
  let i (j : Fin n) := pullback.lift (t j) (𝟙 U) (by simpa using w j)
  let i' (j : Fin n) := pullback.lift (t' j) (𝟙 U') (by simpa using w' j)
  let d : pullback f' v' ⟶ pullback f v :=
    pullback.lift (pullback.fst f' v' ≫ g') (pullback.snd f' v' ≫ h) (by
      rw [Category.assoc, hsq.w, ← Category.assoc, pullback.condition]
      simp only [Category.assoc, hs.w])
  have hd : IsPullback d (pullback.snd f' v') (pullback.snd f v) h := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f v)
    · simpa only [d, pullback.lift_fst, hs.w] using
        (IsPullback.of_hasPullback f' v').paste_horiz hsq
    · exact pullback.lift_snd _ _ _
  have hj (j : Fin n) : IsPullback h (𝟙 U') (i j ≫ pullback.snd f v) h := by
    have hh : i j ≫ pullback.snd f v = 𝟙 U := pullback.lift_snd _ _ _
    rw [hh]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc.some
  refine ⟨t', w', ht, ?_⟩
  exact hu.nonempty_isColimit_of_isPullback_right
    (fun j ↦ i j ≫ pullback.snd f v) (pullback.snd f v) h
    (fun _ ↦ h) (fun _ ↦ 𝟙 U') hj hd (Cofan.mk _ i') (Iso.refl _)

private theorem module_isIso_of_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {Y : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (v : ∀ i, U i ⟶ Y)
    [∀ i, WeaklyEtale (v i)]
    (hv : Presieve.ofArrows U v ∈ Scheme.proetalePrecoverage Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)}
    (k : M ⟶ N) (hk : ∀ i, IsIso ((upperStar Λ.X (v i)).map k)) : IsIso k := by
  have : IsIso ((Mod.forget (condensedRingObj Λ.X Y)).map k) := by
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} k.hom v hv
    intro i
    have := hk i
    have h : IsIso ((ProEtale.upperStar Ab.{u + 1} (v i)).map k.hom) :=
      (NatIso.isIso_map_iff (upperStarForgetIso Λ.X (v i)) k).2 (by
        change IsIso ((Mod.forget _).map ((upperStar Λ.X (v i)).map k))
        infer_instance)
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (v i) inferInstance)
      k.hom).1 h
  exact isIso_of_reflects_iso k (Mod.forget _)

-- Keep the coordinate algebra abstract to avoid unfolding the module pullback functors.
private theorem component_eq_of_functor_projections
    {C D : Type*} [Category C] [Category D]
    (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ : C ⥤ D)
    (c₁ : ∀ M, P₀.obj M ⟶ P₁.obj M) (k : ∀ M, P₁.obj M ⟶ P₂.obj M)
    (q : ∀ M, P₂.obj M ⟶ P₃.obj M) (pxy : ∀ M, P₀.obj M ⟶ P₄.obj M)
    (cg : ∀ M, P₄.obj M ⟶ P₃.obj M) (cy : ∀ M, P₀.obj M ⟶ P₅.obj M)
    (py : ∀ M, P₅.obj M ⟶ P₄.obj M) (pht : ∀ M, P₅.obj M ⟶ P₆.obj M)
    (ct : ∀ M, P₆.obj M ⟶ P₄.obj M) (chv : ∀ M, P₅.obj M ⟶ P₇.obj M)
    (uhp : ∀ M, P₇.obj M ⟶ P₈.obj M) (chi : ∀ M, P₈.obj M ⟶ P₆.obj M)
    (h₁ : ∀ M, c₁ M ≫ k M ≫ q M = pxy M ≫ cg M)
    (h₂ : ∀ M, cy M ≫ py M = pxy M)
    (h₃ : ∀ M, pht M ≫ ct M = py M)
    (h₄ : ∀ M, pht M = chv M ≫ uhp M ≫ chi M) (M : C) :
    c₁ M ≫ k M ≫ q M = cy M ≫ chv M ≫ uhp M ≫ chi M ≫ ct M ≫ cg M := by
  rw [h₁, ← h₂, ← h₃, h₄]
  simp only [Category.assoc]

private theorem chart_components
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' U U' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f g) (v : U ⟶ Y)
    (v' : U' ⟶ Y') (h : U' ⟶ U) (hs : IsPullback h v' v g)
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (t' : Fin n → (U' ⟶ X')) (w' : ∀ j, t' j ≫ f' = v')
    (ht : ∀ j, t' j ≫ g' = h ≫ t j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    ∀ j : Fin n,
        (upperStarComp Λ.X v' g).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app M) ≫
            stalkLowerStarProj Λ.X (w' j) ((upperStar Λ.X g').obj M) =
          (upperStarCongr Λ.X hs.w.symm).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStarComp Λ.X h v).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStar Λ.X h).map (stalkLowerStarProj Λ.X (w j) M) ≫
            (upperStarComp Λ.X h (t j)).inv.app M ≫
            (upperStarCongr Λ.X (ht j).symm).hom.app M ≫
            (upperStarComp Λ.X (t' j) g').hom.app M := by
  intro j
  have hxy : (t' j ≫ g') ≫ f = v' ≫ g := by
    rw [ht j, Category.assoc, w j, hs.w]
  have hxy' : (h ≫ t j) ≫ f = h ≫ v := by
    rw [Category.assoc, w j]
  have hy : (t' j ≫ g') ≫ f = h ≫ v := by
    rw [ht j, Category.assoc, w j]
  exact component_eq_of_functor_projections
    ((lowerStar Λ.X f) ⋙ upperStar Λ.X (v' ≫ g))
    ((lowerStar Λ.X f) ⋙ upperStar Λ.X g ⋙ upperStar Λ.X v')
    ((upperStar Λ.X g') ⋙ lowerStar Λ.X f' ⋙ upperStar Λ.X v')
    ((upperStar Λ.X g') ⋙ upperStar Λ.X (t' j))
    (upperStar Λ.X (t' j ≫ g'))
    ((lowerStar Λ.X f) ⋙ upperStar Λ.X (h ≫ v))
    (upperStar Λ.X (h ≫ t j))
    ((lowerStar Λ.X f) ⋙ upperStar Λ.X v ⋙ upperStar Λ.X h)
    ((upperStar Λ.X (t j)) ⋙ upperStar Λ.X h)
    (fun N ↦ (upperStarComp Λ.X v' g).hom.app ((lowerStar Λ.X f).obj N))
    (fun N ↦ (upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app N))
    (fun N ↦ stalkLowerStarProj Λ.X (w' j) ((upperStar Λ.X g').obj N))
    (fun N ↦ stalkLowerStarProj Λ.X hxy N)
    (fun N ↦ (upperStarComp Λ.X (t' j) g').hom.app N)
    (fun N ↦ (upperStarCongr Λ.X hs.w.symm).hom.app ((lowerStar Λ.X f).obj N))
    (fun N ↦ stalkLowerStarProj Λ.X hy N)
    (fun N ↦ stalkLowerStarProj Λ.X hxy' N)
    (fun N ↦ (upperStarCongr Λ.X (ht j).symm).hom.app N)
    (fun N ↦ (upperStarComp Λ.X h v).hom.app ((lowerStar Λ.X f).obj N))
    (fun N ↦ (upperStar Λ.X h).map (stalkLowerStarProj Λ.X (w j) N))
    (fun N ↦ (upperStarComp Λ.X h (t j)).inv.app N)
    (fun N ↦ stalkLowerStarProj_lowerStarBaseChange' Λ.X hsq.toCommSq (w' j) hxy N)
    (fun N ↦ upperStarCongr_hom_app_stalkLowerStarProj Λ.X hs.w.symm hxy hy N)
    (fun N ↦ stalkLowerStarProj_upperStarCongr_hom_app Λ.X (ht j).symm hxy' hy N)
    (fun N ↦ stalkLowerStarProj_comp_left Λ.X h (w j) hxy' N) M

/-- On a splitting chart, and its pulled-back splitting, the two counit projection maps
are finite-product isomorphisms and the exchange has the componentwise pullback formula.
The integer `n` may be zero. The maps `t'` are the transported sheets, as expressed by `ht`.

Source: Stacks Project, Tag 095B, split-cover computation, and Tag 04HN; latest blueprint,
`lem-a1-finite-map-purity`, first paragraph
(blueprint: lem-a1-finite-etale-condensed-base-change).

Proof in words. Apply the split pro-étale module product theorem directly to `f` and `v`,
and to `f'` and `v'`. Its projections agree with `stalkLowerStarProj` by the counit formula;
`v'` is étale by base change. For each sheet, the counit equation
`stalkLowerStarProj_lowerStarBaseChange'` gives the component of the exchange. Transport
its base map using `hs.w`, transport its top map using `ht`, and apply
`stalkLowerStarProj_comp_left`. These four identities combine into the displayed chart
equation. This includes an empty family of sheets. -/
theorem finiteEtaleCondensedBaseChange_chart
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' U U' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsFinite f] [Etale f]
    (hsq : IsPullback g' f' f g) (v : U ⟶ Y) [Etale v]
    (v' : U' ⟶ Y') (h : U' ⟶ U) (hs : IsPullback h v' v g)
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (t' : Fin n → (U' ⟶ X')) (w' : ∀ j, t' j ≫ f' = v')
    (ht : ∀ j, t' j ≫ g' = h ≫ t j)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback f v)
      (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j)))))
    (hc' : Nonempty (IsColimit (Cofan.mk (pullback f' v')
      (fun j ↦ pullback.lift (t' j) (𝟙 U') (by simpa using w' j)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    IsIso (Pi.lift (fun j ↦ stalkLowerStarProj Λ.X (w j) M)) ∧
      IsIso (Pi.lift (fun j ↦
        stalkLowerStarProj Λ.X (w' j) ((upperStar Λ.X g').obj M))) ∧
      ∀ j : Fin n,
        (upperStarComp Λ.X v' g).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app M) ≫
            stalkLowerStarProj Λ.X (w' j) ((upperStar Λ.X g').obj M) =
          (upperStarCongr Λ.X hs.w.symm).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStarComp Λ.X h v).hom.app ((lowerStar Λ.X f).obj M) ≫
            (upperStar Λ.X h).map (stalkLowerStarProj Λ.X (w j) M) ≫
            (upperStarComp Λ.X h (t j)).inv.app M ≫
            (upperStarCongr Λ.X (ht j).symm).hom.app M ≫
            (upperStarComp Λ.X (t' j) g').hom.app M := by
  let : Etale v' := MorphismProperty.of_isPullback (P := @Etale) hs inferInstance
  refine ⟨splitProjection_isIso Λ f v n t w hc M,
    splitProjection_isIso Λ f' v' n t' w' hc' _, ?_⟩
  exact chart_components Λ hsq v v' h hs n t w t' w' ht M

private theorem sheets_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' U U' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsFinite f] [Etale f]
    (hsq : IsPullback g' f' f g) (v : U ⟶ Y) [Etale v]
    (v' : U' ⟶ Y') (h : U' ⟶ U) (hs : IsPullback h v' v g)
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback f v)
      (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j)))))
    (t' : Fin n → (U' ⟶ X')) (w' : ∀ j, t' j ≫ f' = v')
    (ht : ∀ j, t' j ≫ g' = h ≫ t j)
    (hc' : Nonempty (IsColimit (Cofan.mk (pullback f' v')
      (fun j ↦ pullback.lift (t' j) (𝟙 U') (by simpa using w' j)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    IsIso ((upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app M)) := by
  let : Etale v' := MorphismProperty.of_isPullback (P := @Etale) hs inferInstance
  exact isIso_of_chart_arrows (upperStar Λ.X h)
    (lowerStar Λ.X f ⋙ upperStar Λ.X (v' ≫ g))
    (lowerStar Λ.X f ⋙ upperStar Λ.X g ⋙ upperStar Λ.X v')
    (upperStar Λ.X g' ⋙ lowerStar Λ.X f' ⋙ upperStar Λ.X v')
    (lowerStar Λ.X f ⋙ upperStar Λ.X (h ≫ v))
    (lowerStar Λ.X f ⋙ upperStar Λ.X v)
    (fun j ↦ upperStar Λ.X (t j))
    (fun j ↦ upperStar Λ.X g' ⋙ upperStar Λ.X (t' j))
    (fun N ↦ (upperStarComp Λ.X v' g).hom.app ((lowerStar Λ.X f).obj N))
    (fun N ↦ (upperStarCongr Λ.X hs.w.symm).hom.app ((lowerStar Λ.X f).obj N))
    (fun N ↦ (upperStarComp Λ.X h v).hom.app ((lowerStar Λ.X f).obj N))
    (fun N j ↦ (upperStarComp Λ.X h (t j)).inv.app N ≫
      (upperStarCongr Λ.X (ht j).symm).hom.app N ≫
      (upperStarComp Λ.X (t' j) g').hom.app N)
    (fun N ↦ (upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app N))
    (fun N j ↦ stalkLowerStarProj Λ.X (w j) N)
    (fun N j ↦ stalkLowerStarProj Λ.X (w' j) ((upperStar Λ.X g').obj N))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    (fun _ _ ↦ inferInstance)
    (fun N ↦ splitProjection_isIso Λ f v n t w hc N)
    (fun N ↦ splitProjection_isIso Λ f' v' n t' w' hc' ((upperStar Λ.X g').obj N))
    (chart_components Λ hsq v v' h hs n t w t' w' ht) M


private theorem baseChange_isIso_on_chart
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' U U' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsFinite f] [Etale f]
    (hsq : IsPullback g' f' f g) (v : U ⟶ Y) [Etale v]
    (v' : U' ⟶ Y') (h : U' ⟶ U) (hs : IsPullback h v' v g)
    (n : ℕ) (t : Fin n → (U ⟶ X)) (w : ∀ j, t j ≫ f = v)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback f v)
      (fun j ↦ pullback.lift (t j) (𝟙 U) (by simpa using w j)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    IsIso ((upperStar Λ.X v').map ((lowerStarBaseChange Λ.X hsq.toCommSq).app M)) := by
  obtain ⟨t', w', ht, hc'⟩ := splitChart_baseChange hsq hs n t w hc
  exact sheets_isIso Λ hsq v v' h hs n t w hc t' w' ht hc' M

/-- Exchanges respect an isomorphism of Cartesian diagrams. The two routes around the
cube agree, using the canonical exchanges along the vertical diagram isomorphisms.
No ground-field linearity is imposed on any of the four isomorphisms.

Source: Stacks Project, Tag 0959, canonical pullback map, and the ordinary mate whiskering
and pasting calculation of node steps 1 and 6
(blueprint: lem-a1-finite-etale-condensed-base-change).

Proof in words. Paste the original square with the primed vertical face, and the
unprimed vertical face with the new square. The outer base maps are identified by `sb.w`
and their top maps by `st.w`. Equality transport identifies the two outer exchanges.
Apply `lowerStarBaseChange_app_paste` twice and cancel the composition isomorphisms.
Expanding the two square comparisons gives the claimed equality of natural
transformations, hence the component at `M`. This calculation is in absolute schemes,
so it includes semilinear isomorphisms. -/
theorem finiteEtaleCondensedBaseChange_diagramIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' X₁ Y₁ X₁' Y₁' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁' ⟶ Y₁} {f₁' : X₁' ⟶ Y₁'} {g₁' : X₁' ⟶ X₁}
    [IsFinite f] [Etale f] (hsq : IsPullback g' f' f g)
    (hsq₁ : IsPullback g₁' f₁' f₁ g₁)
    (a : X₁ ≅ X) (b : Y₁ ≅ Y) (a' : X₁' ≅ X') (b' : Y₁' ≅ Y')
    (sv : CommSq a.hom f₁ f b.hom) (sv' : CommSq a'.hom f₁' f' b'.hom)
    (st : CommSq a'.hom g₁' g' a.hom) (sb : CommSq b'.hom g₁ g b.hom)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    (upperStar Λ.X b'.hom).map ((lowerStarBaseChange Λ.X hsq.toCommSq).app M) ≫
        (lowerStarBaseChange Λ.X sv').app ((upperStar Λ.X g').obj M) ≫
        (lowerStar Λ.X f₁').map ((upperStarSquareComparison Λ.X st).inv.app M) =
      (upperStarSquareComparison Λ.X sb).inv.app ((lowerStar Λ.X f).obj M) ≫
        (upperStar Λ.X g₁).map ((lowerStarBaseChange Λ.X sv).app M) ≫
        (lowerStarBaseChange Λ.X hsq₁.toCommSq).app ((upperStar Λ.X a.hom).obj M) := by
  let q₁ : CommSq (a'.hom ≫ g') f₁' f (b'.hom ≫ g) :=
    ⟨by rw [Category.assoc, hsq.w, ← Category.assoc, sv'.w, Category.assoc]⟩
  let q₂ : CommSq (g₁' ≫ a.hom) f₁' f (g₁ ≫ b.hom) :=
    ⟨by rw [Category.assoc, sv.w, ← Category.assoc, hsq₁.w, Category.assoc]⟩
  exact cube_mate_comparison_app (lowerStar Λ.X f₁') (lowerStar Λ.X f)
    (upperStar Λ.X (b'.hom ≫ g))
    (upperStar Λ.X g ⋙ upperStar Λ.X b'.hom)
    (upperStar Λ.X (g₁ ≫ b.hom))
    (upperStar Λ.X b.hom ⋙ upperStar Λ.X g₁)
    (upperStar Λ.X (a'.hom ≫ g'))
    (upperStar Λ.X g' ⋙ upperStar Λ.X a'.hom)
    (upperStar Λ.X (g₁' ≫ a.hom))
    (upperStar Λ.X a.hom ⋙ upperStar Λ.X g₁')
    (upperStar Λ.X g' ⋙ lowerStar Λ.X f' ⋙ upperStar Λ.X b'.hom)
    (upperStar Λ.X a.hom ⋙ lowerStar Λ.X f₁ ⋙ upperStar Λ.X g₁)
    (upperStarComp Λ.X b'.hom g) (upperStarComp Λ.X g₁ b.hom)
    (upperStarCongr Λ.X sb.w)
    (upperStarComp Λ.X a'.hom g') (upperStarComp Λ.X g₁' a.hom)
    (upperStarCongr Λ.X st.w)
    (upperStarSquareComparison Λ.X sb).symm (upperStarSquareComparison Λ.X st).symm
    (squareComparison_inv Λ.X sb) (squareComparison_inv Λ.X st)
    (fun N ↦ (upperStar Λ.X b'.hom).map ((lowerStarBaseChange Λ.X hsq.toCommSq).app N))
    (fun N ↦ (lowerStarBaseChange Λ.X sv').app ((upperStar Λ.X g').obj N))
    (fun N ↦ (upperStar Λ.X g₁).map ((lowerStarBaseChange Λ.X sv).app N))
    (fun N ↦ (lowerStarBaseChange Λ.X hsq₁.toCommSq).app ((upperStar Λ.X a.hom).obj N))
    (fun N ↦ (lowerStarBaseChange Λ.X q₁).app N)
    (fun N ↦ (lowerStarBaseChange Λ.X q₂).app N)
    (lowerStarBaseChange_app_paste Λ.X hsq.toCommSq sv' q₁)
    (lowerStarBaseChange_app_paste Λ.X sv hsq₁.toCommSq q₂)
    (baseChange_congr Λ.X q₁ q₂ sb.w st.w) M


/-- The canonical adjunction exchange for a finite étale morphism is invertible for every
base change and every internal module over the pulled-back condensed coefficient ring.

Source: Stacks Project, Tags 0959 and 095B, with the split charts of Tag 04HN;
the pro-étale module extension in the latest blueprint, `lem-a1-finite-map-purity`,
first proof paragraph (blueprint: lem-a1-finite-etale-condensed-base-change).

Proof in words.
1. Choose an étale splitting neighborhood over `g z` for every point `z : Y'`, using
Tag 04HN. Replace the clopen pieces by copies of their base using their isomorphisms,
then reindex by `Fin n`. Their canonical lifts form a colimiting cofan.
2. Base change these charts to `Y'`. Lift their sheets through `hsq`. Universality of
finite coproducts of schemes shows that the lifted sheets still form a colimiting cofan.
The pulled-back chart maps are étale and jointly surjective, hence a pro-étale cover.
3. The chart theorem gives both finite-product isomorphisms and the counit projection
equations for the localized exchange.
4. In these coordinates, the localized exchange is the pullback of the first product
isomorphism followed by the finite-product comparison and the sheet isomorphisms.
Module pullback preserves finite products, including the empty product, so the
localized exchange is invertible after cancelling the second product isomorphism.
5. The coefficient comparison is invertible, so forgetting the module action identifies
chart pullback with abelian-sheaf inverse image, and then with localization restriction.
Cover-local sheaf detection makes the underlying exchange invertible globally.
6. The module forgetful functor reflects isomorphisms. Apply this to every module and
use the component criterion for an isomorphism of natural transformations. -/
theorem finiteEtaleCondensedBaseChange_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsFinite f] [Etale f]
    (hsq : IsPullback g' f' f g) :
    IsIso (lowerStarBaseChange Λ.X hsq.toCommSq) := by
  classical
  choose U v hv hy n t w hc using fun z : Y' ↦ splitChart_exists f (g z)
  let U' (z : Y') := pullback (v z) g
  let v' (z : Y') : U' z ⟶ Y' := pullback.snd (v z) g
  let h (z : Y') : U' z ⟶ U z := pullback.fst (v z) g
  let (z : Y') : Etale (v z) := hv z
  let (z : Y') : Etale (v' z) := inferInstanceAs (Etale (pullback.snd (v z) g))
  have hs (z : Y') : IsPullback (h z) (v' z) (v z) g :=
    IsPullback.of_hasPullback _ _
  have hcover : Presieve.ofArrows U' v' ∈ Scheme.proetalePrecoverage Y' := by
    apply Scheme.etalePrecoverage_le_proetalePrecoverage
    change Presieve.ofArrows U' v' ∈ Scheme.precoverage @Etale Y'
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun z ↦ inferInstance⟩
    intro z
    obtain ⟨u, hu⟩ := hy z
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback u z hu
    exact ⟨z, p, hp⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply module_isIso_of_cover Λ v' hcover
  intro z
  exact baseChange_isIso_on_chart Λ hsq (v z) (v' z) (h z) (hs z)
    (n z) (t z) (w z) (hc z) M


end AlgebraicGeometry.ProEtale.CondensedRing
