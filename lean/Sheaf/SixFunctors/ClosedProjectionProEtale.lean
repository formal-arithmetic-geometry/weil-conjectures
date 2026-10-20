/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C7
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.ProEtaleOperations

import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Unbounded closed projection with arbitrary ringed coefficients

Source: current blueprint main-20261015, six-functors basics, middle projection
identity of closed-costalk duality (blueprint: lem-sf-proetale-closed-projection-unbounded).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u a b c va vb vc
open CategoryTheory CategoryTheory.Limits Opposite
/- The formal projection argument: closed restriction inverts the counit, while
open restriction sees zero objects. Joint conservativity detects invertibility. -/
private theorem projectionOfRestrictions
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (L : A ⥤ B) (V : B ⥤ A) (J : A ⥤ C) (adj : L ⊣ V)
    (α : TA ⋙ L ≅ (L.prod L) ⋙ TB)
    (β : TA ⋙ J ≅ (J.prod J) ⋙ TC)
    (hc : ∀ N : B, IsIso (adj.counit.app N))
    (hz : ∀ N : B, IsZero (J.obj (V.obj N)))
    (htzero : ∀ X Y : C, IsZero X → IsZero (TC.obj (X, Y)))
    (hdet : ∀ {X Y : A} (f : X ⟶ Y), IsIso (L.map f) → IsIso (J.map f) → IsIso f) :
    Nonempty (((𝟭 B).prod L) ⋙ TB ⋙ V ≅ (V.prod (𝟭 A)) ⋙ TA) := by
  let F := (V.prod (𝟭 A)) ⋙ TA
  let G := ((𝟭 B).prod L) ⋙ TB ⋙ V
  let p : F ⟶ G :=
    { app X := adj.homEquiv _ _
        (α.hom.app (V.obj X.1, X.2) ≫ TB.map (Prod.mkHom (adj.counit.app X.1)
          (𝟙 (L.obj X.2))))
      naturality X Y f := by
        dsimp only [F, G, Functor.comp_map, Functor.prod_map, Functor.id_map]
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        congr 1
        have ha := α.hom.naturality (Prod.mkHom (V.map f.1) f.2)
        dsimp only [Functor.comp_map, Functor.prod_map] at ha
        rw [← Category.assoc, ha, Category.assoc, ← TB.map_comp]
        rw [Category.assoc, ← TB.map_comp]
        congr 2
        ext
        · exact adj.counit.naturality f.1
        · simp }
  have hi (X : B × A) : IsIso (p.app X) := by
    let := hc X.1
    let := hc (TB.obj (X.1, L.obj X.2))
    have he : L.map (p.app X) ≫ adj.counit.app (TB.obj (X.1, L.obj X.2)) =
        α.hom.app (V.obj X.1, X.2) ≫
          TB.map (Prod.mkHom (adj.counit.app X.1) (𝟙 (L.obj X.2))) := by
      exact (adj.homEquiv_counit _ _ _).symm.trans
        ((adj.homEquiv _ _).symm_apply_apply _)
    have hcomp : IsIso (L.map (p.app X) ≫ adj.counit.app (TB.obj (X.1, L.obj X.2))) := by
      have hpair : IsIso (Prod.mkHom (adj.counit.app X.1) (𝟙 (L.obj X.2))) :=
        (isIso_prod_iff B B).2 ⟨hc X.1, inferInstance⟩
      rw [he]
      infer_instance
    have hl : IsIso (L.map (p.app X)) :=
      by
        let := hcomp
        exact IsIso.of_isIso_comp_right (L.map (p.app X))
          (adj.counit.app (TB.obj (X.1, L.obj X.2)))
    have hsrc : IsZero (J.obj (F.obj X)) :=
      (htzero _ _ (hz X.1)).of_iso (β.app (V.obj X.1, X.2))
    have htgt : IsZero (J.obj (G.obj X)) := hz _
    have hj : IsIso (J.map (p.app X)) := hsrc.isIso htgt _
    exact hdet _ hl hj
  have : IsIso p := NatIso.isIso_of_isIso_app p
  exact ⟨(asIso p).symm⟩

namespace AlgebraicGeometry.Scheme

/- Restrict the normalized comparison from all K-flat complexes to the flat-term subclass. -/
private noncomputable def costalkTensorModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (t : RingedSiteDualityModel.{u + 1, u, 0, u + 2} (ProEt.topology X) R) :
    ProEtaleTensorModel X R := by
  let P : ObjectProperty (CochainComplex (proEtaleRingModules X R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R)
  let q : (proEtaleFlatRepresentatives X R).FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun P h ↦ h.1)
  refine ⟨t.closed.tensor, ?_⟩
  exact Functor.isoWhiskerLeft (q.prod q) t.models.comparison

/- Identity coefficient transport is the actual sectionwise closed pushforward. -/
private noncomputable def costalkPushIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModuleDirectImage f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
        proEtaleRingedDirectImage f R := by
  unfold proEtaleRingModuleDirectImage proEtaleRingedDirectImage proEtaleRingDirectImageMap
  simp only [Iso.refl_hom]
  exact Iso.refl _

/- The open-closed theorem gives exactness without its optional qcqs colimit hypothesis. -/
private theorem costalkClosedExact {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleRingModuleDirectImage i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)) := by
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, hq, ai, aj, hc, hu, hz, hzi, hl, hcl, hil, hic, hs, hf⟩ :=
    proEtale_ringed_open_closed i V hij R
  let := hic
  exact preservesFiniteColimits_of_natIso (costalkPushIso i R).symm

/- Full faithfulness survives right derivation because the exact left adjoint preserves
K-injectivity on its right. This concerns the specified canonical derived adjunction. -/
private theorem costalkDerivedCounit {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    IsIso (proEtaleRingDerivedAdjunction i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).counit := by
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, hq, ai, aj, hc, hu, hz, hzi, hl, hcl, hil, hic, hs, hf⟩ :=
    proEtale_ringed_open_closed i V hij R
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  let ff := ai.fullyFaithfulROfIsIsoCounit
  have : (proEtaleRingedDirectImage i R).Full := ff.full
  have : (proEtaleRingedDirectImage i R).Faithful := ff.faithful
  have : (proEtaleRingModuleDirectImage i R _ (Iso.refl _)).Full :=
    Functor.Full.of_iso (costalkPushIso i R).symm
  have : (proEtaleRingModuleDirectImage i R _ (Iso.refl _)).Faithful :=
    Functor.Faithful.of_iso (costalkPushIso i R).symm
  have : (proEtaleRingModuleDirectImage i R _ (Iso.refl _)).PreservesKInjectiveComplexes :=
    (proEtaleRingModuleAdjunction i R _ (Iso.refl _)).preservesKInjectiveComplexes
  unfold proEtaleRingDerivedAdjunction
  infer_instance

/- Exactness computes closed direct image on cohomology; the essential-image theorem
then makes its open restriction zero in every degree. -/
private theorem costalkDerivedOpenZero {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (N : DerivedCategory (proEtaleRingModules Z
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R))) :
    IsZero ((proEtaleRingDerivedPullback j R
      ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj
        ((proEtaleRingDerivedDirectImage i R
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj N)) := by
  let Ri := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let Rj := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
  let F := proEtaleRingModuleDirectImage i R Ri (Iso.refl _)
  let G := proEtaleRingModulePullback j R Rj (Iso.refl _)
  have : F.IsRightAdjoint := (proEtaleRingModuleAdjunction i R Ri (Iso.refl _)).isRightAdjoint
  have : PreservesFiniteColimits F := costalkClosedExact i j hij R
  have h0 (M : proEtaleRingModules Z Ri) : IsZero (G.obj (F.obj M)) := by
    exact (proEtaleRingModule_closed_essImage_iff_and_unit_isIso i j hij R Ri Rj
      (Iso.refl _) (Iso.refl _) (F.obj M)).1.1 ⟨M, ⟨Iso.refl _⟩⟩
  apply (DerivedCategory.isZero_iff _).2
  intro n
  let e := G.mapIso ((F.rightDerivedFunctorHomologyFunctorIso n).app N) ≪≫
    (G.mapDerivedCategoryHomologyFunctorIso n).app (F.rightDerivedFunctor.obj N)
  exact (h0 ((DerivedCategory.homologyFunctor _ n).obj N)).of_iso e.symm

/- Apply underived open-closed detection separately to every cohomology module. -/
private theorem costalkDerivedZeroDetection {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (proEtaleRingModules X R))
    (hi : IsZero ((proEtaleRingDerivedPullback i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj K))
    (hj : IsZero ((proEtaleRingDerivedPullback j R
      ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj K)) :
    IsZero K := by
  let Ri := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let Rj := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
  let F := proEtaleRingModulePullback i R Ri (Iso.refl _)
  let G := proEtaleRingModulePullback j R Rj (Iso.refl _)
  apply (DerivedCategory.isZero_iff _).2
  intro n
  apply proEtaleRingModule_isZero_of_open_closed i j hij R Ri Rj
    (Iso.refl _) (Iso.refl _) ((DerivedCategory.homologyFunctor _ n).obj K)
  · exact ((DerivedCategory.homologyFunctor _ n).map_isZero hj).of_iso
      ((G.mapDerivedCategoryHomologyFunctorIso n).app K)
  · exact ((DerivedCategory.homologyFunctor _ n).map_isZero hi).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K)

/- Exact restriction preserves a distinguished cone triangle, so zero detection detects
isomorphisms without boundedness assumptions. -/
private theorem costalkDerivedIsoDetection {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {K M : DerivedCategory (proEtaleRingModules X R)} (f : K ⟶ M)
    (hi : IsIso ((proEtaleRingDerivedPullback i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).map f))
    (hj : IsIso ((proEtaleRingDerivedPullback j R
      ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R) (Iso.refl _)).map f)) :
    IsIso f := by
  let F := proEtaleRingDerivedPullback i R
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let G := proEtaleRingDerivedPullback j R
    ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R) (Iso.refl _)
  obtain ⟨P, g, h, ht⟩ := Pretriangulated.distinguished_cocone_triangle f
  have hF := (Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (F.mapTriangle.obj (Pretriangulated.Triangle.mk f g h)) (F.map_distinguished _ ht)).2 hi
  have hG := (Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (G.mapTriangle.obj (Pretriangulated.Triangle.mk f g h)) (G.map_distinguished _ ht)).2 hj
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ ht).1
    (costalkDerivedZeroDetection i j hij R P hF hG)

/-- Closed projection for the normalized derived tensor on the small pro-etale site.
The rings and the module direct image below are the actual inverse-image ring and
sectionwise direct image. The derived functors are the recorded actual operations,
using the identity coefficient comparison. No exceptional inverse image or dualizing object occurs.

Source: current blueprint main-20261015, six-functors basics,
`sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.proof.md`, middle
projection identity; Stacks, Tags 09AA, 09BM, 09AH, 07A4 and 08J9.
(blueprint: lem-sf-proetale-closed-projection-unbounded).

Proof: the closed pushforward is exact, its inverse-image counit is invertible,
and its open restriction is zero. Use the ringed open-closed theorem for the
quasi-compact open complement. Its localization sequence gives joint zero
detection. The closed and open inverse images
are jointly conservative on sheaves and on cohomology of arbitrary complexes.
Their exact termwise functors and adjunction descend through quasi-isomorphism
localization, with the
canonical factorization comparisons. Inverse image commutes with the derived tensor:
resolve by flat K-flat complexes and use the sheafified scalar tensor comparison.
The models' representative comparisons identify these tensors with the specified
normalized tensors. Form the natural projection map from i_*N tensor K to
i_*(N tensor i^*K) as the adjoint of the inverse-image tensor comparison followed
by the closed counit tensor identity. Closed restriction makes it invertible by
the counit and its triangle identity. Open restriction makes it a map between
zero objects. Both restrictions preserve cones; joint detection on cohomology
makes its cone zero, so the projection map is invertible. Take its inverse to
obtain the orientation displayed below. All constructions are natural in N,K.
The argument applies to the empty closed or open subscheme and to zero complexes,
and uses no boundedness or Tor bound. -/
theorem closedImmersionProEtaleProjection
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (t : RingedSiteDualityModel.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
    (z : RingedSiteDualityModel.{u + 1, u, 0, u + 2} (ProEt.topology Z)
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) :
    let RZ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
    let L := proEtaleRingDerivedPullback i R RZ (Iso.refl _)
    let V := proEtaleRingDerivedDirectImage i R RZ (Iso.refl _)
    Nonempty (((𝟭 (DerivedCategory (proEtaleRingModules Z RZ))).prod L) ⋙
      z.closed.tensor ⋙ V ≅
      (V.prod (𝟭 (DerivedCategory (proEtaleRingModules T R)))) ⋙ t.closed.tensor) := by
  dsimp only
  let Rj := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
  obtain ⟨o⟩ := ringedSiteDualityMaps_exists.{u + 1, u, 0, u + 2} (ProEt.topology U) Rj
  let L := proEtaleRingDerivedPullback i R _ (Iso.refl _)
  let V := proEtaleRingDerivedDirectImage i R _ (Iso.refl _)
  let J := proEtaleRingDerivedPullback j R Rj (Iso.refl _)
  let α := proEtaleCanonicalTensorComparison i R _ (Iso.refl _)
    (costalkTensorModel T R t) (costalkTensorModel Z _ z)
  let β := proEtaleCanonicalTensorComparison j R _ (Iso.refl _)
    (costalkTensorModel T R t) (costalkTensorModel U Rj o)
  apply projectionOfRestrictions t.closed.tensor z.closed.tensor o.closed.tensor L V J
    (proEtaleRingDerivedAdjunction i R _ (Iso.refl _)) α β
  · intro N
    have := costalkDerivedCounit i j hij R
    infer_instance
  · exact costalkDerivedOpenZero i j hij R
  · intro X Y hX
    have : (@MonoidalCategory.tensorRight _ _ o.closed.monoidal Y).IsLeftAdjoint :=
      (o.closed.adjunction Y).isLeftAdjoint
    exact (@MonoidalCategory.tensorRight _ _ o.closed.monoidal Y).map_isZero hX
  · exact fun f hi hj ↦ costalkDerivedIsoDetection i j hij R f hi hj


end AlgebraicGeometry.Scheme
