/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.CategoryTheory.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Unbounded comparison under a finite étale cohomological-dimension bound

Source: Stacks Project, proetale.tex, lemma-morphism-comparison, and derived.tex,
Tag 07K7; the lower-truncation argument of UnboundedDirectImageTruncationStability.
(blueprint: lem-pur-finite-cd-unbounded-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem finiteCD_target_upper_bound
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (d : ℕ) (hcd : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℕ), d < q →
        IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj M))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : ℤ) [K.IsLE b] :
    ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).IsLE
        (b + d + 1) := by
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let H := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let F := lowerStar (ModuleCat.{u + 1} A) g
  let E := Etale.lowerStar (ModuleCat.{u + 1} A) g
  let β := mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom
  have := CountableAB4Star.ofShape (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℕ
  have := CountableAB4Star.ofShape (C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) ℕ
  let adj := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    |>.mapDerivedCategoryRightDerivedAdjunction
  have := adj.rightAdjoint_preservesLimits
  change (F.rightDerivedFunctor.obj (G.mapDerivedCategory.obj K)).IsLE (b + d + 1)
  apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    F.rightDerivedFunctor (G.mapDerivedCategory.obj K) (b + d)
  intro n
  let L := (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K
  have : L.IsGE (-(n : ℤ)) := inferInstance
  have : L.IsLE b := inferInstance
  have : (E.rightDerivedFunctor.obj L).IsLE (b + d) :=
    E.isLE_rightDerivedFunctor_obj_of_dimension d hcd L b inferInstance
  have : (H.mapDerivedCategory.obj (E.rightDerivedFunctor.obj L)).IsLE (b + d) :=
    H.isLE_mapDerivedCategory_obj _ _
  have hL : IsIso (β.app L) :=
    isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app (ModuleCat.{u + 1} A) g L
      ⟨-(n : ℤ), inferInstance⟩
  let e := (H.leftDerivedFunctorIsoMapDerivedCategory.app
      (E.rightDerivedFunctor.obj L)).symm ≪≫ asIso (β.app L) ≪≫
    F.rightDerivedFunctor.mapIso (G.leftDerivedFunctorIsoMapDerivedCategory.app L) ≪≫
    F.rightDerivedFunctor.mapIso ((G.mapDerivedCategoryTruncGEIso (-(n : ℤ))).app K)
  exact DerivedCategory.TStructure.t.isLE_of_iso e (b + d)


private theorem finiteCD_truncation_stable
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : DerivedCategory C ⥤ DerivedCategory D) [S.CommShift ℤ] [S.IsTriangulated]
    (e : ℤ) (hS : ∀ (L : DerivedCategory C) (b : ℤ), L.IsLE b → (S.obj L).IsLE (b + e))
    (K : DerivedCategory C) (m N : ℤ) (hN : N + e ≤ m) :
    IsIso ((DerivedCategory.homologyFunctor D m).map
      (S.map ((DerivedCategory.TStructure.t.truncGEπ N).app K))) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE N).obj K
  let T' := S.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := S.map_distinguished T
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished N K)
  have : T'.obj₁.IsLE (N - 1 + e) := hS T.obj₁ (N - 1) inferInstance
  have hz₀ : IsZero ((DerivedCategory.homologyFunctor _ m).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + e) m (by omega)
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor _ (m + 1)).obj T'.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (N - 1 + e) (m + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T' hT' m).2
      (hz₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T' hT' m (m + 1)).2
      (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ m).map T'.mor₂)

/-- A uniform bound on étale higher direct images extends the specified comparison mate
from bounded-below to arbitrary complexes.
Source: Stacks Project, proetale.tex, lemma-morphism-comparison, and derived.tex,
Tag 07K7 (blueprint: lem-pur-finite-cd-unbounded-comparison).

Proof: a bound d on higher images makes the total étale direct image raise upper bounds
by at most d. Exact comparison preserves this bound. On every lower truncation the
bounded-below comparison mate identifies the pro-étale image with this étale image.
Exact countable products in pro-étale module sheaves imply left completeness, and the
right derived direct image preserves products, so its value on a comparison pullback
raises upper bounds by at most d+1. For each m choose N=m-d-2. Applying the two functors
to the lower truncation triangle kills the tail in degrees m and m+1. Thus both maps
to the lower truncation are invertible on H^m. Naturality of the actual mate and its
bounded-below invertibility imply invertibility on H^m of K, for every m. Homology
detects isomorphisms. This includes zero rings, empty schemes and two-sided unbounded K.
-/
theorem isIso_comparisonMate_of_finiteCohomologicalDimension
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (hcd : ∃ d : ℕ,
      ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ), d < q →
        IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj M))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom).app K) := by
  obtain ⟨d, hd⟩ := hcd
  let G := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let H := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let F := lowerStar (ModuleCat.{u + 1} A) g
  let E := Etale.lowerStar (ModuleCat.{u + 1} A) g
  let β₀ : E.rightDerivedFunctor ⋙ H.leftDerivedFunctor ⟶
      G.leftDerivedFunctor ⋙ F.rightDerivedFunctor :=
    mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom
  let β : E.rightDerivedFunctor ⋙ H.mapDerivedCategory ⟶
      G.mapDerivedCategory ⋙ F.rightDerivedFunctor :=
    Functor.whiskerLeft E.rightDerivedFunctor H.leftDerivedFunctorIsoMapDerivedCategory.inv ≫
      β₀ ≫ Functor.whiskerRight G.leftDerivedFunctorIsoMapDerivedCategory.hom F.rightDerivedFunctor
  have hsource (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) (b : ℤ)
      (hb : L.IsLE b) : (H.mapDerivedCategory.obj (E.rightDerivedFunctor.obj L)).IsLE
        (b + d) := by
    have : (E.rightDerivedFunctor.obj L).IsLE (b + d) :=
      E.isLE_rightDerivedFunctor_obj_of_dimension d hd L b hb
    exact H.isLE_mapDerivedCategory_obj _ _
  have hβK : IsIso (β.app K) := by
    apply (DerivedCategory.isIso_iff _ _).2
    intro m
    let N : ℤ := m - d - 2
    have hS := finiteCD_truncation_stable (E.rightDerivedFunctor ⋙ H.mapDerivedCategory)
      (d : ℤ) hsource K m N (by dsimp [N]; omega)
    have hT := finiteCD_truncation_stable (G.mapDerivedCategory ⋙ F.rightDerivedFunctor)
      ((d : ℤ) + 1) (fun L b hb ↦ by
        let := hb
        dsimp only [Functor.comp_obj, F, G]
        simpa only [add_assoc] using finiteCD_target_upper_bound A g d hd L b)
      K m N (by dsimp [N]; omega)
    let L := (DerivedCategory.TStructure.t.truncGE N).obj K
    have : L.IsGE N := inferInstance
    have : IsIso (β₀.app L) :=
      isIso_mateEquiv_leftDerivedComparisonUpperStarCompUpperStarIso_app (ModuleCat.{u + 1} A) g L
        ⟨N, inferInstance⟩
    have : IsIso (β.app L) := by
      dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance
    let t := (DerivedCategory.TStructure.t.truncGEπ N).app K
    let HM := DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) m
    have hn := congrArg HM.map (β.naturality t)
    simp only [Functor.map_comp] at hn
    change HM.map ((E.rightDerivedFunctor ⋙ H.mapDerivedCategory).map t) ≫
      HM.map (β.app L) = HM.map (β.app K) ≫
        HM.map ((G.mapDerivedCategory ⋙ F.rightDerivedFunctor).map t) at hn
    have : IsIso (HM.map ((G.mapDerivedCategory ⋙ F.rightDerivedFunctor).map t)) := hT
    have : IsIso (HM.map ((E.rightDerivedFunctor ⋙ H.mapDerivedCategory).map t)) := hS
    have : IsIso (HM.map (β.app K) ≫
        HM.map ((G.mapDerivedCategory ⋙ F.rightDerivedFunctor).map t)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (HM.map ((G.mapDerivedCategory ⋙ F.rightDerivedFunctor).map t))
  dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hβK
  have := hβK
  have : IsIso (β₀.app K ≫ F.rightDerivedFunctor.map
      (G.leftDerivedFunctorIsoMapDerivedCategory.hom.app K)) :=
    IsIso.of_isIso_comp_left
      (H.leftDerivedFunctorIsoMapDerivedCategory.inv.app (E.rightDerivedFunctor.obj K)) _
  exact IsIso.of_isIso_comp_right _
    (F.rightDerivedFunctor.map (G.leftDerivedFunctorIsoMapDerivedCategory.hom.app K))

end AlgebraicGeometry.ProEtale
