/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.LineCounitComparison

/-! # Comparison of the independently normalized ordered integration

Source: blueprint sk-prop-an, lem-amb-affine-space-top-trace, proof paragraphs 2--3;
Stacks 099R, 09AF, and 0B65.
(blueprint: lem-pur-ordered-integration-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
attribute [local implicit_reducible] affineTraceTower
attribute [local implicit_reducible] affineTraceLineCompactification Etale.affineTraceOpenLeft

end AlgebraicGeometry.ProEtale.VectorIntegrationSite

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

private theorem towerSiteComparison_zero
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower T 0).smallEtaleTopology
      (ModuleCat.{u + 1} A))) : towerSiteComparison A T 0 J = Iso.refl _ := by
  delta towerSiteComparison
  rfl

private theorem towerSiteComparison_succ
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) (d : ℕ)
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower T (d + 1)).smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    towerSiteComparison A T (d + 1) J =
      let L := Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification (affineTraceTower T d))
      let e := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) (affineTraceLineCompactification (affineTraceTower T d))).app J
      (towerLeft A T d).mapIso (lineSiteComparison A _ J) ≪≫
        (towerLeft A T d).mapIso ((comparison A _).mapIso e.symm) ≪≫
        towerSiteComparison A T d (L.obj J) ≪≫
        (comparison A T).mapIso ((Etale.affineTraceLeft A T d).mapIso e) := by
  delta towerSiteComparison
  rfl

private theorem towerSiteComparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) (d : ℕ)
    (J J' : DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) (f : J ⟶ J') :
    (towerLeft A T d).map ((comparison A _).map f.hom) ≫
        (towerSiteComparison A T d J').hom =
      (towerSiteComparison A T d J).hom ≫
        (comparison A T).map ((Etale.affineTraceLeft A T d).map f.hom) := by
  induction d with
  | zero =>
    simp only [towerSiteComparison_zero, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  | succ d ih =>
    let L := Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower T d))
    let e := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) (affineTraceLineCompactification (affineTraceTower T d))
    have hn := (compactSupportSiteComparison A
      (affineTraceLineCompactification (affineTraceTower T d))).hom.naturality f
    have hn' : (lineLeft A _).map ((comparison A _).map f.hom) ≫
        (lineSiteComparison A _ J').hom =
      (lineSiteComparison A _ J).hom ≫
        (comparison A _).map ((Etale.affineTraceLineLeft A _).map f.hom) := by
      unfold lineSiteComparison
      with_unfolding_all exact hn
    have he := e.inv.naturality f
    have hi := ih (L.obj J) (L.obj J') (L.map f)
    change (Etale.affineTraceLineLeft A _).map f.hom ≫ e.inv.app J' =
      e.inv.app J ≫ (L.map f).hom at he
    have he' := e.hom.naturality f
    change (L.map f).hom ≫ e.hom.app J' =
      e.hom.app J ≫ (Etale.affineTraceLineLeft A _).map f.hom at he'
    change (lineLeft A _ ⋙ towerLeft A T d).map _ ≫ _ = _
    simp only [towerSiteComparison_succ, Iso.trans_hom, Functor.mapIso_hom,
      Functor.comp_map, Category.assoc]
    change (towerLeft A T d).map ((lineLeft A _).map _) ≫
        (towerLeft A T d).map _ ≫ (towerLeft A T d).map _ ≫ _ ≫ _ = _
    rw [← Functor.map_comp_assoc]
    change (towerLeft A T d).map
        ((lineLeft A _).map _ ≫ (lineSiteComparison A _ J').hom) ≫ _ = _
    with_unfolding_all erw [hn']
    simp only [Functor.map_comp, Category.assoc]
    have hemap := congrArg (fun g ↦ (towerLeft A T d).map
      ((comparison A (affineTraceTower T d)).map g)) he
    simp only [Functor.map_comp] at hemap
    with_unfolding_all erw [reassoc_of% hemap, reassoc_of% hi]
    have hemap' := congrArg (fun g ↦ (comparison A T).map
      ((Etale.affineTraceLeft A T d).map g)) he'
    simp only [Functor.map_comp] at hemap'
    with_unfolding_all erw [hemap']
    rfl

private theorem compared_tower_recursion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    TowerCounitRecursion l E n T hT r hA K
      (fun d ↦ (towerSiteComparison (Scheme.finiteTateCoefficient l E n) T d
        ⟨_, rightTower_plus l E n T hT r hA d K⟩).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) T).map
          ((Etale.affineTraceAdjunction _ (l ^ (r + 1)) hA
            (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
            (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
            T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d).counit.app K.obj)) := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  let t := Etale.projectiveLineTraceTransport N hN A hA
  let D := Etale.projectiveLineTraceDatum N hN A hA
  have hTN : IsUnit (N : Γ(T, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hT.pow (r + 1)
  constructor
  · apply heq_of_eq
    simp [towerSiteComparison_zero, Etale.affineTraceAdjunction,
      Etale.affineTraceAdjunctionTower]
    rfl
  · intro d
    let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
    let J : DerivedCategory.Plus (Sheaf (affineTraceTower T (d + 1)).smallEtaleTopology
      (ModuleCat.{u + 1} A)) := ⟨_, rightTower_plus l E n T hT r hA (d + 1) K⟩
    let J' : DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
      (ModuleCat.{u + 1} A)) := ⟨_, rightTower_plus l E n T hT r hA d K⟩
    let L := Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification (affineTraceTower T d))
    let e := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) (affineTraceLineCompactification (affineTraceTower T d))
    let c := (Etale.affineTraceLineAdjunction A N hA t (affineTraceTower T d)
      (affineTraceInvertible N T hTN d)
      (D _ (affineTraceInvertible N T hTN d))).counit.app J'.obj
    let f : L.obj J ⟶ J' := ⟨e.hom.app J ≫ c⟩
    have hn := towerSiteComparison_naturality A T d (L.obj J) J' f
    have hl := lineCounit_comparison l E n (affineTraceTower T d)
      (affineTraceInvertible l T hT d) r hA J'
    apply heq_of_eq
    change (towerSiteComparison A T (d + 1) J).hom ≫
        (comparison A T).map
          ((Etale.affineTraceAdjunction A N hA t D T hTN (d + 1)).counit.app K.obj) = _
    have hs := Etale.affineTraceAdjunctionTower_counit_succ
      (C := fun d ↦ Etale.DerivedCategoryModule A (affineTraceTower T d))
      (fun d ↦ letI := affineTraceNoetherian T d
        Etale.affineTraceLineAdjunction A N hA t (affineTraceTower T d)
          (affineTraceInvertible N T hTN d)
          (D _ (affineTraceInvertible N T hTN d))) d K.obj
    have hs' : (Etale.affineTraceAdjunction A N hA t D T hTN (d + 1)).counit.app K.obj =
        (Etale.affineTraceLeft A T d).map c ≫
          (Etale.affineTraceAdjunction A N hA t D T hTN d).counit.app K.obj := by
      unfold Etale.affineTraceAdjunction
      exact hs
    rw [hs']
    change (towerSiteComparison A T (d + 1) J).hom ≫
        (comparison A T).map
          ((Etale.affineTraceLeft A T d).map c ≫
            (Etale.affineTraceAdjunction A N hA t D T hTN d).counit.app K.obj) = _
    rw [towerSiteComparison_succ]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    dsimp only [f, ObjectProperty.homMk_hom] at hn
    simp only [Functor.map_comp, Category.assoc] at hn
    with_unfolding_all erw [← reassoc_of% hn]
    have he : (towerLeft A T d).map ((comparison A _).map (e.inv.app J)) ≫
        (towerLeft A T d).map ((comparison A _).map (e.hom.app J)) = 𝟙 _ := by
      simp only [← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    with_unfolding_all
      erw [reassoc_of% he, ← Functor.map_comp_assoc, ← hl]

/-- The ordered composite of the supported-Kummer pro-etale counits is the comparison
image of the ordinary affine trace. This statement involves no vector bundle or gluing.
Source: blueprint sk-prop-an, affine-space top trace, proof paragraphs 2--3;
Stacks 099R, 09AF, and 0B65
(blueprint: lem-pur-ordered-integration-comparison).

Proof: compare the ordinary projective-line Chern class with the supported Cartier
Kummer class using CartierKummerChern and the root-normalized finite Tate comparison.
The canonical direct-image mate carries both the twisted unit and the Chern adjunct
to their pro-etale counterparts. Biprod injections therefore identify the projective
line decompositions, and their inverse followed by the second projection identifies
the traces. The tensor projection comparison, including its symmetries and right
unitor, then identifies projective counits on every bounded-below coefficient.
Exact extension by zero and inverse image preserve the open adjunction's counit:
transpose both sides and use the identity and the pullback comparison. This gives
the line-counit comparison. Induct on the ordered coordinates; naturality of the
compact-support comparison and its defining successor compositor show that the
compared ordinary counits satisfy TowerCounitRecursion. Its uniqueness identifies
them with towerCounit. Cancel towerSiteComparison to obtain the displayed equality.
At zero coordinates both composites are identities; the argument also includes the
empty base, since all functors, adjunctions, and normalization equations remain valid.
-/
theorem orderedIntegration_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    orderedIntegration l E n T hT r hA d =
      (comparison (Scheme.finiteTateCoefficient l E n) T).map
        (Etale.affineTraceCounit _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d) := by
  let K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
    ⟨Etale.ordinaryFiniteUnit _ T, ⟨0, inferInstance⟩⟩
  have he := (existsUniqueTowerCounit l E n T hT r hA K).unique
    (compared_tower_recursion l E n T hT r hA K)
    (existsUniqueTowerCounit l E n T hT r hA K).exists.choose_spec
  unfold orderedIntegration towerCounit
  rw [← he]
  dsimp only [K]
  simp only [Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
