/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.CompletedPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # The projection-defined constant-tower derived-limit unit

Source: the completed-pullback invocation in the proof of
lem-cbc-completed-extension-zero-comparison; Stacks Tag 079P,
injectives.tex, theorem-K-injective-embedding-grothendieck
(blueprint: lem-cbc-constant-derived-limit-resolution-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The canonical constant-tower map is computed by factoring the components of any
fixed functorial K-injective resolution through the ordinary limit of complexes.
Source: completed-pullback invocation in lem-cbc-completed-extension-zero-comparison;
Stacks Tag 079P, theorem-K-injective-embedding-grothendieck
(blueprint: lem-cbc-constant-derived-limit-resolution-unit).

Proof: (1) Apply the ordinary limit functor degreewise to the fixed resolution J.
The sectionwise module-sheaf limit theorem gives compatible families, with differential
and J's maps acting coordinatewise, hence a functor without an exactness assumption.
(2) The components of iota on a constant tower are compatible. The universal property
of the ordinary limit gives z, with the prescribed projections, uniquely in every degree.
(3) Naturality of iota gives naturality of z after every projection, and joint monicity
of those projections gives naturality as chain maps. Additivity of J is not required.
(4) Levelwise exactness makes the constant-tower functor exact. Its recorded derived
factorization and the universal Rlim comparison give the fixed localization comparison;
it is invertible on J's K-injective values and on the localized resolution maps.
(5) Localize z and compose with this comparison. Localization.liftNatTrans descends
it uniquely to the derived category, including inverses of quasi-isomorphisms.
(6) Naturality then holds for all derived morphisms. The ordinary constant/limit
adjunction followed by the same universal right-derived comparison has precisely these
components, identifying the descent with the unit used in completed pullback. -/
theorem constantDerivedLimitResolutionUnit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (J : CochainComplex (d.towers T) ℤ ⥤ CochainComplex (d.towers T) ℤ)
    (ι : 𝟭 (CochainComplex (d.towers T) ℤ) ⟶ J)
    (hι : ∀ M : CochainComplex (d.towers T) ℤ, QuasiIso (ι.app M))
    (hJ : ∀ M : CochainComplex (d.towers T) ℤ, (J.obj M).IsKInjective) :
    ∃ z : 𝟭 (CochainComplex (reductionModules T (d.completedRing T)) ℤ) ⟶
        (d.constantTower T).mapHomologicalComplex (.up ℤ) ⋙ J ⋙
          (completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ),
      (∀ (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
          (i : ℤ) (n : ℕ),
        (z.app C).f i ≫ limit.π
            ((J.obj (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C)).X i)
            (op n) =
          ((ι.app (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C)).f i).app
            (op n)) ∧
      (∀ (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
          (w : C ⟶ ((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex
            (.up ℤ)).obj (J.obj (((d.constantTower T).mapHomologicalComplex
              (.up ℤ)).obj C))),
        (∀ (i : ℤ) (n : ℕ), w.f i ≫ limit.π
            ((J.obj (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C)).X i)
            (op n) =
          ((ι.app (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C)).f i).app
            (op n)) → w = z.app C) ∧
      ∃ η : 𝟭 (d.derived T) ⟶ d.derivedConstantTower T ⋙
          completedRlim T (d.completedRing T),
        η = (d.constantRlimAdjunction T).unit ∧
        (∀ C : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
          η.app (DerivedCategory.Q.obj C) ≫
              (completedRlim T (d.completedRing T)).map
                ((d.constantTower T).mapDerivedCategoryFactors.hom.app C ≫
                  DerivedCategory.Q.map
                    (ι.app (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C))) =
            DerivedCategory.Q.map (z.app C) ≫
              (completedRlimUnit T (d.completedRing T)).app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj
                  (J.obj (((d.constantTower T).mapHomologicalComplex (.up ℤ)).obj C)))) ∧
        (∀ (C D : d.derived T) (h : C ⟶ D),
          η.app C ≫ (completedRlim T (d.completedRing T)).map
              ((d.derivedConstantTower T).map h) = h ≫ η.app D) := by
  have := hι
  have := hJ
  let L := (d.constantTower T).mapHomologicalComplex (.up ℤ)
  let R := (completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)
  let a : d.constantTower T ⊣ completedTowerLimit T (d.completedRing T) := constLimAdj
  let u := (a.mapHomologicalComplex (.up ℤ)).unit
  let z : 𝟭 (CochainComplex (reductionModules T (d.completedRing T)) ℤ) ⟶
      L ⋙ J ⋙ R := u ≫ Functor.whiskerRight (Functor.whiskerLeft L ι) R
  have hz (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
      (i : ℤ) (n : ℕ) :
      (z.app C).f i ≫ limit.π ((J.obj (L.obj C)).X i) (op n) =
        ((ι.app (L.obj C)).f i).app (op n) := by
    dsimp [z, u, R]
    simp only [Functor.mapHomologicalComplex_map_f]
    change (a.unit.app (C.X i) ≫ lim.map ((ι.app (L.obj C)).f i)) ≫
      limit.π _ (op n) = _
    simp [a, constLimAdj]
  refine ⟨z, hz, ?_, (d.constantRlimAdjunction T).unit, rfl, ?_, ?_⟩
  · intro C w hw
    apply HomologicalComplex.Hom.ext
    funext i
    apply limit.hom_ext
    intro n
    exact (hw i n.unop).trans (hz C i n.unop).symm
  · intro C
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (d.constantTower T).mapDerivedCategoryFactorsh.hom
      (completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnit
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
    have hfac : (d.constantTower T).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj C) =
        (d.constantTower T).mapDerivedCategoryFactors.hom.app C := by
      simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
        Functor.mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso,
        Quotient.lift.isLift_hom, Quotient.lift.isLift_inv, Functor.comp_obj]
      erw [DerivedCategory.Qh.map_id]
      erw [(d.constantTower T).mapDerivedCategory.map_id]
      erw [Category.id_comp]
      repeat erw [Category.comp_id]
    rw [hfac] at hu
    change (d.constantRlimAdjunction T).unit.app (DerivedCategory.Q.obj C) ≫
        (completedRlim T (d.completedRing T)).map
          ((d.constantTower T).mapDerivedCategoryFactors.hom.app C) =
      DerivedCategory.Q.map (u.app C) ≫
        (completedRlimUnit T (d.completedRing T)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (L.obj C)) at hu
    have hn := (completedRlimUnit T (d.completedRing T)).naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map (ι.app (L.obj C)))
    change DerivedCategory.Q.map (R.map (ι.app (L.obj C))) ≫
        (completedRlimUnit T (d.completedRing T)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (J.obj (L.obj C))) =
      (completedRlimUnit T (d.completedRing T)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (L.obj C)) ≫
        (completedRlim T (d.completedRing T)).map
          (DerivedCategory.Q.map (ι.app (L.obj C))) at hn
    rw [Functor.map_comp, ← Category.assoc, hu, Category.assoc, ← hn,
      ← Category.assoc, ← Functor.map_comp]
    rfl
  · intro C D h
    exact ((d.constantRlimAdjunction T).unit.naturality h).symm

end AlgebraicGeometry.Scheme
