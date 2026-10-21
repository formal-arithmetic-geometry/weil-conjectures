/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.CompletedPullback

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

private def resolutionUnitMap
    {B E : Type*} [Category B] [Category E] [Preadditive B] [Preadditive E]
    {L : B ⥤ E} {R : E ⥤ B} [L.Additive] [R.Additive] (a : L ⊣ R)
    (J : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (ι : 𝟭 (CochainComplex E ℤ) ⟶ J) :
    𝟭 (CochainComplex B ℤ) ⟶ L.mapHomologicalComplex (.up ℤ) ⋙ J ⋙
      R.mapHomologicalComplex (.up ℤ) where
  app C := (a.mapHomologicalComplex (.up ℤ)).unit.app C ≫
    (R.mapHomologicalComplex (.up ℤ)).map
      (ι.app ((L.mapHomologicalComplex (.up ℤ)).obj C))
  naturality C D f := by
    let LC := L.mapHomologicalComplex (.up ℤ)
    let RC := R.mapHomologicalComplex (.up ℤ)
    let ac := a.mapHomologicalComplex (.up ℤ)
    have hu : f ≫ ac.unit.app D = ac.unit.app C ≫ RC.map (LC.map f) :=
      ac.unit.naturality f
    have hi : RC.map (LC.map f) ≫ RC.map (ι.app (LC.obj D)) =
        RC.map (ι.app (LC.obj C)) ≫ RC.map (J.map (LC.map f)) := by
      simpa only [Functor.id_map, Functor.map_comp] using
        congrArg RC.map (ι.naturality (LC.map f))
    change f ≫ (ac.unit.app D ≫ RC.map (ι.app (LC.obj D))) =
      (ac.unit.app C ≫ RC.map (ι.app (LC.obj C))) ≫ RC.map (J.map (LC.map f))
    rw [← Category.assoc, hu, Category.assoc, hi, Category.assoc]

private theorem resolutionUnitMap_app
    {B E : Type*} [Category B] [Category E] [Preadditive B] [Preadditive E]
    {L : B ⥤ E} {R : E ⥤ B} [L.Additive] [R.Additive] (a : L ⊣ R)
    (J : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (ι : 𝟭 (CochainComplex E ℤ) ⟶ J) (C : CochainComplex B ℤ) :
    (resolutionUnitMap a J ι).app C =
      (a.mapHomologicalComplex (.up ℤ)).unit.app C ≫
        (R.mapHomologicalComplex (.up ℤ)).map
          (ι.app ((L.mapHomologicalComplex (.up ℤ)).obj C)) := rfl

-- Keep the naturality proof and the underlying functor data behind the application API.
attribute [irreducible] resolutionUnitMap

set_option backward.isDefEq.respectTransparency false in
private theorem derivedUnit_factorization
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions E]
    {L : B ⥤ E} {R : E ⥤ B} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (C : CochainComplex B ℤ) :
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj C) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app C) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app C) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj C)) := by
  simp only [Adjunction.mapDerivedCategoryRightDerivedAdjunction, Adjunction.derived_unit]
  have hf := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj C)
  rw [L.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hf
  dsimp only [Functor.comp_obj] at hf
  have hid : DerivedCategory.Qh.map
      ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app C) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = _
    exact DerivedCategory.Qh.map_id _
  rw [hid] at hf
  have hqhom : (DerivedCategory.quotientCompQhIso B).hom.app C = 𝟙 _ := rfl
  have hqinv : (DerivedCategory.quotientCompQhIso E).inv.app
      ((L.mapHomologicalComplex (.up ℤ)).obj C) = 𝟙 _ := rfl
  rw [hqhom, hqinv] at hf
  change ((a.mapHomotopyCategory (.up ℤ)).derivedη
      (HomotopyCategory.quasiIso B (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit).app (DerivedCategory.Q.obj C) ≫ R.rightDerivedFunctor.map
        (L.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj C)) ≫
          L.mapDerivedCategoryFactors.hom.app C ≫
          𝟙 (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj C)) ≫
          𝟙 (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj C))) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app C) ≫
      R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj C)) at hf
  erw [Category.comp_id, Category.comp_id, L.mapDerivedCategory.map_id,
    Category.id_comp] at hf
  exact hf

-- The prescribed interface retains both resolution hypotheses; the unit identity is formal.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
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
  let L := d.constantTower T
  let R := completedTowerLimit T (d.completedRing T)
  let a : L ⊣ R := constLimAdj
  let LC := L.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let ac := a.mapHomologicalComplex (.up ℤ)
  let z := resolutionUnitMap a J ι
  have hz (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
      (i : ℤ) (n : ℕ) :
      (z.app C).f i ≫ limit.π ((J.obj (LC.obj C)).X i) (op n) =
        ((ι.app (LC.obj C)).f i).app (op n) := by
    dsimp only [z]
    rw [resolutionUnitMap_app]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    change a.unit.app (C.X i) ≫ lim.map _ ≫ limit.π _ (op n) = _
    erw [limMap_π]
    rw [← Category.assoc]
    have hp : a.unit.app (C.X i) ≫ limit.π (L.obj (C.X i)) (op n) = 𝟙 _ :=
      limit.lift_π _ _
    erw [hp, Category.id_comp]
  refine ⟨z, hz, ?_, (d.constantRlimAdjunction T).unit, rfl, ?_, ?_⟩
  · intro C w hw
    apply HomologicalComplex.Hom.ext
    funext i
    apply limit.hom_ext
    intro n
    exact (hw i n.unop).trans (hz C i n.unop).symm
  · intro C
    have hf := derivedUnit_factorization a C
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj C) ≫
      R.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactors.hom.app C ≫ DerivedCategory.Q.map (ι.app (LC.obj C))) =
      DerivedCategory.Q.map (z.app C) ≫
        R.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj (J.obj (LC.obj C)))
    have hzapp : z.app C = ac.unit.app C ≫ RC.map (ι.app (LC.obj C)) :=
      resolutionUnitMap_app a J ι C
    rw [hzapp]
    erw [Functor.map_comp, ← Category.assoc, hf, Category.assoc]
    have hn := R.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient _ _).map (ι.app (LC.obj C)))
    change DerivedCategory.Q.map (RC.map (ι.app (LC.obj C))) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          (J.obj (LC.obj C))) =
      R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj (LC.obj C)) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Q.map (ι.app (LC.obj C))) at hn
    rw [← hn, ← Category.assoc, ← Functor.map_comp]
  · intro C D f
    exact ((d.constantRlimAdjunction T).unit.naturality f).symm

end AlgebraicGeometry.Scheme
