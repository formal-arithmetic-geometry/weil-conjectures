/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization

/-! # The augmented projection mate in the derived category of strict towers

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 0B56,
equation-projection-formula-map, on the diagram sites of strict inverse sequences
(blueprint: lem-weil-pbc-augmented-diagram-projection-mate).

We use the equivalent adjoint description in the node. Evaluated reduction means
`B` followed by exact evaluation: its universal counit in StrictReduction identifies
it with derived tensor by the indicated coefficient algebra. Thus the evaluation
formula below is the ambient counit-tensor mate, with all interchange maps written out.
Natural number n encodes the positive level n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe uA vA uB vB wA wB wTA wTB
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.StrictReduction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]

/-- The already specified derived direct images, canonical adjunctions, and normalized
constant/evaluation comparisons, grouped as presentation data. The Hom equations are
exactly those of tower-derived-evaluation-normalization. The last two equations specify
chi and beta uniquely as adjunction mates, so these are not arbitrary isomorphisms.
Source: Stacks 07A6 and 0A07; the counit normalizations of
lem-weil-pbc-constant-tower-pushforward-normalization and
lem-weil-pbc-tower-derived-evaluation-normalization
(blueprint: lem-weil-pbc-augmented-diagram-projection-mate). -/
structure AugmentedProjectionDirectImage (F : B ⥤ A) (G : A ⥤ B)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) where
  RG : DerivedCategory A ⥤ DerivedCategory B
  RT : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  eta : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG
  etaT : (termwise G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RT
  universal : RG.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso A (.up ℤ))
  universalT : RT.IsRightDerivedFunctor etaT
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  d : F.mapDerivedCategory ⊣ RG
  dT : (termwise F).mapDerivedCategory ⊣ RT
  hom_normalization : ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (g : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
    d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
      (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ eta.app I
  tower_hom_normalization : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (g : ((termwise F).mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
    dT.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
      ((termwise F).mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map
          (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ etaT.app I
  chi : RG ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ≅
    (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ RT
  beta : ∀ n : ℕᵒᵖ,
    RT ⋙ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ RG
  chi_counit : ∀ M : DerivedCategory A,
    (termwise F).mapDerivedCategory.map (chi.hom.app M) ≫
        dT.counit.app ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj M) =
      (ringedConstantTowerPullback F).hom.app (RG.obj M) ≫
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.map (d.counit.app M)
  beta_counit : ∀ (n : ℕᵒᵖ) (M : DerivedCategory (ℕᵒᵖ ⥤ A)),
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map (dT.counit.app M) =
      (towerDerivedEvaluationInterchange F n).hom.app (RT.obj M) ≫
        F.mapDerivedCategory.map ((beta n).hom.app M) ≫
          d.counit.app (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.obj M)

/-- The actual natural projection map, formed in the derived category of strict towers.
It is the tower-adjunction unit followed by the normalized reduction comparison and
reduction of the ambient counit. No maps are assembled from their evaluations.
Source: Stacks 0B56, equation-projection-formula-map, equivalent adjoint description
(blueprint: lem-weil-pbc-augmented-diagram-projection-mate). -/
def augmentedDiagramProjection
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (P : AugmentedProjectionDirectImage F G adj)
    (BY : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (BX : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
    (tau : BY ⋙ (termwise F).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ BX) :
    P.RG ⋙ BY ⟶ BX ⋙ P.RT :=
  Functor.whiskerLeft (P.RG ⋙ BY) P.dT.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft P.RG tau.hom) P.RT ≫
      Functor.whiskerRight (Functor.whiskerRight P.d.counit BX) P.RT

end CategoryTheory.StrictReduction

namespace CategoryTheory.StrictReduction
open CochainPullback

universe uC vC uD vD r dR dS dTY dTX
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{dR} (Modules R)] [HasDerivedCategory.{dS} (Modules S)]
  [HasDerivedCategory.{dTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{dTX} (ℕᵒᵖ ⥤ Modules S)]

/-- The strict augmented projection map, its adjoint description, its evaluated
counit-tensor description, and the augmentation identity before evaluation or Rlim.
Source: Stacks 07A4, lemma-pullback-tensor-product, 07A6, lemma-adjoint, and 0B56,
equation-projection-formula-map, on the diagram sites
(blueprint: lem-weil-pbc-augmented-diagram-projection-mate).

Proof:
1. The explicit unit construction is the tower-adjunction Hom equivalence applied to
   tau followed by BX of the ambient counit. Apply its inverse to get the first equation.
2. Apply the inverse ambient Hom equivalence to the evaluated equation and precompose
   with the invertible evaluation interchange. Its naturality and beta_counit reduce
   the equation to evaluation of the first equation. Cancel the interchange and its inverse.
3. Uniqueness of the normalized reduction comparison gives augmentation compatibility
   for the supplied tau. Apply the inverse tower Hom equivalence to both augmentation
   composites. The first equation, augmentation compatibility and naturality of iX give
   the first transpose. Naturality of the tower counit and chi_counit give the second.
   The constant-tower interchanges in these transposes are definitionally equal, since
   their ordinary components are identities. Injectivity gives the strict-tower equality.
No inverse limit, perfectness, invertibility of h, boundedness or completeness is used. -/
theorem augmentedDiagramProjectionMate
    (f : RingedPullback R S) [IsIso f.coefficient] [f.V.Additive]
    [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : CommMon (ℕᵒᵖ ⥤ Modules R))
    (MY : RingedModel Q.X (MonObj.one (X := Q.X)))
    (MX : RingedModel (Q.X ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X))))
    (tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B)
    (htau : IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
      (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau)
    (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj) :
    (∀ M : DerivedCategory (Modules S),
      (termwise f.L).mapDerivedCategory.map
          ((augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M) ≫
        P.dT.counit.app (MX.B.obj M) =
      tau.hom.app (P.RG.obj M) ≫ MX.B.map (P.d.counit.app M)) ∧
    (∀ (n : ℕᵒᵖ) (M : DerivedCategory (Modules S)),
      ((evaluation ℕᵒᵖ (Modules R)).obj n).mapDerivedCategory.map
          ((augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M) ≫
        (P.beta n).hom.app (MX.B.obj M) =
      P.d.homEquiv
        (((evaluation ℕᵒᵖ (Modules R)).obj n).mapDerivedCategory.obj (MY.B.obj (P.RG.obj M)))
        (((evaluation ℕᵒᵖ (Modules S)).obj n).mapDerivedCategory.obj (MX.B.obj M))
        ((towerDerivedEvaluationInterchange f.L n).inv.app (MY.B.obj (P.RG.obj M)) ≫
          ((evaluation ℕᵒᵖ (Modules S)).obj n).mapDerivedCategory.map
            (tau.hom.app (P.RG.obj M)) ≫
          ((evaluation ℕᵒᵖ (Modules S)).obj n).mapDerivedCategory.map
            (MX.B.map (P.d.counit.app M)))) ∧
    (∀ M : DerivedCategory (Modules S),
      MY.i.app (P.RG.obj M) ≫
          (augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M =
        P.chi.hom.app M ≫ P.RT.map (MX.i.app M)) := by
  have hmate (M : DerivedCategory (Modules S)) :
      (augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M =
        P.dT.homEquiv _ _ (tau.hom.app (P.RG.obj M) ≫ MX.B.map (P.d.counit.app M)) := by
    simp only [augmentedDiagramProjection, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Adjunction.homEquiv_unit,
      Functor.map_comp]
  have hc (M : DerivedCategory (Modules S)) :
      (termwise f.L).mapDerivedCategory.map
          ((augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M) ≫
        P.dT.counit.app (MX.B.obj M) =
      tau.hom.app (P.RG.obj M) ≫ MX.B.map (P.d.counit.app M) := by
    rw [hmate]
    exact (P.dT.homEquiv _ _).symm_apply_apply _
  refine ⟨hc, ?_, ?_⟩
  · intro n M
    apply (P.d.homEquiv _ _).symm.injective
    erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp]
    let E := ((evaluation ℕᵒᵖ (Modules S)).obj n).mapDerivedCategory
    let c := towerDerivedEvaluationInterchange f.L n
    let h := (augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M
    apply (cancel_epi (c.hom.app (MY.B.obj (P.RG.obj M)))).mp
    calc
      _ = E.map ((termwise f.L).mapDerivedCategory.map h) ≫
          (c.hom.app (P.RT.obj (MX.B.obj M)) ≫
            f.L.mapDerivedCategory.map ((P.beta n).hom.app (MX.B.obj M)) ≫
              P.d.counit.app (E.obj (MX.B.obj M))) := by
        simpa only [c, E, h, Category.assoc, Functor.comp_map, Functor.comp_obj] using
          congrArg (fun g ↦ g ≫
            f.L.mapDerivedCategory.map ((P.beta n).hom.app (MX.B.obj M)) ≫
              P.d.counit.app (E.obj (MX.B.obj M))) (c.hom.naturality h).symm
      _ = E.map ((termwise f.L).mapDerivedCategory.map h) ≫
          E.map (P.dT.counit.app (MX.B.obj M)) := by
        rw [← P.beta_counit n (MX.B.obj M)]
      _ = E.map (tau.hom.app (P.RG.obj M) ≫ MX.B.map (P.d.counit.app M)) := by
        rw [← E.map_comp, hc M]
      _ = _ := by
        simp only [c, Iso.hom_inv_id_app_assoc, E, Functor.map_comp]
  · intro M
    obtain ⟨tau', hn, hu, ha, _⟩ := (reductionPullbackDerivedTower f k Q).2.2.2 MY MX
    have heq := hu tau htau
    subst tau'
    apply (P.dT.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hc M]
    rw [← Category.assoc, ha (P.RG.obj M), Category.assoc]
    erw [← MX.i.naturality (P.d.counit.app M)]
    erw [P.dT.counit.naturality (MX.i.app M)]
    simp only [Functor.id_map]
    rw [reassoc_of% (P.chi_counit M)]
    rfl

end CategoryTheory.StrictReduction
