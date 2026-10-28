/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorCochainData
public import Sheaf.SixFunctors.OpenTensorRepresentativeData

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
  (A : SemilinearSections.Closed.{c, v, r} J R) (T : SemilinearSections.Models.{c, v, r} J R A)

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (A' : SemilinearSections.Closed.{c, v, r} J' R')
  (T' : SemilinearSections.Models.{c, v, r} J' R' A')
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

def canonicalProjectionMate
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (S : E × E ⥤ E) (T : D × D ⥤ D)
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    (μ : S ⋙ G ≅ (G.prod G) ⋙ T) :
    (𝟭 D).prod G ⋙ T ⋙ F ⟶ (F.prod (𝟭 E)) ⋙ S where
  app X := (adj.homEquiv _ _).symm
    (T.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫ μ.inv.app (F.obj X.1, X.2))
  naturality := by
    intro X Y f
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (F.map (T.map (Prod.mkHom f.1 (G.map f.2))) ≫ _) =
      adj.homEquiv _ _ (_ ≫ S.map (Prod.mkHom (F.map f.1) f.2))
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp only [Functor.prod_obj, Functor.comp_obj, Functor.id_obj]
    simp only [Equiv.apply_symm_apply]
    have hμ := μ.inv.naturality (Prod.mkHom (F.map f.1) f.2)
    change T.map (Prod.mkHom (G.map (F.map f.1)) (G.map f.2)) ≫
      μ.inv.app (F.obj Y.1, Y.2) =
      μ.inv.app (F.obj X.1, X.2) ≫ G.map (S.map (Prod.mkHom (F.map f.1) f.2)) at hμ
    rw [Category.assoc, ← hμ]
    simp only [← Category.assoc, ← T.map_comp]
    congr 2
    apply Prod.hom_ext
    · exact adj.unit.naturality f.1
    · simp

private theorem canonicalProjectionMate_homEquiv
    {E : Type u₁} {D : Type u₂} [Category.{v₁} E] [Category.{v₂} D]
    (S : E × E ⥤ E) (T : D × D ⥤ D)
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    (μ : S ⋙ G ≅ (G.prod G) ⋙ T)
    (X : D × E) :
    adj.homEquiv _ _ ((canonicalProjectionMate S T F G adj μ).app X) =
      T.map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫
        μ.inv.app (F.obj X.1, X.2) := by
  exact Equiv.apply_symm_apply _ _


/-- The canonical adjunction-transpose projection identity on resolving pairs.
The one-flat comparisons agree with the simultaneous K-flat models; both input
complexes are flat-term K-flat representatives. Source: Stacks 0GL1, 07A4 and
06YS--06YT (blueprint: lem-sf-open-tensor-projection-mate-canonical).

Proof: first show that F carries flat modules to flat modules. The ordinary
projection isomorphisms, their naturality, and symmetry identify tensoring with
F(M) with the composite of exact G, tensoring with the flat M, and exact F.
For a K-flat complex C, test F(C) against any acyclic complex P: exact G carries
P to an acyclic complex, K-flatness of C makes its tensor with G(P) acyclic,
and exact F preserves acyclicity. The chain projection and tensor symmetry
identify this with the required acyclicity test for F(C). Thus F(C) is K-flat
with flat terms. D.pullKFlat and D.pullFlat give the same properties for G(P).
On each signed total summand, D.ordinaryInverse, hordinary, D.summand and
restrictionModel.summand identify the adjunct of D.chain.inv with the tensor
of the cochain adjunction unit and identity followed by restrictionModel.chain.
Coproduct extensionality gives the cochain equality. Localize it using the
unit equation for exactDerivedAdjunction and the exact-functor factorization
isomorphisms. Apply restrictionModel.derived to F(C), P; naturality of the
simultaneous comparison handles the cochain unit. Finally ambientBoth and
openBoth replace the supplied comparisons by those simultaneous comparisons.
The defining hom-equivalence formula for canonicalProjectionMate, followed by
injectivity of that equivalence and cancellation of the chain isomorphism,
gives the displayed equation. -/
theorem openTensorProjection_mate_canonical
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J R A T ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J' R' A' T' openModel)
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R') C)
    (flatC : flatTerms.{c, v, r} J' R' C)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P) :
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P))) ≫
        (canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
          G.mapDerivedCategory
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj)
          restriction).app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
