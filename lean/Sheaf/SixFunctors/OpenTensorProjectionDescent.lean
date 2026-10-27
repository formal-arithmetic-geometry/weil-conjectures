/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorCochainData
public import Sheaf.SixFunctors.OpenTensorRepresentativeData

/-! # Descent of an ordinary open tensor projection

Source: Stacks 0GL1, 07A4, 06YS and 06YT
(blueprint: lem-sf-open-tensor-projection-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
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

/-- Descend the ordinary projection comparison, with its specified inverse transpose,
through the supplied tensor models. This constructs only the derived projection and
its representative equation; the restriction comparison and all ordinary data are inputs.
Source: Stacks 0GL1, proof of lemma-j-shriek-and-tensor; 07A4 and 06YS--06YT
(blueprint: lem-sf-open-tensor-projection-descent).

Proof: first observe that F preserves flat terms and K-flat complexes. For a flat
module M, tensor(F M,-) is identified by D.ordinary with the composite of exact
G, tensor(M,-), and exact F, hence is exact. For a K-flat C and an acyclic test
P, exact G makes G P acyclic; D.chain identifies tensor(F C,P) with
F tensor(C,G P), which is acyclic by K-flatness and exactness of F. Tensor
symmetry gives the acyclicity test in its prescribed order.
Resolve both inputs by flat-term K-flat complexes. For a K-flat P, the source
Tot(F C tensor P) computes the ambient tensor even though F C need not be K-flat.
The target F Tot(C tensor G P) computes the open tensor since G P is K-flat.
Compose the inverse ambient comparison, Q of D.chain, the exact F factorization,
and F of the open comparison. Chain naturality and the naturality of both one-flat
comparisons make this a natural isomorphism on resolving pairs. Two-variable
localization on flat-term K-flat complexes descends it to gamma. Resolve only C
and use the two one-flat naturality squares and D.chainNaturality to prove the
same equation for arbitrary C and flat-term K-flat P; cancel the localized
resolution maps. To identify the inverse transpose, work first with both inputs
flat-term K-flat. D.ordinaryInverse and the summand formulas for D.chain and the
restrictionModel identify its chain adjoint with unit tensor identity followed
by the inverse restriction comparison. The exact derived adjunction is the
localization of the chain adjunction, so the same equation holds after Q, with
the exact-functor factorization isomorphisms inserted. The supplied both-model
identities identify the simultaneous comparisons used here. Naturality and
localization then give the inverse equation on all derived inputs. No inference
from equality after finite evaluations is used. -/
theorem openTensorProjection_descent
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J R A T ambientModel)
    (ambientNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1}
      J R A ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1} J' R' A' T' openModel)
    (openNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r) + 1}
      J' R' A' openModel) :
    ∃ gamma : (F.mapDerivedCategory.prod (𝟭 _)) ⋙ A.tensor ≅
    (𝟭 _).prod G.mapDerivedCategory ⋙ A'.tensor ⋙ F.mapDerivedCategory,
      (∀ M N,
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
        (gamma.inv.app (M, N)) =
      A'.tensor.map (Prod.mkHom
          ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
          (𝟙 (G.mapDerivedCategory.obj N))) ≫
        restriction.inv.app (F.mapDerivedCategory.obj M, N)) ∧
      (∀ (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P),
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) ≫
        gamma.hom.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P)))) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
