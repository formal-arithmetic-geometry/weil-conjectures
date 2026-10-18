/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.ModulePullbackTensorIso
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Paper.RingedTopoiTensorSections

/-!
# Tensor normalization for the open comparison

Source: Stacks Project, Tag 09AF, `lemma-jshriek-comparison`; the tensor refinement
(blueprint: lem-sf-open-comparison-tensor-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The tensor comparison for the comparison inverse image is the canonical oplax
monoidal comparison, viewed as an isomorphism.
Source: Stacks, Tag 03EL; 
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def comparisonTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {T : Scheme.{u}} (V W : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj (V ⊗ W) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj V ⊗
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj W :=
  asIso (Functor.OplaxMonoidal.δ (comparisonUpperStar (ModuleCat.{u + 1} A) T) V W)

/-- The canonical tensor comparison for restriction to an étale open, transported from
`j^*` along the recorded localization isomorphism.
Source: Stacks, Tags 03DI and 03EL; 
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def etaleRestrictionTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V W : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj (V ⊗ W) ≅
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj V ⊗
        (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj W := by
  let i := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j
    (inferInstance : Etale j)
  exact asIso (i.inv.app (V ⊗ W) ≫
    Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) j) V W ≫
      (i.hom.app V ⊗ₘ i.hom.app W))

/-- The canonical tensor comparison for restriction to a pro-étale open, transported from
`j^*` along the recorded localization isomorphism.
Source: Stacks, Tags 03DI and 03EL; 
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def proEtaleRestrictionTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V W : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj (V ⊗ W) ≅
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj V ⊗
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj W := by
  let i := AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} A) j (inferInstance : WeaklyEtale j)
  exact asIso (i.inv.app (V ⊗ W) ≫
    Functor.OplaxMonoidal.δ ((j)^*[ModuleCat.{u + 1} A]) V W ≫
      (i.hom.app V ⊗ₘ i.hom.app W))

/-- The étale projection formula map is the transpose of the open-adjunction unit tensored
with the restricted second factor, using the canonical restriction tensor comparison.
Source: Stacks, Tag 03DI; 
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def openComparisonEtaleKappa (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        (F ⊗ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B) ⟶
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F ⊗ B :=
  (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _ |>.symm
    (((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app F ⊗ₘ
        𝟙 ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B)) ≫
      (etaleRestrictionTensorIso A j
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) B).inv)

/-- The pro-étale projection formula map is the analogous transpose for the pro-étale open.
Source: Stacks, Tag 03DI; 
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def openComparisonProEtaleKappa (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))
    (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        (G ⊗ (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj H) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj G ⊗ H :=
  (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _ |>.symm
    (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app G ⊗ₘ
        𝟙 ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj H)) ≫
      (proEtaleRestrictionTensorIso A j
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj G) H).inv)

/-- The left side of the tensor-normalization square in the node statement.
Source: Stacks Project, Tag 09AF, with the tensor refinement of Tag 03EL
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def openComparisonTensorLeft (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          (F ⊗ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B)) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⊗
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj B :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      (openComparisonEtaleKappa A j F B) ≫
    (comparisonTensorIso A ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) B).hom ≫
    ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).hom.app F ⊗ₘ
      𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj B))

/-- The right side of the tensor-normalization square in the node statement.
Source: Stacks Project, Tag 09AF, with the tensor refinement of Tag 03EL
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
noncomputable def openComparisonTensorRight (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          (F ⊗ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B)) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⊗
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj B :=
  (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).hom.app
      (F ⊗ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map
      ((comparisonTensorIso A F
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B)).hom ≫
        (𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⊗ₘ
          (openComparisonRestrictionIso A j).hom.app B)) ≫
    openComparisonProEtaleKappa A j
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj B)

/-- Tensor compatibility of the étale/pro-étale open-extension comparison. The displayed
maps are equal and form a natural transformation in both sheaf variables.

Source: Stacks Project, Tag 09AF, label `lemma-jshriek-comparison`, and Tag 03EL.

Proof plan, following the six steps of the node:
1. Put N = F tensor rB and M = d(C_U F) tensor C_X B. For h : C_X(eN) to M,
   apply C_U to the etale open unit, then a, then s(h). The unit equation of
   lem-sf-open-comparison-unit-normalization identifies this with the pro-etale
   transpose of c_N inverse followed by h. It is injective by the open Hom bijection
   (lem-weil-pbc-extension-by-zero-adjunction,
   lem-weil-proetale-weakly-etale-localization,
   lem-pur-site-restriction-module-adjunction-exact), without assuming s faithful.
2. The tensor maps t and rho are the canonical pullback comparisons of
   lem-weil-pbc-ringed-topoi-module-pullback-tensor. The constant-ring identification
   of lem-sf-comparison-pullback-exact identifies the algebraic inverse image.
   Naturality of the canonical a with product projections and the pure pairing gives
   rho^d s(t^X) a = (a tensor a) t^U C_U(rho^e). Both sides send a transported
   pure pair to a(x) tensor a(y); the scalar maps agree on A. Use
   lem-weil-pbc-algebraic-inverse-image-tensor-comparison and
   def-weil-pbc-ringed-tensor-section-calculus to determine tensor maps by these
   pairings, without treating every sheafified section as a pure tensor.
3. Apply the injective map of step 1 to the left composite. Naturality of a, rho and t,
   and the defining transpose equation for kappa^e, reduce its image after rho^d to
   (s(c_F) a C_U(eta^e_F) tensor a_B) t^U. The unit-normalization theorem makes
   this (eta^d tensor a_B) t^U.
4. Set q = t^U followed by 1 tensor a_B. Apply step 1 to the right composite.
   Unit normalization at N and naturality of eta^d turn its image into the transpose
   of kappa^d followed by q. The defining unit prescription for kappa^d gives,
   after rho^d, the same (eta^d tensor a_B) t^U.
5. Cancel the restriction tensor isomorphism rho^d and use injectivity from step 1
   to obtain the equality, with the displayed source and target.
6. Naturality of each open unit tensored with the restricted second arrow gives
   naturality of each kappa by the corresponding Hom bijection. Compose with
   naturality of a, c and t to get simultaneous naturality in F and B.
Identity and empty open immersions, zero sheaves and the zero coefficient ring require
no additional hypothesis.
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
theorem openComparison_tensor_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      openComparisonTensorLeft A j F B = openComparisonTensorRight A j F B) ∧
    (∀ {F F' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)}
      {B B' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
      (f : F ⟶ F') (b : B ⟶ B'),
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map (f ⊗ₘ
            (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map b)) ≫
          openComparisonTensorLeft A j F' B' =
        openComparisonTensorLeft A j F B ≫
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map
              ((comparisonUpperStar (ModuleCat.{u + 1} A) U).map f) ⊗ₘ
            (comparisonUpperStar (ModuleCat.{u + 1} A) X).map b)) := by
  sorry

end AlgebraicGeometry.ProEtale
