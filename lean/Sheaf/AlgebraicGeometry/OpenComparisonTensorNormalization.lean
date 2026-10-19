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



private lemma transported_tensor_natural
    {E H : Type*} [Category E] [Category H] [MonoidalCategory E] [MonoidalCategory H]
    {T R : E ⥤ H} [T.OplaxMonoidal] (i : T ≅ R)
    {V V' W W' : E} (f : V ⟶ V') (g : W ⟶ W') :
    R.map (f ⊗ₘ g) ≫ i.inv.app (V' ⊗ W') ≫
        Functor.OplaxMonoidal.δ T V' W' ≫ (i.hom.app V' ⊗ₘ i.hom.app W') =
      (i.inv.app (V ⊗ W) ≫ Functor.OplaxMonoidal.δ T V W ≫
        (i.hom.app V ⊗ₘ i.hom.app W)) ≫ (R.map f ⊗ₘ R.map g) := by
  rw [i.inv.naturality_assoc, ← Functor.OplaxMonoidal.δ_natural_assoc]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  rw [i.hom.naturality f, i.hom.naturality g]

private lemma restriction_tensor_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {V V' W W' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : V ⟶ V') (g : W ⟶ W') :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map (f ⊗ₘ g) ≫
        (etaleRestrictionTensorIso A j V' W').hom =
      (etaleRestrictionTensorIso A j V W).hom ≫
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map f ⊗ₘ
          (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map g) := by
  exact transported_tensor_natural
    (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j
      (inferInstance : Etale j)) f g

private lemma etale_kappa_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {F F' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {B B' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : F ⟶ F') (b : B ⟶ B') :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map
        (f ⊗ₘ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map b) ≫
      openComparisonEtaleKappa A j F' B' =
    openComparisonEtaleKappa A j F B ≫
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).map f ⊗ₘ b) := by
  let adj := Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  apply (adj.homEquiv _ _).injective
  dsimp only [adj]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [openComparisonEtaleKappa, Equiv.apply_symm_apply]
  apply (cancel_mono (etaleRestrictionTensorIso A j
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F') B').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [restriction_tensor_natural A j]
  simp only [Iso.inv_hom_id_assoc]
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  exact congrArg (fun k ↦ k ⊗ₘ
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map b)
      (adj.unit.naturality f)


private lemma monoidal_delta_natural
    {E H : Type*} [Category E] [Category H] [MonoidalCategory E] [MonoidalCategory H]
    {T R : E ⥤ H} [T.Monoidal] [R.Monoidal]
    (a : T ⟶ R) [NatTrans.IsMonoidal a] (V W : E) :
    a.app (V ⊗ W) ≫ Functor.OplaxMonoidal.δ R V W =
      Functor.OplaxMonoidal.δ T V W ≫ (a.app V ⊗ₘ a.app W) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ T V W)).1
  rw [← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id,
    Functor.Monoidal.μ_δ_assoc]

/-- The canonical restriction comparison intertwines the transported tensor comparisons.
Source: Stacks Project, Tags 09AF and 03EL; step 2 of
lem-sf-open-comparison-tensor-normalization.

Proof: Substitute the definition of the restriction comparison: the inverse etale
localization identification, the canonical comparison of pullbacks, and the pro-etale
localization identification. Substitute the transported tensor comparisons on both
restrictions. Cancel the localization identifications using their inverse equations
and naturality. The remaining square is the oplax monoidality equation of the canonical
comparison of inverse images, which is the conjugate of the monoidal comparison of
right adjoints. The latter comparison is induced by the same fibre-product identity
on the site functors, so its monoidality follows from the monoidality of sheaf
pushforward composition. This argument applies to identity and empty opens, zero
sheaves and the zero coefficient ring, since it uses no nonvanishing assumptions.
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
private lemma openComparison_restriction_tensor_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V W : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openComparisonRestrictionIso A j).hom.app (V ⊗ W) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          (comparisonTensorIso A V W).hom ≫
        (proEtaleRestrictionTensorIso A j
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj V)
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj W)).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
          (etaleRestrictionTensorIso A j V W).hom ≫
        (comparisonTensorIso A
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj V)
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj W)).hom ≫
        ((openComparisonRestrictionIso A j).hom.app V ⊗ₘ
          (openComparisonRestrictionIso A j).hom.app W)  := by
  let E := Etale.upperStar (ModuleCat.{u + 1} A) j
  let P := upperStar (ModuleCat.{u + 1} A) j
  let C := comparisonUpperStar (ModuleCat.{u + 1} A) U
  let D := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let b := (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).inv
  have hb := monoidal_delta_natural b V W
  let r := Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j
  let s := openImmersionRestriction (ModuleCat.{u + 1} A) j
  let i := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j
    (inferInstance : Etale j)
  let k := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j
    (inferInstance : WeaklyEtale j)
  change (C.map (i.inv.app (V ⊗ W)) ≫ b.app (V ⊗ W) ≫
      k.hom.app (D.obj (V ⊗ W))) ≫ s.map (Functor.OplaxMonoidal.δ D V W) ≫
      k.inv.app (D.obj V ⊗ D.obj W) ≫
      Functor.OplaxMonoidal.δ P (D.obj V) (D.obj W) ≫
      (k.hom.app (D.obj V) ⊗ₘ k.hom.app (D.obj W)) =
    C.map (i.inv.app (V ⊗ W) ≫ Functor.OplaxMonoidal.δ E V W ≫
      (i.hom.app V ⊗ₘ i.hom.app W)) ≫
      Functor.OplaxMonoidal.δ C (r.obj V) (r.obj W) ≫
      ((C.map (i.inv.app V) ≫ b.app V ≫ k.hom.app (D.obj V)) ⊗ₘ
        (C.map (i.inv.app W) ≫ b.app W ≫ k.hom.app (D.obj W)))
  simp only [Functor.map_comp, Category.assoc]
  have hk := k.hom.naturality (Functor.OplaxMonoidal.δ D V W)
  change P.map (Functor.OplaxMonoidal.δ D V W) ≫ k.hom.app (D.obj V ⊗ D.obj W) =
    k.hom.app (D.obj (V ⊗ W)) ≫ s.map (Functor.OplaxMonoidal.δ D V W) at hk
  rw [← reassoc_of% hk]
  simp only [Iso.hom_inv_id_app_assoc]
  have hi := Functor.OplaxMonoidal.δ_natural C (i.hom.app V) (i.hom.app W)
  change Functor.OplaxMonoidal.δ C (E.obj V) (E.obj W) ≫
      (C.map (i.hom.app V) ⊗ₘ C.map (i.hom.app W)) =
    C.map (i.hom.app V ⊗ₘ i.hom.app W) ≫
      Functor.OplaxMonoidal.δ C (r.obj V) (r.obj W) at hi
  rw [← reassoc_of% hi]
  simp only [tensorHom_comp_tensorHom, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  simp only [Category.assoc]
  dsimp only [Functor.OplaxMonoidal.comp_δ] at hb
  rw [reassoc_of% hb]
  simp only [tensorHom_comp_tensorHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [C.map_id, C.map_id]
  simp only [Category.id_comp]
  rfl

/-- The transpose of the transported etale projection map, followed by the pro-etale
restriction tensor comparison, is the open unit tensored with the restriction comparison.

Source: Stacks Project, Tag 09AF, lemma-jshriek-comparison, and Tag 03EL,
lemma-tensor-product-pullback; steps 1--3 of the parent node.

Proof: Write C and D for comparison on U and X, e and d for open extensions,
r and s for restrictions, c for the extension comparison and a for the restriction
comparison. The unit normalization gives
C(eta_N) a_(eN) s(c_N) = eta_(CN). Thus the transpose of c_N inverse followed
by a map h is C(eta_N) a_(eN) s(h). Apply this to the left composite.
Naturality of a moves the etale projection map next to eta_N. The tensor square
rho_d s(t_D) a = (a tensor a) t_C C(rho_e) follows from the monoidal comparison
of inverse images: after the localization identifications it is the monoidality
square of the canonical comparisonUpperStarCompUpperStarIso. Naturality of rho_d
moves s(c_F tensor identity) across rho_d. The defining transpose equation for
kappa_e gives eta_N r(kappa_e) rho_e = eta_F tensor identity. Naturality of t_C
then yields (C(eta_F) a_(eF) s(c_F) tensor a_B) t_C. Apply unit normalization at F.
The argument uses only adjunction identities and isomorphisms, and therefore also
applies to empty opens, zero sheaves, and the zero coefficient ring.
(blueprint: lem-sf-open-comparison-tensor-normalization). -/
private lemma openComparison_tensor_left_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _
      ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).inv.app
          (F ⊗ (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B) ≫
        openComparisonTensorLeft A j F B) ≫
      (proEtaleRestrictionTensorIso A j
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F))
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj B)).hom =
    (comparisonTensorIso A F
      ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj B)).hom ≫
      ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⊗ₘ
        (openComparisonRestrictionIso A j).hom.app B)  := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} A) U
  let D := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let e := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let r := Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j
  let d := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let s := openImmersionRestriction (ModuleCat.{u + 1} A) j
  let adj := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  let c := openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j
  let a := openComparisonRestrictionIso A j
  let N := F ⊗ r.obj B
  have hu := (openComparison_unit_normalization A j).2
  have htrans : adj.homEquiv _ _ (c.inv.app N ≫ openComparisonTensorLeft A j F B) =
      C.map ((Etale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} A) j).unit.app N) ≫
        a.hom.app (e.obj N) ≫ s.map (openComparisonTensorLeft A j F B) := by
    rw [Adjunction.homEquiv_unit]
    rw [← hu N]
    dsimp only [c, C, a, e, s]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [htrans]
  dsimp only [openComparisonTensorLeft]
  simp only [Functor.map_comp, Category.assoc]
  have hrho := transported_tensor_natural
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j
      (inferInstance : WeaklyEtale j)) (c.hom.app F) (𝟙 (D.obj B))
  change s.map (c.hom.app F ⊗ₘ 𝟙 (D.obj B)) ≫
      (proEtaleRestrictionTensorIso A j (d.obj (C.obj F)) (D.obj B)).hom =
    (proEtaleRestrictionTensorIso A j (D.obj (e.obj F)) (D.obj B)).hom ≫
      (s.map (c.hom.app F) ⊗ₘ s.map (𝟙 (D.obj B))) at hrho
  rw [hrho]
  have hn := a.hom.naturality (openComparisonEtaleKappa A j F B)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [reassoc_of% (openComparison_restriction_tensor_coherence A j (e.obj F) B)]
  simp only [← Functor.map_comp_assoc]
  let eta := (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit
  have hk : eta.app N ≫ r.map (openComparisonEtaleKappa A j F B) ≫
      (etaleRestrictionTensorIso A j (e.obj F) B).hom =
      eta.app F ⊗ₘ 𝟙 (r.obj B) := by
    have hk := Equiv.apply_symm_apply
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv
        N (e.obj F ⊗ B))
      ((eta.app F ⊗ₘ 𝟙 (r.obj B)) ≫
        (etaleRestrictionTensorIso A j (e.obj F) B).inv)
    change (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv
      _ _ (openComparisonEtaleKappa A j F B) = _ at hk
    rw [Adjunction.homEquiv_unit] at hk
    rw [reassoc_of% hk]
    simp only [Iso.inv_hom_id, Category.comp_id]
  change C.map (eta.app N) ≫ C.map _ ≫ _ = _
  rw [← C.map_comp_assoc, hk]
  dsimp only [comparisonTensorIso, asIso_hom]
  rw [← reassoc_of% (Functor.OplaxMonoidal.δ_natural C
    (eta.app F) (𝟙 (r.obj B)))]
  simp only [tensorHom_comp_tensorHom]
  rw [hu F, C.map_id, s.map_id]
  simp only [Category.id_comp]
  exact congrArg (fun h ↦ Functor.OplaxMonoidal.δ C F (r.obj B) ≫
    (adj.unit.app (C.obj F) ⊗ₘ h)) (Category.comp_id (a.hom.app B))

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
  constructor
  · intro F B
    let C := comparisonUpperStar (ModuleCat.{u + 1} A) U
    let D := comparisonUpperStar (ModuleCat.{u + 1} A) X
    let e := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
    let r := Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j
    let d := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
    let s := openImmersionRestriction (ModuleCat.{u + 1} A) j
    let adj := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
    let c := openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j
    let a := openComparisonRestrictionIso A j
    let N := F ⊗ r.obj B
    let q := (comparisonTensorIso A F (r.obj B)).hom ≫
      (𝟙 (C.obj F) ⊗ₘ a.hom.app B)
    apply (cancel_epi (c.inv.app N)).1
    apply (adj.homEquiv _ _).injective
    apply (cancel_mono (proEtaleRestrictionTensorIso A j
      (d.obj (C.obj F)) (D.obj B)).hom).1
    rw [openComparison_tensor_left_transpose A j F B]
    dsimp only [openComparisonTensorRight]
    dsimp only [c, N, r]
    simp only [Iso.inv_hom_id_app_assoc]
    dsimp only [adj]
    rw [Adjunction.homEquiv_naturality_left, openComparisonProEtaleKappa]
    dsimp only [Functor.comp_obj]
    rw [Equiv.apply_symm_apply]
    dsimp only [d, C, D]
    simp only [Category.assoc]
    simp [comparisonTensorIso, tensorHom_def']
  · intro F F' B B' f b
    dsimp only [openComparisonTensorLeft, comparisonTensorIso, asIso_hom]
    rw [← Functor.map_comp_assoc, etale_kappa_natural A j, Functor.map_comp]
    simp only [Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc]
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have hc := (openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) j).hom.naturality f
    dsimp only [Functor.comp_map] at hc
    rw [hc]



end AlgebraicGeometry.ProEtale
