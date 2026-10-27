/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
import all Sheaf.Paper.FiniteSmoothLevelOfOrientation
import all Sheaf.Paper.EtaleScalarPullbackUnitCoherence
import Sheaf.Paper.ExceptionalCoefficientLeftUnitCoherence

/-! # The unit coordinate of finite purity-source reduction

Source: finite smooth coefficient balancing, compatibility (3).
(blueprint: lem-pur-finite-source-unit-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  Functor.rightAdjoint Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

private theorem transportScalarSource
    {C D C' D' B E B' E' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category B] [Category E] [Category B'] [Category E']
    (F : C ⥤ C') (R : C' ⥤ C) (adj : F ⊣ R)
    (G : B ⥤ B') (R' : B' ⥤ B) (adj' : G ⊣ R')
    (P : C ⥤ D) (Q : C' ⥤ D') (H : D ⥤ D')
    (P' : B ⥤ E) (Q' : B' ⥤ E') (H' : E ⥤ E')
    (S : C ⥤ B) (T : C' ⥤ B') (U : D ⥤ E) (V : D' ⥤ E')
    (q : P ⋙ H ≅ F ⋙ Q) (q' : P' ⋙ H' ≅ G ⋙ Q')
    (s : F ⋙ T ≅ S ⋙ G) (t : H ⋙ V ≅ U ⋙ H')
    (alpha : P ⋙ U ⟶ S ⋙ P')
    (K₀ : C) (K : C') [IsIso (adj.counit.app K)] (e : F.obj K₀ ≅ K) :
    let m := adj'.homEquiv _ _
      (s.inv.app (R.obj K) ≫ T.map (adj.counit.app K))
    V.map (q.hom.app K₀ ≫ Q.map e.hom) ≫
        (V.map (Q.map (inv (adj.counit.app K)) ≫ q.inv.app (R.obj K)) ≫
          t.hom.app (P.obj (R.obj K)) ≫
          H'.map (alpha.app (R.obj K) ≫ P'.map m) ≫
          q'.hom.app (R'.obj (T.obj K)) ≫ Q'.map (adj'.counit.app (T.obj K))) ≫
        Q'.map (T.map e.inv ≫ s.hom.app K₀) =
      t.hom.app (P.obj K₀) ≫ H'.map (alpha.app K₀) ≫ q'.hom.app (S.obj K₀) := by
  dsimp only
  let i : K₀ ⟶ R.obj K := adj.unit.app K₀ ≫ R.map e.hom
  have hi : e.hom ≫ inv (adj.counit.app K) = F.map i := by
    apply (cancel_mono (adj.counit.app K)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      i, F.map_comp]
    erw [show F.map (R.map e.hom) ≫ adj.counit.app K =
      adj.counit.app (F.obj K₀) ≫ e.hom from adj.counit.naturality e.hom,
      ← Category.assoc, adj.left_triangle_components]
    simp only [Category.id_comp]
  have hm : G.map (adj'.homEquiv _ _
      (s.inv.app (R.obj K) ≫ T.map (adj.counit.app K))) ≫
      adj'.counit.app (T.obj K) =
        s.inv.app (R.obj K) ≫ T.map (adj.counit.app K) := by
    erw [← adj'.homEquiv_counit]
    exact (adj'.homEquiv _ _).symm_apply_apply _
  have hq : (q.hom.app K₀ ≫ Q.map e.hom) ≫
      (Q.map (inv (adj.counit.app K)) ≫ q.inv.app (R.obj K)) =
        H.map (P.map i) := by
    erw [Category.assoc, ← Q.map_comp_assoc, hi]
    erw [q.inv.naturality]
    simp only [Functor.comp_map, ← Category.assoc,
      q.hom_inv_id_app, Category.id_comp]
  simp only [H'.map_comp, Q'.map_comp, Category.assoc]
  erw [← V.map_comp_assoc, hq]
  erw [reassoc_of% (t.hom.naturality (P.map i))]
  erw [← H'.map_comp_assoc, alpha.naturality i]
  simp only [Functor.comp_map, H'.map_comp, Category.assoc]
  erw [reassoc_of% (q'.hom.naturality
    (adj'.homEquiv _ _ (s.inv.app (R.obj K) ≫ T.map (adj.counit.app K))))]
  erw [← Q'.map_comp_assoc, hm]
  erw [reassoc_of% (q'.hom.naturality (S.map i))]
  have hend : G.map (S.map i) ≫
      s.inv.app (R.obj K) ≫ T.map (adj.counit.app K) ≫
        T.map e.inv ≫ s.hom.app K₀ = 𝟙 _ := by
    erw [reassoc_of% (s.inv.naturality i)]
    erw [← T.map_comp_assoc, ← T.map_comp_assoc]
    have hic : F.map i ≫ adj.counit.app K ≫ e.inv = 𝟙 _ := by
      erw [← hi, Category.assoc, IsIso.inv_hom_id_assoc, e.hom_inv_id]
    simp only [Category.assoc]
    erw [hic, T.map_id, Category.id_comp, s.inv_hom_id_app]
    rfl
  simp only [Category.assoc, ← Q'.map_comp]
  erw [hend, Q'.map_id, Category.comp_id]


private def tensorBalancing
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (P : C ⥤ D) (P' : B ⥤ E) (S : C ⥤ B) (U : D ⥤ E)
    (delta : Functor.uncurry.obj (curriedTensor D) ⋙ U ≅
      U.prod U ⋙ Functor.uncurry.obj (curriedTensor E))
    (c : S ⋙ P' ≅ P ⋙ U) (L : D) (M : E) (e : U.obj L ≅ M) :
    (P ⋙ (curriedTensor D).flip.obj L) ⋙ U ≅
      S ⋙ (P' ⋙ (curriedTensor E).flip.obj M) :=
  NatIso.ofComponents (fun K ↦ delta.app (P.obj K, L) ≪≫
    ((curriedTensor E).mapIso (c.app K).symm).app _ ≪≫
      ((curriedTensor E).obj (P'.obj (S.obj K))).mapIso e) (by
    intro K K' a
    have hd := Etale.tensor_naturality_left U delta (P.map a) L
    have hc := c.inv.naturality a
    dsimp only [Functor.comp_map] at hc
    dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.comp_map, Functor.flip_obj_map, curriedTensor_obj_map,
      curriedTensor_map_app, Iso.symm_hom]
    simp only [Category.assoc]
    change U.map (P.map a ▷ L) ≫ delta.hom.app (P.obj K', L) ≫
      c.inv.app K' ▷ U.obj L ≫ P'.obj (S.obj K') ◁ e.hom =
        delta.hom.app (P.obj K, L) ≫ c.inv.app K ▷ U.obj L ≫
          P'.obj (S.obj K) ◁ e.hom ≫ P'.map (S.map a) ▷ M
    erw [reassoc_of% hd, ← comp_whiskerRight_assoc, hc,
      comp_whiskerRight_assoc, whisker_exchange])

private theorem tensorBalancing_unit
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory B] [MonoidalCategory E]
    (P : C ⥤ D) (P' : B ⥤ E) (S : C ⥤ B) (U : D ⥤ E)
    (delta : Functor.uncurry.obj (curriedTensor D) ⋙ U ≅
      U.prod U ⋙ Functor.uncurry.obj (curriedTensor E))
    (c : S ⋙ P' ≅ P ⋙ U)
    (uP : P.obj (𝟙_ C) ≅ 𝟙_ D) (uP' : P'.obj (𝟙_ B) ≅ 𝟙_ E)
    (uS : S.obj (𝟙_ C) ≅ 𝟙_ B) (uU : U.obj (𝟙_ D) ≅ 𝟙_ E)
    (hu : ∀ L, delta.hom.app (𝟙_ D, L) ≫ uU.hom ▷ U.obj L ≫
      (λ_ (U.obj L)).hom = U.map (λ_ L).hom)
    (hc : c.hom.app (𝟙_ C) ≫ U.map uP.hom ≫ uU.hom =
      P'.map uS.hom ≫ uP'.hom)
    (L : D) (M : E) (e : U.obj L ≅ M) :
    U.map ((λ_ L).inv ≫ (uP.inv ▷ L)) ≫
      (tensorBalancing P P' S U delta c L M e).hom.app (𝟙_ C) ≫
      (P'.map uS.hom ▷ M) ≫ (uP'.hom ▷ M) ≫ (λ_ M).hom = e.hom := by
  have hc' : c.inv.app (𝟙_ C) ≫ P'.map uS.hom ≫ uP'.hom =
      U.map uP.hom ≫ uU.hom := by
    erw [← hc, c.inv_hom_id_app_assoc]
  have hd := Etale.tensor_naturality_left U delta uP.inv L
  simp only [tensorBalancing, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app,
    curriedTensor_obj_map, U.map_comp, Category.assoc]
  change U.map (λ_ L).inv ≫ U.map (uP.inv ▷ L) ≫
    delta.hom.app (P.obj (𝟙_ C), L) ≫ c.inv.app (𝟙_ C) ▷ U.obj L ≫
      P'.obj (S.obj (𝟙_ C)) ◁ e.hom ≫ P'.map uS.hom ▷ M ≫
        uP'.hom ▷ M ≫ (λ_ M).hom = e.hom
  erw [reassoc_of% hd]
  erw [whisker_exchange_assoc, whisker_exchange_assoc]
  erw [← comp_whiskerRight_assoc (P'.map uS.hom),
    ← comp_whiskerRight_assoc (c.inv.app (𝟙_ C)), hc']
  erw [comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp only [← U.map_comp, uP.inv_hom_id, U.map_id, id_whiskerRight, Category.id_comp]
  erw [leftUnitor_naturality, reassoc_of% (hu L), ← U.map_comp_assoc, Iso.inv_hom_id,
    U.map_id, Category.id_comp]

private theorem finishSourceTransport
    {B E B' E' : Type*}
    [Category B] [Category E] [Category B'] [Category E']
    (F : B ⥤ B') (P : B ⥤ E) (Q : B' ⥤ E') (H : E ⥤ E')
    (q : P ⋙ H ≅ F ⋙ Q)
    (K₀ K₁ : B) (K' T₀ : B') (Z : E') (M : E)
    (e : F.obj K₁ ≅ K') (a : T₀ ⟶ F.obj K₀) (b : K₀ ⟶ K₁)
    (u : P.obj K₁ ⟶ M) (z : Z ⟶ Q.obj T₀) (w : Z ⟶ H.obj (P.obj K₀))
    (h : z ≫ Q.map a = w ≫ q.hom.app K₀) :
    z ≫ Q.map (a ≫ F.map b ≫ e.hom) ≫
      (Q.map e.inv ≫ q.inv.app K₁ ≫ H.map u) =
        w ≫ H.map (P.map b ≫ u) := by
  simp only [Q.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc e.hom, e.hom_inv_id, Q.map_id, Category.id_comp]
  rw [reassoc_of% h]
  erw [reassoc_of% (q.inv.naturality b)]
  rw [reassoc_of% (q.hom_inv_id_app K₀)]
  simp only [H.map_comp]

private theorem finishUnitSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (H : C ⥤ D) (V : D ⥤ F) (U : C ⥤ E) (H' : E ⥤ F)
    (t : H ⋙ V ≅ U ⋙ H') {K L : C} {M : E} {A' : D} {B' : F}
    (ua : K ≅ L) (sa : A' ≅ H.obj L) (sb : B' ≅ H'.obj M)
    (c : H.obj K ⟶ A') (v : V.obj A' ⟶ B')
    (z : U.obj K ⟶ M) (e : U.obj L ⟶ M)
    (ha : sa.inv = H.map ua.inv ≫ c)
    (hv : V.map c ≫ v ≫ sb.hom = t.hom.app K ≫ H'.map z)
    (hz : U.map ua.inv ≫ z = e) :
    V.map sa.inv ≫ v = (t.hom.app L ≫ H'.map e) ≫ sb.inv := by
  apply (cancel_mono sb.hom).mp
  simp only [Category.assoc, sb.inv_hom_id, Category.comp_id]
  rw [ha, V.map_comp, Category.assoc, hv]
  erw [reassoc_of% (t.hom.naturality ua.inv)]
  change t.hom.app L ≫ H'.map (U.map ua.inv) ≫ H'.map z =
    t.hom.app L ≫ H'.map e
  rw [← H'.map_comp, hz]

private theorem comparisonCounitUnitIsIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (Y : Scheme.{u}) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app
      (𝟙_ (proCategory A Y))) := by
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
  let e : (comparison A Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory A Y) :=
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y
  have hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y (𝟙_ _) (ordinaryUnitCtf A Y).1.1.1
  have hmu : IsIso ((comparison A Y).map (adj.unit.app (𝟙_ _))) := inferInstance
  have hcu : IsIso (adj.counit.app ((comparison A Y).obj (𝟙_ _))) :=
    IsIso.of_isIso_fac_left (adj.left_triangle_components (𝟙_ _))
  exact (NatTrans.isIso_app_iff_of_iso adj.counit e).mp hcu

/-- The actual source balancing at the coefficient unit is the root comparison.
This is an equality of the specified maps, independent of a purity orientation.

Source: finite smooth reduction, scalar/pullback/twist balancing, compatibility (3).
(blueprint: lem-pur-finite-source-unit-reduction)

Proof: expand proLambda through its origin counits and the site/scalar mate. The
comparison unit is invertible, so its triangle identities cancel the origin round
trips. Naturality of the site/scalar comparison moves the fixed comparison-unit
maps through it. In ordinary coordinates, scalar/pullback balancing carries the
pullback of the unit to the unit: its adjoint is coefficient multiplication.
The scalar tensor comparison then commutes with the left unitor, as both send
(a tensor x) tensor b to ab times the reduced root tensor. What remains is precisely
CoefficientLineComparison.tensorPower, followed by its site/scalar mate, hence
proTwistMap. All maps are induced by these formulas on K-flat models; their universal
counits extend the equality to the derived category. The zero-fold root tensor uses
the same coefficient-unit multiplication, and the equal-level case is included.
-/
theorem finitePuritySourceUnitReduction
    (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) :
    (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) X).map
        (unitSource ell b f d).inv ≫
      proLambda f d r (𝟙_ _) ≫
      (finiteProSource ell (a + 1) f d).map (unitReduction Y ell b a hab).hom =
        proTwistMap d r ≫ (unitSource ell a f d).inv := by
  let A := coefficient.{u} ell (b + 1)
  let B := coefficient.{u} ell (a + 1)
  let phi := FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)
  let LA := line A (ell ^ (b + 1)) (CharP.cast_eq_zero _ _) X d
  let LB := line B (ell ^ (a + 1)) (CharP.cast_eq_zero _ _) X d
  let PA := puritySource A f LA
  let PB := puritySource B f LB
  let QA := proSource A f LA
  let QB := proSource B f LB
  let HA := comparison A X
  let HB := comparison B X
  let V := proScalar phi X
  let T := proScalar phi Y
  let U := ordinaryScalar phi X
  let S := ordinaryScalar phi Y
  let qA : PA ⋙ HA ≅ comparison A Y ⋙ QA := sourceNatIso A f LA
  let qB : PB ⋙ HB ≅ comparison B Y ⋙ QB := sourceNatIso B f LB
  let s : comparison A Y ⋙ T ≅ S ⋙ comparison B Y :=
    ProEtale.pbcComparisonReduction Y phi
  let t : HA ⋙ V ≅ U ⋙ HB := ProEtale.pbcComparisonReduction X phi
  let eA : (comparison A Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory A Y) :=
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y
  let eB : (comparison B Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory B Y) :=
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso B Y
  let uA : PA.obj (𝟙_ _) ≅ LA := ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app LA ≪≫
      Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X LA
  let uB : PB.obj (𝟙_ _) ≅ LB := ((Etale.derivedTensor (ModuleCat.{u + 1} B) X).mapIso
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f)).app LB ≪≫
      Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} B) X LB
  let delta : PA ⋙ U ≅ S ⋙ PB := tensorBalancing (Etale.ordinaryFinitePullback A f)
    (Etale.ordinaryFinitePullback B f) S U (Etale.ExceptionalCoefficients.tensorIso phi X)
    (Etale.scalarPullbackIso phi f) LA LB (r.tensorPower d)
  have hdelta (K : Etale.DerivedCategoryModule A Y) :
      (delta.app K).hom = (pullbackTwistComparison f d r K).hom := rfl
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
  have hc : IsIso (adj.counit.app (𝟙_ _)) := comparisonCounitUnitIsIso A Y
  have ht := transportScalarSource (comparison A Y) (origin A Y) adj
    (comparison B Y) (origin B Y)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) Y)
    PA QA HA PB QB HB S T U V qA qB s t delta.hom (𝟙_ _) (𝟙_ _) eA
  have hqA (K : Etale.DerivedCategoryModule A Y) :
      qA.app K = sourceAtOriginIso A f LA K := sourceNatIso_app A f LA K
  have hqB (K : Etale.DerivedCategoryModule B Y) :
      qB.app K = sourceAtOriginIso B f LB K := sourceNatIso_app B f LB K
  have hc0 : IsIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} (FiniteReduction.Coeff.{u} ell (b + 1))) Y).counit.app
        (𝟙_ (proCategory (FiniteReduction.Coeff.{u} ell (b + 1)) Y))) := hc
  have hlambda : proLambda f d r (𝟙_ _) =
      V.map (QA.map (inv (adj.counit.app (𝟙_ _))) ≫
        qA.inv.app ((origin A Y).obj (𝟙_ _))) ≫
      t.hom.app (PA.obj ((origin A Y).obj (𝟙_ _))) ≫
      HB.map (delta.hom.app ((origin A Y).obj (𝟙_ _)) ≫
        PB.map (originReductionMap phi Y (𝟙_ _))) ≫
      qB.hom.app ((origin B Y).obj (T.obj (𝟙_ _))) ≫
      QB.map ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) Y).counit.app
        (T.obj (𝟙_ _))) := by
    simp only [proLambda, sourceToOrigin, sourceFromOrigin, originInverse,
      dif_pos hc0, ← Iso.app_hom, ← Iso.app_inv, hqA, hqB, hdelta]
    rfl
  have htrans :
      V.map (qA.hom.app (𝟙_ _) ≫ QA.map eA.hom) ≫
        proLambda f d r (𝟙_ _) ≫ QB.map (T.map eA.inv ≫ s.hom.app (𝟙_ _)) =
      t.hom.app (PA.obj (𝟙_ _)) ≫ HB.map (delta.hom.app (𝟙_ _)) ≫
        qB.hom.app (S.obj (𝟙_ _)) := by
    rw [hlambda]
    exact ht
  have hunit : U.map uA.inv ≫ delta.hom.app (𝟙_ _) ≫
      PB.map (Etale.ExceptionalCoefficients.unitIso phi Y).hom ≫ uB.hom =
        (r.tensorPower d).hom := by
    exact tensorBalancing_unit (Etale.ordinaryFinitePullback A f)
      (Etale.ordinaryFinitePullback B f) S U
      (Etale.ExceptionalCoefficients.tensorIso phi X) (Etale.scalarPullbackIso phi f)
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f)
      (Etale.ExceptionalCoefficients.unitIso phi Y)
      (Etale.ExceptionalCoefficients.unitIso phi X)
      (Etale.ExceptionalCoefficients.tensorIso_left_unit phi X)
      (Etale.etaleScalarPullback_unit phi f) LA LB (r.tensorPower d)
  have hsa : (unitSource ell b f d).inv =
      HA.map uA.inv ≫ qA.hom.app (𝟙_ _) ≫ QA.map eA.hom := by
    rw [← Iso.app_hom, hqA]
    simp only [unitSource, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc]
    rfl
  have hsb : (unitSource ell a f d).hom =
      QB.map eB.inv ≫ qB.inv.app (𝟙_ _) ≫ HB.map uB.hom := by
    rw [← Iso.app_inv, hqB]
    unfold unitSource
    rfl
  have hr : (unitReduction Y ell b a hab).hom =
      T.map eA.inv ≫ s.hom.app (𝟙_ _) ≫
        (comparison B Y).map (Etale.ExceptionalCoefficients.unitIso phi Y).hom ≫
        eB.hom := rfl
  have hcore : V.map (qA.hom.app (𝟙_ _) ≫ QA.map eA.hom) ≫
      proLambda f d r (𝟙_ _) ≫ QB.map (unitReduction Y ell b a hab).hom ≫
        (unitSource ell a f d).hom =
      t.hom.app (PA.obj (𝟙_ _)) ≫
        HB.map (delta.hom.app (𝟙_ _) ≫
          PB.map (Etale.ExceptionalCoefficients.unitIso phi Y).hom ≫ uB.hom) := by
    rw [hsb, hr]
    have hh := finishSourceTransport (comparison B Y) PB QB HB qB
      (S.obj (𝟙_ _)) (𝟙_ _) (𝟙_ _) (T.obj (𝟙_ _)) _ _ eB
      (T.map eA.inv ≫ s.hom.app (𝟙_ _))
      (Etale.ExceptionalCoefficients.unitIso phi Y).hom uB.hom
      (V.map (qA.hom.app (𝟙_ _) ≫ QA.map eA.hom) ≫ proLambda f d r (𝟙_ _))
      (t.hom.app (PA.obj (𝟙_ _)) ≫ HB.map (delta.hom.app (𝟙_ _)))
      (by simpa only [Category.assoc] using htrans)
    simpa only [Category.assoc, HB.map_comp] using hh
  have hfinal := finishUnitSquare HA V U HB t
    (K := PA.obj (𝟙_ _)) (L := LA) (M := LB)
    (A' := QA.obj (𝟙_ _)) (B' := QB.obj (𝟙_ _)) uA (unitSource ell b f d)
    (unitSource ell a f d) (qA.hom.app (𝟙_ _) ≫ QA.map eA.hom)
    (proLambda f d r (𝟙_ _) ≫ QB.map (unitReduction Y ell b a hab).hom)
    (delta.hom.app (𝟙_ _) ≫
      PB.map (Etale.ExceptionalCoefficients.unitIso phi Y).hom ≫ uB.hom)
    (r.tensorPower d).hom hsa (by simpa only [Category.assoc] using hcore) hunit
  simpa only [V, QB, B, LB, t, HB, LA, A, phi, proTwistMap, finiteProSource,
    Category.assoc] using hfinal


end AlgebraicGeometry.Scheme.PurityIntegralTower
