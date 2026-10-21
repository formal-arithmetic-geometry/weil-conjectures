/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.SmoothPurityCompactProjectionData
import Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation
import Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation
import Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

/-! # Compact-support projection and arbitrary base change

Source: blueprint main-20261015, proof (2) of `det-sp-purity-bc-factors`;
Stacks 0E48 and 0GL1 (blueprint: lem-sp-compact-projection-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

-- The uncurried form of the mate calculation, following the private calculation in
-- RingedExchangeTensorCoherence; it applies to the original independent universes.
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_mate_coherence
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : T ⋙ F ⟶ (F.prod F) ⋙ U) (tG : T ⋙ G ⟶ (G.prod G) ⋙ V)
    (tH : U ⋙ H ⟶ (H.prod H) ⋙ W) (tK : V ⋙ K ⟶ (K.prod K) ⋙ W)
    (theta : G ⋙ K ≅ F ⋙ H)
    (hc : ∀ P Q : A,
      theta.hom.app (T.obj (P, Q)) ≫ H.map (tF.app (P, Q)) ≫
        tH.app (F.obj P, F.obj Q) =
      K.map (tG.app (P, Q)) ≫ tK.app (G.obj P, G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (theta.hom.app P) (theta.hom.app Q)))
    (E : B) (Q : A) :
    G.map (adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))) ≫
      (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).natTrans.app
        (U.obj (E, F.obj Q)) ≫
      S.map (tH.app (E, F.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (𝟙 (H.obj E)) (theta.inv.app Q))) =
    tG.app (R.obj E, Q) ≫
      V.map (CategoryTheory.Prod.mkHom
        ((mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).natTrans.app E)
        (𝟙 (G.obj Q))) ≫
      adj'.homEquiv _ _ (tK.app (S.obj (H.obj E), G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (adj'.counit.app (H.obj E))
          (𝟙 (K.obj (G.obj Q))))) := by
  let ex := (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).natTrans
  let pi := adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
    U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  have hex (Z : B) : K.map (ex.app Z) ≫ adj'.counit.app (H.obj Z) =
      theta.hom.app (R.obj Z) ≫ H.map (adj.counit.app Z) :=
    mateEquiv_counit adj adj' (TwoSquare.mk G F K H theta.hom) Z
  dsimp only [Functor.id_obj, Functor.comp_obj]
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm (G.map pi ≫ ex.app _ ≫ S.map _) = _
  rw [adj'.homEquiv_naturality_left_symm,
    adj'.homEquiv_naturality_right_symm]
  rw [adj'.homEquiv_counit, hex]
  simp only [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hn := theta.hom.naturality pi
  dsimp at hn
  dsimp only [Functor.id_obj] at *
  simp only [← Category.assoc]
  rw [hn]
  have hpi : F.map pi ≫ adj.counit.app (U.obj (E, F.obj Q)) =
      tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))) := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hpi, H.map_comp, Category.assoc]
  have htH := tH.naturality
    (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))
  have htK := tK.naturality
    (CategoryTheory.Prod.mkHom (ex.app E) (𝟙 (G.obj Q)))
  dsimp at htH htK
  rw [reassoc_of% htH, reassoc_of% htK]
  rw [reassoc_of% (hc (R.obj E) Q)]
  simp only [← W.map_comp]
  congr 2
  congr 1
  ext
  · simpa using (hex E).symm
  · simp


private def properProjection {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {B Y : Scheme.{u}} (p : B ⟶ Y) (M : Der (c.ring B)) (K : Der (c.ring Y)) :=
  (o.operation p).derivedAdjunction.homEquiv _ _
    ((o.tensorComparison p).comparison.hom.app ((o.operation p).right.obj M, K) ≫
      (o.tensor B).functor.map
        (CategoryTheory.Prod.mkHom ((o.operation p).derivedAdjunction.counit.app M)
          (𝟙 ((o.operation p).left.obj K))))

private def properExchange {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
    {B' B Y' Y : Scheme.{u}} {b : B' ⟶ B} {p' : B' ⟶ Y'} {p : B ⟶ Y}
    {v : Y' ⟶ Y} (s : CommSq b p' p v) :=
  (mateEquiv (o.operation p).derivedAdjunction (o.operation p').derivedAdjunction
    (TwoSquare.mk _ _ _ _ (o.square s).hom)).natTrans

private theorem proper_compatibility {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) {B' B Y' Y : Scheme.{u}}
    {b : B' ⟶ B} {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
    (s : CommSq b p' p v) (M : Der (c.ring B)) (K : Der (c.ring Y)) :
    (o.operation v).left.map (properProjection o p M K) ≫
        (properExchange o s).app
          ((o.tensor B).functor.obj (M, (o.operation p).left.obj K)) ≫
        (o.operation p').right.map
          ((o.tensorComparison b).comparison.hom.app (M, (o.operation p).left.obj K) ≫
            (o.tensor B').functor.map
              (CategoryTheory.Prod.mkHom (𝟙 ((o.operation b).left.obj M))
                ((o.square s).inv.app K))) =
      (o.tensorComparison v).comparison.hom.app ((o.operation p).right.obj M, K) ≫
        (o.tensor Y').functor.map (CategoryTheory.Prod.mkHom
          ((properExchange o s).app M) (𝟙 ((o.operation v).left.obj K))) ≫
        properProjection o p' ((o.operation b).left.obj M) ((o.operation v).left.obj K) := by
  exact tensor_mate_coherence (o.operation p).derivedAdjunction
    (o.operation p').derivedAdjunction
    (o.tensor Y).functor (o.tensor B).functor (o.tensor Y').functor (o.tensor B').functor
    (o.tensorComparison p).comparison.hom (o.tensorComparison v).comparison.hom
    (o.tensorComparison b).comparison.hom (o.tensorComparison p').comparison.hom
    (o.square s) (o.tensor_square s) M K

private theorem properProjection_naturality {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) {B Y : Scheme.{u}} (p : B ⟶ Y)
    {M N : Der (c.ring B)} {K L : Der (c.ring Y)} (r : M ⟶ N) (z : K ⟶ L) :
    (o.tensor Y).functor.map (CategoryTheory.Prod.mkHom ((o.operation p).right.map r) z) ≫
        properProjection o p N L =
      properProjection o p M K ≫ (o.operation p).right.map
        ((o.tensor B).functor.map
          (CategoryTheory.Prod.mkHom r ((o.operation p).left.map z))) := by
  let t := (o.operation p).derivedAdjunction.rightAdjointProjectionMap
    (o.curriedTensorComparison p).hom
  have H := (Functor.uncurry.map t).naturality (CategoryTheory.Prod.mkHom r z)
  simpa [t, Adjunction.rightAdjointProjectionMap_app_app, properProjection,
    Presentation.curriedTensorComparison, curryPostIso, curryPreIso,
    ← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id] using H

private theorem projection_factorization {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) (h : OpenComparisons o) {X B Y : Scheme.{u}}
    (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y)
    (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    o.projection h j p M K = properProjection o p ((o.shriek j).obj M) K ≫
      (o.operation p).right.map ((o.gammaIso h j).hom.app (M, (o.operation p).left.obj K)) := by
  simp [Presentation.projection,
    CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData,
    Adjunction.rightAdjointProjectionMap_app_app, Presentation.openProjectionIso,
    Presentation.curriedTensorComparison, curryPostIso, curryPreIso, properProjection]

private theorem exchange_factorization {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) (h : OpenComparisons o) {X' X B' B Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
    {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (so : IsPullback a j' j b) (sp : CommSq b p' p v) (M : Der (c.ring X)) :
    o.exchange h so sp M = (properExchange o sp).app ((o.shriek j).obj M) ≫
      (o.operation p').right.map ((o.betaIso h so).hom.app M) := by
  simp [Presentation.exchange, properExchange,
    CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData]

private theorem inverse_square {C : Type v} [Category.{w} C]
    {A B C' D : C} (p : A ⟶ B) (c : B ⟶ C') (b : A ⟶ D) (q : D ⟶ C')
    [IsIso p] [IsIso c] [IsIso q] (h : p ≫ c = b ≫ q) :
    inv c ≫ inv p ≫ b = inv q := by
  apply (cancel_mono q).1
  calc
    (inv c ≫ inv p ≫ b) ≫ q = inv c ≫ inv p ≫ (b ≫ q) := by simp
    _ = inv c ≫ inv p ≫ (p ≫ c) := by rw [h]
    _ = inv q ≫ q := by simp

section OpenCompatibility
variable {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
  (h : OpenComparisons o) {X' X B' B : Scheme.{u}}
  {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
  [IsOpenImmersion j] [IsOpenImmersion j'] (so : IsPullback a j' j b)

omit [IsOpenImmersion j] [IsOpenImmersion j'] in
private theorem inverse_tensor_square (M N : Der (c.ring B)) :
    (o.operation a).left.map ((o.tensorComparison j).comparison.inv.app (M, N)) ≫
        (o.square so.toCommSq).inv.app ((o.tensor B).functor.obj (M, N)) ≫
        (o.operation j').left.map ((o.tensorComparison b).comparison.hom.app (M, N)) =
      (o.tensorComparison a).comparison.hom.app
          ((o.operation j).left.obj M, (o.operation j).left.obj N) ≫
        (o.tensor X').functor.map (CategoryTheory.Prod.mkHom
          ((o.square so.toCommSq).inv.app M) ((o.square so.toCommSq).inv.app N)) ≫
        (o.tensorComparison j').comparison.inv.app
          ((o.operation b).left.obj M, (o.operation b).left.obj N) := by
  apply (cancel_epi ((o.square so.toCommSq).hom.app
    ((o.tensor B).functor.obj (M, N)) ≫
    (o.operation a).left.map ((o.tensorComparison j).comparison.hom.app (M, N)))).1
  simp only [Category.assoc]
  rw [reassoc_of% (o.tensor_square so.toCommSq M N)]
  simp only [← Functor.map_comp_assoc, prod_comp, Iso.hom_inv_id_app]
  simp

private theorem open_inverse_compatibility (M : Der (c.ring X))
    (N : Der (c.ring B)) :
    o.betaInv so ((o.tensor X).functor.obj (M, (o.operation j).left.obj N)) ≫
        (o.operation b).left.map (o.gammaInv j M N) ≫
        (o.tensorComparison b).comparison.hom.app ((o.shriek j).obj M, N) =
      (o.shriek j').map ((o.tensorComparison a).comparison.hom.app
        (M, (o.operation j).left.obj N)) ≫
        (o.shriek j').map ((o.tensor X').functor.map (CategoryTheory.Prod.mkHom
          (𝟙 ((o.operation a).left.obj M)) ((o.square so.toCommSq).inv.app N))) ≫
        o.gammaInv j' ((o.operation a).left.obj M) ((o.operation b).left.obj N) ≫
        (o.tensor B').functor.map (CategoryTheory.Prod.mkHom (o.betaInv so M)
          (𝟙 ((o.operation b).left.obj N))) := by
  have H := Adjunction.projectionMap_mate (o.openAdjunction j) (o.openAdjunction j')
    (o.operation j).left (o.operation j').left
    (o.curriedTensorComparison j).inv (o.curriedTensorComparison j').inv
    (o.curriedTensorComparison a).hom (o.curriedTensorComparison b).hom
    (o.square so.toCommSq).inv (o.square so.toCommSq).inv (o.betaInvNat so)
    (fun Z ↦ (unit_mateEquiv_symm (o.openAdjunction j) (o.openAdjunction j')
      (TwoSquare.mk _ _ _ _ (o.square so.toCommSq).inv) Z).symm)
    (by
      intro Z W
      simpa [Presentation.curriedTensorComparison, curryPostIso, curryPreIso,
        ← Functor.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id,
        Category.assoc] using inverse_tensor_square o so Z W)
    M N
  simpa [Presentation.curriedTensorComparison, curryPostIso, curryPreIso,
    Presentation.gammaInv, Presentation.gammaInvNat, Presentation.betaInv,
    ← Functor.map_comp, prod_comp] using H

private theorem gammaIso_inv {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : Der (c.ring U)) (N : Der (c.ring T)) :
    (o.gammaIso h j).inv.app (M, N) = o.gammaInv j M N := by
  simp [Presentation.gammaIso, Presentation.gammaInv]

private theorem open_compatibility (M : Der (c.ring X)) (N : Der (c.ring B)) :
    (o.operation b).left.map ((o.gammaIso h j).hom.app (M, N)) ≫
        (o.betaIso h so).hom.app
          ((o.tensor X).functor.obj (M, (o.operation j).left.obj N)) ≫
        (o.shriek j').map
          ((o.tensorComparison a).comparison.hom.app (M, (o.operation j).left.obj N) ≫
            (o.tensor X').functor.map (CategoryTheory.Prod.mkHom
              (𝟙 ((o.operation a).left.obj M)) ((o.square so.toCommSq).inv.app N))) =
      (o.tensorComparison b).comparison.hom.app ((o.shriek j).obj M, N) ≫
        (o.tensor B').functor.map (CategoryTheory.Prod.mkHom ((o.betaIso h so).hom.app M)
          (𝟙 ((o.operation b).left.obj N))) ≫
        (o.gammaIso h j').hom.app ((o.operation a).left.obj M, (o.operation b).left.obj N) := by
  have hg := gammaIso_inv o h j M N
  have hg' := gammaIso_inv o h j' ((o.operation a).left.obj M)
    ((o.operation b).left.obj N)
  have H := open_inverse_compatibility o so M N
  change (o.betaIso h so).inv.app _ ≫ (o.operation b).left.map (o.gammaInv j M N) ≫ _ =
    _ ≫ _ ≫ o.gammaInv j' _ _ ≫ (o.tensor B').functor.map
      (CategoryTheory.Prod.mkHom ((o.betaIso h so).inv.app M) (𝟙 _)) at H
  simp only [← hg, ← hg'] at H
  change (o.betaIso h so).inv.app
      ((o.tensor X).functor.obj (M, (o.operation j).left.obj N)) ≫
      (o.operation b).left.map ((o.gammaIso h j).inv.app (M, N)) ≫
      (o.tensorComparison b).comparison.hom.app ((o.shriek j).obj M, N) = _ at H
  apply (cancel_epi ((o.betaIso h so).inv.app
    ((o.tensor X).functor.obj (M, (o.operation j).left.obj N)) ≫
    (o.operation b).left.map ((o.gammaIso h j).inv.app (M, N)))).1
  simp only [Category.assoc]
  conv_rhs => rw [reassoc_of% H]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at H ⊢
  simp only [Functor.map_comp]
  rw [← (o.tensor B').functor.map_comp_assoc]
  simp only [prod_comp, Iso.inv_hom_id_app, Category.id_comp]
  have hid : CategoryTheory.Prod.mkHom
      (𝟙 (((o.operation a).left ⋙ o.shriek j').obj M))
      (𝟙 ((o.operation b).left.obj N)) =
      𝟙 ((((o.operation a).left ⋙ o.shriek j').obj M,
        (o.operation b).left.obj N)) := rfl
  rw [hid]
  erw [(o.tensor B').functor.map_id]
  rw [Category.id_comp]
  erw [← (o.operation b).left.map_comp_assoc, Iso.inv_hom_id_app,
    (o.operation b).left.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]


end OpenCompatibility

section FormalConsequences
variable {m : Mode} {c : Coefficients.{u} m} (o : Presentation c) (h : OpenComparisons o)
  {X B Y : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y)

private theorem projection_naturality
    {M N : Der (c.ring X)} {K L : Der (c.ring Y)} (r : M ⟶ N) (z : K ⟶ L) :
    (o.tensor Y).functor.map
        (CategoryTheory.Prod.mkHom (((o.shriek j) ⋙ (o.operation p).right).map r) z) ≫
      o.projection h j p N L =
    o.projection h j p M K ≫ ((o.shriek j) ⋙ (o.operation p).right).map
      ((o.tensor X).functor.map (CategoryTheory.Prod.mkHom r
        ((o.operation j).left.map ((o.operation p).left.map z)))) := by
  let t := CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData
    (o.shriek j) ((o.operation p).left ⋙ (o.operation j).left)
    (o.operation p).left (o.operation p).right (o.operation p).derivedAdjunction
    (Functor.curry.obj (o.tensor X).functor) (Functor.curry.obj (o.tensor B).functor)
    (Functor.curry.obj (o.tensor Y).functor)
    (o.curriedTensorComparison p) (o.openProjectionIso h j p)
  have H := (Functor.uncurry.map t).naturality (CategoryTheory.Prod.mkHom r z)
  change
    ((o.tensor Y).functor.map (CategoryTheory.Prod.mkHom
        (((o.shriek j) ⋙ (o.operation p).right).map r) (𝟙 K)) ≫
      (o.tensor Y).functor.map (CategoryTheory.Prod.mkHom (𝟙 _) z)) ≫
        o.projection h j p N L =
      o.projection h j p M K ≫
        (((o.shriek j) ⋙ (o.operation p).right).map
          ((o.tensor X).functor.map (CategoryTheory.Prod.mkHom r (𝟙 _))) ≫
        ((o.shriek j) ⋙ (o.operation p).right).map
          ((o.tensor X).functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
            ((o.operation j).left.map ((o.operation p).left.map z))))) at H
  simpa only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id] using H

end FormalConsequences

section DiagramConsequences
variable {m : Mode} {c : Coefficients.{u} m} (o : Presentation c) (h : OpenComparisons o)
  {X' X B' B Y' Y : Scheme.{u}}
  {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
  {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
  [IsOpenImmersion j] [IsOpenImmersion j']
  (so : IsPullback a j' j b) (sp : CommSq b p' p v)

private theorem diagramAssertion_of_forward
    (hf : ∀ (M : Der (c.ring X)) (K : Der (c.ring Y)),
      o.pulledProjection h (j := j) (p := p) (v := v) M K ≫ o.tensorTargetExchange h so sp M K =
        o.tensorExchange h so sp M K ≫
          o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K)) :
    DiagramAssertion o h so sp := by
  refine ⟨hf, ?_, ?_⟩
  · intro M N K L r z
    rw [hf, hf]
    let ex := CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
      (o.shriek j) (o.shriek j')
      (o.operation p).left (o.operation p).right (o.operation p).derivedAdjunction
      (o.operation p').left (o.operation p').right (o.operation p').derivedAdjunction
      (o.operation v).left (o.operation a).left (o.operation b).left
      (o.square sp) (o.betaIso h so)
    have hex := ex.naturality r
    change (o.operation v).left.map (((o.shriek j) ⋙ (o.operation p).right).map r) ≫
        o.exchange h so sp N = o.exchange h so sp M ≫
          ((o.shriek j') ⋙ (o.operation p').right).map ((o.operation a).left.map r) at hex
    have ht : (o.tensor Y').functor.map
        (CategoryTheory.Prod.mkHom
          ((o.operation v).left.map (((o.shriek j) ⋙ (o.operation p).right).map r))
          ((o.operation v).left.map z)) ≫ o.tensorExchange h so sp N L =
        o.tensorExchange h so sp M K ≫ (o.tensor Y').functor.map
          (CategoryTheory.Prod.mkHom
            (((o.shriek j') ⋙ (o.operation p').right).map ((o.operation a).left.map r))
            ((o.operation v).left.map z)) := by
      dsimp only [Presentation.tensorExchange]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext
      · exact hex
      · simp
    rw [← Category.assoc, ht, Category.assoc,
      projection_naturality o h j' p' ((o.operation a).left.map r)
        ((o.operation v).left.map z)]
    simp only [Category.assoc]
  · intro M K _ _ _ _
    let : IsIso (o.pulledProjection h (j := j) (p := p) (v := v) M K) := by
      dsimp only [Presentation.pulledProjection]
      infer_instance
    let : IsIso (o.tensorTargetExchange h so sp M K) := by
      dsimp only [Presentation.tensorTargetExchange]
      infer_instance
    have hi := inverse_square (o.pulledProjection h (j := j) (p := p) (v := v) M K)
      (o.tensorTargetExchange h so sp M K) (o.tensorExchange h so sp M K)
      (o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K))
      (hf M K)
    simpa [Presentation.pulledProjection, Presentation.tensorTargetExchange,
      IsIso.inv_comp, ← Functor.map_inv, Category.assoc] using hi

end DiagramConsequences

private theorem open_target_compatibility {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) (h : OpenComparisons o) {X' X B' B Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
    {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (so : IsPullback a j' j b) (sp : CommSq b p' p v)
    (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    (o.operation b).left.map
          ((o.gammaIso h j).hom.app (M, (o.operation p).left.obj K)) ≫
        (o.betaIso h so).hom.app
          ((o.tensor X).functor.obj (M, (o.operation j).left.obj ((o.operation p).left.obj K))) ≫
        (o.shriek j').map (o.targetIso so sp M K).hom =
      ((o.tensorComparison b).comparison.hom.app ((o.shriek j).obj M,
          (o.operation p).left.obj K) ≫
        (o.tensor B').functor.map (CategoryTheory.Prod.mkHom
          (𝟙 ((o.operation b).left.obj ((o.shriek j).obj M))) ((o.square sp).inv.app K))) ≫
        (o.tensor B').functor.map (CategoryTheory.Prod.mkHom
          ((o.betaIso h so).hom.app M) (𝟙 _)) ≫
        (o.gammaIso h j').hom.app
          ((o.operation a).left.obj M, (o.operation p').left.obj ((o.operation v).left.obj K)) := by
  have ho := open_compatibility o h so M ((o.operation p).left.obj K)
  have hn := (o.gammaIso h j').hom.naturality
    (CategoryTheory.Prod.mkHom (𝟙 ((o.operation a).left.obj M)) ((o.square sp).inv.app K))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hn
  rw [(o.shriek j').map_id] at hn
  dsimp only [Presentation.targetIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  change _ ≫ _ ≫ (o.shriek j').map
    ((o.tensorComparison a).comparison.hom.app (M, (o.operation j).left.obj
        ((o.operation p).left.obj K)) ≫
      (o.tensor X').functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
        ((o.square so.toCommSq).inv.app ((o.operation p).left.obj K) ≫
          (o.operation j').left.map ((o.square sp).inv.app K)))) = _
  have hsplit : (o.tensor X').functor.map (CategoryTheory.Prod.mkHom
      (𝟙 ((o.operation a).left.obj M))
      ((o.square so.toCommSq).inv.app ((o.operation p).left.obj K) ≫
        (o.operation j').left.map ((o.square sp).inv.app K))) =
      (o.tensor X').functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
        ((o.square so.toCommSq).inv.app ((o.operation p).left.obj K))) ≫
      (o.tensor X').functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
        ((o.operation j').left.map ((o.square sp).inv.app K))) := by
    rw [← Functor.map_comp]
    congr 1
  rw [hsplit]
  simp only [Functor.map_comp, Category.assoc] at ho ⊢
  rw [reassoc_of% ho]
  dsimp only [Functor.comp_obj] at hn ⊢
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc, prod_comp,
    Category.id_comp, Category.comp_id]

private theorem forward_compatibility {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) (h : OpenComparisons o) {X' X B' B Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {j' : X' ⟶ B'} {j : X ⟶ B} {b : B' ⟶ B}
    {p' : B' ⟶ Y'} {p : B ⟶ Y} {v : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (so : IsPullback a j' j b) (sp : CommSq b p' p v)
    (M : Der (c.ring X)) (K : Der (c.ring Y)) :
    o.pulledProjection h (j := j) (p := p) (v := v) M K ≫
        o.tensorTargetExchange h so sp M K =
      o.tensorExchange h so sp M K ≫
        o.projection h j' p' ((o.operation a).left.obj M) ((o.operation v).left.obj K) := by
  apply (cancel_epi ((o.tensorComparison v).comparison.hom.app
    (((o.shriek j) ⋙ (o.operation p).right).obj M, K))).1
  simp only [Presentation.pulledProjection, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [projection_factorization]
  simp only [Functor.map_comp, Category.assoc, Presentation.tensorTargetExchange,
    exchange_factorization]
  have hn := (properExchange o sp).naturality
    ((o.gammaIso h j).hom.app (M, (o.operation p).left.obj K))
  dsimp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hn
  rw [reassoc_of% hn]
  dsimp only [CategoryTheory.Functor.comp_map]
  rw [← (o.operation p').right.map_comp_assoc,
    ← (o.operation p').right.map_comp]
  simp only [Category.assoc]
  rw [open_target_compatibility o h so sp M K]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (o.operation p').right.map_comp_assoc,
    reassoc_of% (proper_compatibility o sp ((o.shriek j).obj M) K)]
  have hp :
      (o.tensor Y').functor.map (CategoryTheory.Prod.mkHom
        ((o.operation p').right.map ((o.betaIso h so).hom.app M)) (𝟙 _)) ≫
        properProjection o p' ((o.shriek j').obj ((o.operation a).left.obj M))
          ((o.operation v).left.obj K) =
      properProjection o p' ((o.operation b).left.obj ((o.shriek j).obj M))
          ((o.operation v).left.obj K) ≫
        (o.operation p').right.map ((o.tensor B').functor.map
          (CategoryTheory.Prod.mkHom ((o.betaIso h so).hom.app M) (𝟙 _))) := by
    have hn := properProjection_naturality o p'
      ((o.betaIso h so).hom.app M) (𝟙 ((o.operation v).left.obj K))
    rw [(o.operation p').left.map_id] at hn
    exact hn
  dsimp only [Functor.comp_obj] at hp ⊢
  rw [← reassoc_of% hp]
  rw [projection_factorization]
  simp only [Presentation.tensorExchange, exchange_factorization,
    ← (o.tensor Y').functor.map_comp_assoc, prod_comp, Category.comp_id]

/-- Compact-support projection commutes with arbitrary base change, both for a finite
ell-primary commutative ring and for the ordinary varying-coefficient tower category.
Existence and independence of canonical presentations are both explicit:
their functors are fixed by section maps, adjunctions and K-flat localization.
The ring systems and their section-preserving equivalences are conclusions, not additional
hypotheses. `DiagramAssertion` contains the forward equation, simultaneous naturality,
and the inverse equation under precisely the four stated isomorphism assumptions.
Source: blueprint main-20261015, det-sp-purity-bc-factors proof (2); Stacks 0E48 and 0GL1
(blueprint: lem-sp-compact-projection-base-change).

Proof plan, following the five DAG steps:
1. For finite rings use the constant ring sheaf. For towers use the vertical diagram
site, its actual varying ring system and the normalized equivalence with
`spCoefficientTowers` (det-sp-coefficient-towers-abelian and
lem-weil-pbc-diagram-site-realization). Module inverse image is exact levelwise;
sectionwise direct image has the stated derived adjunction. K-flat totalization gives
the tensor and its canonical comparisons (lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
2. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the proper square and the
input j_!M. Its mate and counit-transpose maps are precisely the definitions above.
3. Lem-sf-open-tensor-normalization identifies the two open composites after restriction
with the same inverse-image tensor map. On flat K-flat representatives they split the
same tensor factors in each bidegree, preserving total differentials. Full faithfulness
of open extension proves equality on the diagram site, without detecting equality by
separate level evaluations.
4. Expand the compactification composites. Use naturality of proper exchange at the
open tensor map, then step 3, step 2, and naturality of the proper projection map in its
first input (lem-weil-pbc-ringed-projection-mate-exact). This gives P;C = B;Q and its
simultaneous naturality. No proper-exchange or projection invertibility is used.
5. Under the four isomorphism assumptions compose P;C = B;Q with inverses to obtain
C^{-1};P^{-1};B = Q^{-1}. Expand the two tensor/composition identifications, yielding
exactly the final equation of DiagramAssertion. -/
theorem compact_projection_base_change (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p) :
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
      (_ha : ∃ r : ℕ, 1 ≤ r ∧ (l ^ r : A) = 0),
      (∃ o : Presentation (finiteCoefficients A), Nonempty (OpenComparisons o)) ∧
        ∀ (o : Presentation (finiteCoefficients A)) (h : OpenComparisons o),
          GeometricAssertion D o h) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
      (∃ c : Coefficients.{u} .systems, TowerCoefficients l E c ∧
        ∃ o : Presentation c, Nonempty (OpenComparisons o)) ∧
      ∀ (c : Coefficients.{u} .systems), TowerCoefficients l E c →
        ∀ (o : Presentation c) (h : OpenComparisons o), GeometricAssertion D o h) := by
  have hg {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
      (h : OpenComparisons o) : GeometricAssertion D o h := by
    intro X Y Y' _ _ _ _ _ _ _ _ _ _ _ _ f v _ _ _ _ _ q X' B' a f' b p' j' _
      sx sb sj hf'
    exact diagramAssertion_of_forward o h sj sb.toCommSq
      (forward_compatibility o h sj sb.toCommSq)
  constructor
  · intro A _ _ ha
    exact ⟨finite_presentation_exists A, fun o h ↦ hg o h⟩
  · intro E _ _ _
    exact ⟨tower_presentation_exists l E, fun c hc o h ↦ hg o h⟩

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
