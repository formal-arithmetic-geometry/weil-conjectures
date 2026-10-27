/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction
import all Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare
import all Sheaf.SixFunctors.OpenReconstructionEffectivity
import all Sheaf.SixFunctors.TensorAdjunctionReductionSquares

/-! # Ordinary coefficient compatibility for compactification exchange

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp ringedSquare Compositors.square

private theorem mate_pasting_square
    {AZ AV AW AU BZ BV BW BU : Type*}
    [Category AZ] [Category AV] [Category AW] [Category AU]
    [Category BZ] [Category BV] [Category BW] [Category BU]
    {P : AZ ⥤ AV} {Q : AV ⥤ AZ} {P' : AW ⥤ AU} {Q' : AU ⥤ AW}
    {F : BZ ⥤ BV} {G : BV ⥤ BZ} {F' : BW ⥤ BU} {G' : BU ⥤ BW}
    {RZ : AZ ⥤ BZ} {RV : AV ⥤ BV} {RW : AW ⥤ BW} {RU : AU ⥤ BU}
    {I : AZ ⥤ AW} {K : AV ⥤ AU} {J : BZ ⥤ BW} {H : BV ⥤ BU}
    (a : P ⊣ Q) (b : P' ⊣ Q') (c : F ⊣ G) (d : F' ⊣ G')
    (δp : P ⋙ RV ≅ RZ ⋙ F) (δr : P' ⋙ RU ≅ RW ⋙ F')
    (δi : I ⋙ RW ⟶ RZ ⋙ J) (δk : K ⋙ RU ⟶ RV ⋙ H)
    (θr : TwoSquare I P P' K) (θs : TwoSquare J F F' H)
    (h : (Functor.whiskerLeft I δr.hom ≫ Functor.whiskerRight δi F') ≫
        Functor.whiskerLeft RZ θs.natTrans =
      Functor.whiskerRight θr.natTrans RU ≫
        (Functor.whiskerLeft P δk ≫ Functor.whiskerRight δp.hom H))
    (L : AV) :
    δi.app (Q.obj L) ≫ J.map ((mateEquiv a c δp.inv).natTrans.app L) ≫
        (mateEquiv c d θs).natTrans.app (RV.obj L) =
      RW.map ((mateEquiv a b θr).natTrans.app L) ≫
        (mateEquiv b d δr.inv).natTrans.app (K.obj L) ≫ G'.map (δk.app L) := by
  apply (d.homEquiv _ _).symm.injective
  change F'.map _ ≫ d.counit.app _ = F'.map _ ≫ d.counit.app _
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hε := d.counit.naturality (δk.app L)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hε
  erw [hε, mateEquiv_counit c d θs (RV.obj L)]
  have hn := θs.natTrans.naturality ((mateEquiv a c δp.inv).natTrans.app L)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← H.map_comp, mateEquiv_counit a c δp.inv L]
  erw [reassoc_of% (mateEquiv_counit b d δr.inv (K.obj L))]
  have hn' := δr.inv.naturality ((mateEquiv a b θr).natTrans.app L)
  dsimp only [Functor.comp_map] at hn'
  erw [reassoc_of% hn', ← RU.map_comp_assoc, mateEquiv_counit a b θr L]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn'' := δk.naturality (a.counit.app L)
  dsimp only [Functor.comp_map] at hn''
  erw [hn'']
  apply (cancel_epi (δr.hom.app (I.obj (Q.obj L)))).1
  simp only [Iso.hom_inv_id_app_assoc]
  have h₀ := whisker_square_app δi δr.hom δp.hom δk θr.natTrans θs.natTrans h
    (Q.obj L)
  erw [reassoc_of% h₀]
  simp only [← H.map_comp_assoc, Iso.hom_inv_id_app]
  erw [H.map_id, Category.id_comp]
  rfl

private theorem proper_pull_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (w : k ≫ p = r ≫ i) :
    (Functor.whiskerLeft (ringedPull l E i) (a.realizationModel.reductionPull r).hom ≫
        Functor.whiskerRight (a.realizationModel.reductionPull i).hom (pull l E r)) ≫
        Functor.whiskerLeft (calculus l E Z).reduction
          (a.compositors.square l E k r p i w).hom =
      Functor.whiskerRight (ringedSquare l E k r p i w).hom
          (calculus l E U).reduction ≫
        (Functor.whiskerLeft (ringedPull l E p) (a.realizationModel.reductionPull k).hom ≫
          Functor.whiskerRight (a.realizationModel.reductionPull p).hom (pull l E k)) := by
  have h := pull_square_nat l E o a.realizationModel a.compositors r k i p w.symm
  have hR : (ringedSquare l E r k i p w.symm).inv =
      (ringedSquare l E k r p i w).hom := by
    simp only [ringedSquare, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Category.assoc]
    rfl
  have hS : (a.compositors.square l E r k i p w.symm).inv =
      (a.compositors.square l E k r p i w).hom := by
    simp only [Compositors.square, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Category.assoc]
    rfl
  rw [hR, hS] at h
  exact h

private theorem push_reduction_eq_mate
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    ordinaryPushReduction l E o a.realizationModel f =
      (mateEquiv (ringedAdj l E f) (o.direct f).adj
        (a.realizationModel.reductionPull f).inv).natTrans := by
  rfl

private theorem proper_exchange_eq_mate
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (w : k ≫ p = r ≫ i) :
    properExchange l E o a.compositors k r p i w =
      (mateEquiv (o.direct p).adj (o.direct r).adj
        (TwoSquare.mk _ _ _ _ (a.compositors.square l E k r p i w).hom)).natTrans := by
  rfl

section

attribute [local irreducible] mateEquiv ringedAdj Direct.adj

private theorem proper_exchange_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (w : k ≫ p = r ≫ i) (L : Integral l E V) :
    type_of% (mate_pasting_square
    (ringedAdj l E p) (ringedAdj l E r)
    (o.direct p).adj (o.direct r).adj
    (a.realizationModel.reductionPull p) (a.realizationModel.reductionPull r)
    (a.realizationModel.reductionPull i).hom (a.realizationModel.reductionPull k).hom
    (TwoSquare.mk _ _ _ _ (ringedSquare l E k r p i w).hom)
    (TwoSquare.mk _ _ _ _ (a.compositors.square l E k r p i w).hom)
    (proper_pull_coeff l E o a k r p i w) L) :=
  mate_pasting_square
    (ringedAdj l E p) (ringedAdj l E r)
    (o.direct p).adj (o.direct r).adj
    (a.realizationModel.reductionPull p) (a.realizationModel.reductionPull r)
    (a.realizationModel.reductionPull i).hom (a.realizationModel.reductionPull k).hom
    (TwoSquare.mk _ _ _ _ (ringedSquare l E k r p i w).hom)
    (TwoSquare.mk _ _ _ _ (a.compositors.square l E k r p i w).hom)
    (proper_pull_coeff l E o a k r p i w) L

end

private theorem open_beta_coeff
    (o : Operations l E) (a : AmbientModels l E o)
    {U' U V' V : Scheme.{u}} (v : U' ⟶ U) (j' : U' ⟶ V') (j : U ⟶ V) (g : V' ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (w : v ≫ j = j' ≫ g) (sq : IsPullback v j' j g)
    (L : Integral l E U) (M : System l E U)
    (q : (calculus l E U).reduction.obj L ⟶ M) :
    (a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E g).map
          (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j).app L) ≫
            (Operations.shriek l E o j).map q) ≫
        (a.openComparisons.beta v j' j g w sq).hom.app M =
      (calculus l E V').reduction.map ((a.ringedOpenComparisons.beta v j' j g w sq).hom.app L) ≫
        GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j').app
          ((ringedPull l E v).obj L)) ≫
        (Operations.shriek l E o j').map
          ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q) := by
  let qJ := GeneratorReduction.inverseOrZero
    ((a.realizationModel.openReduction l E j).app L) ≫
      (Operations.shriek l E o j).map q
  have hj : IsIso ((a.realizationModel.openReduction l E j).app L) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j L
  have hj' : IsIso ((a.realizationModel.openReduction l E j').app
    ((ringedPull l E v).obj L)) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j' _
  have hj₀ := hj
  have hj'₀ := hj'
  change IsIso (((mateEquiv (ringedOpenAdj l E j) (o.extension j).adj).symm
    (a.realizationModel.reductionPull j).hom).natTrans.app L) at hj
  change IsIso (((mateEquiv (ringedOpenAdj l E j') (o.extension j').adj).symm
    (a.realizationModel.reductionPull j').hom).natTrans.app
      ((ringedPull l E v).obj L)) at hj'
  have hu : q ≫ (o.extension j).adj.unit.app M =
      (calculus l E _).reduction.map ((ringedOpenAdj l E j).unit.app L) ≫
        (a.realizationModel.reductionPull j).hom.app ((ringedOpen l E j).obj L) ≫
        (pull l E j).map qJ := by
    simpa only [qJ, RealizationModel.openReduction, ringedOpenAdj, Operations.shriek] using!
      GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j)
        (o.extension j).adj (a.realizationModel.reductionPull j).hom q
  have hs := open_beta_inverse_square l E o a v j' j g w sq L M q qJ hu
  have hi := inverse_square (calculus l E V').reduction
    ((a.ringedOpenComparisons.beta v j' j g w sq).app L).symm
    ((a.openComparisons.beta v j' j g w sq).app M).symm
    (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j').app
        ((ringedPull l E v).obj L)) ≫
      (Operations.shriek l E o j').map
        ((a.realizationModel.reductionPull v).hom.app L ≫ (pull l E v).map q))
    ((a.realizationModel.reductionPull g).hom.app ((ringedOpen l E j).obj L) ≫
      (pull l E g).map qJ)
    (by
      rw [GeneratorReduction.inverseOrZero_eq_inv]
      simpa only [Iso.symm_hom, Iso.app_inv, RealizationModel.openReduction,
        ringedOpenAdj, Operations.shriek, Category.assoc] using! hs)
  simpa only [Iso.symm_inv, Iso.app_hom, qJ, Category.assoc] using! hi

/-- Ordinary coefficient compatibility with the fixed compactification exchange.
Source: blueprint fix-prop-coherence, the prescribed proper/open exchange composite.
(blueprint: lem-sf-integral-ordinary-compactification-exchange-square).

Proof: write L for the ringed interpretation of e, M for its system interpretation,
and q : R(L) ⟶ M for its ordinary coefficient map. The coefficient of the open
image is the inverse open-reduction component followed by open extension of q.
The helper proper_pull_coeff supplies the pullback coefficient boundary; applying
mate_pasting_square with the actual ringed and system direct-image adjunctions
transposes it to the proper-exchange coefficient square on the open image.
Naturality of properExchange inserts the open-image coefficient. The helper
open_beta_coeff supplies the open base-change square for the same q, obtained
from the inverse-open mate unit equation and open_beta_inverse_square by inverse
cancellation. It applies to every compactification open, without quasi-compactness.
Apply ordinaryPushReduction.naturality to the ringed open base-change component.
Functoriality now pastes these three equalities: proper exchange, proper image
of open base change, and transport of the open coefficient. Expanding the
prescribed compactificationExchangeFromData and ringedCompactificationExchange
identifies precisely the two fixed composites in this statement. Reassociate and
use map_comp to obtain the displayed equality. No completion comparison is used.

The generic mate, pullback-boundary, and open-base-change helpers above are proved.
The remaining step is their concrete pasting: the draft closes tactic goals but
kernel checking times out while converting the mate components' category instances.
-/
theorem ordinaryCompactificationExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {U V U' V' : Over B}
    (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
    (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
    (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
    (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    (Expression.pull y (.compactSupport f cf e)).ordinaryReduction l E o a K ≫
        (compactificationExchange l E o a.compositors a.openComparisons
          cf cf' x.left y.left z wi wp hi).app
            (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V'.left).reduction.map
          ((ringedCompactificationExchange l E a.ringedModels a.ringedOpenComparisons
            cf cf' x.left y.left z wi wp hi).app (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.compactSupport f' cf' (.pull x e)).ordinaryReduction l E o a K := by sorry

end WeilConjectures.IntegralSystemRealization
