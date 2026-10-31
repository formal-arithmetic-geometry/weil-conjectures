/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SbcExchangeDiscrete
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ComparisonDirectImageCanonicalMate
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import all WeilConjectures.AlgebraicGeometry.FiniteClopenBetaSiteTransport
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! Discrete pro-etale site comparison for the exchange mate.

The comparison is obtained by transposing both paths under the `f'` adjunction,
using the unit and counit equations for the canonical direct-image mate and the
coherence of the inverse-image comparison. (blueprint: sk-lem-sbc-exchange-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives D] [EnoughInjectives D']
  {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
  {a : C ⥤ C'} {b : D ⥤ D'}
  [l.Additive] [r.Additive] [p.Additive] [t.Additive] [a.Additive] [b.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]

private theorem derived_mate_eq (e : l ⊣ r) (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom).natTrans =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom).natTrans := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnit D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom).natTrans) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

end

section
variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  (e : l ⊣ r) (e' : l' ⊣ r') (d : p ⊣ s) (d' : p' ⊣ s')
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}
  (a : A₀ ⋙ p ≅ l ⋙ A₁) (a' : A₂ ⋙ p' ≅ l' ⋙ A₃)
  (c : A₀ ⋙ q ≅ g ⋙ A₂) (c' : A₁ ⋙ t ≅ h ⋙ A₃)
  (b : r ⋙ A₀ ⟶ A₁ ⋙ s) (b' : r' ⋙ A₂ ⟶ A₃ ⋙ s')
  (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
  (hb : ∀ K, a.inv.app (r.obj K) ≫ p.map (b.app K) ≫ d.counit.app (A₁.obj K) =
    A₁.map (e.counit.app K))
  (hb' : ∀ K, a'.inv.app (r'.obj K) ≫ p'.map (b'.app K) ≫ d'.counit.app (A₃.obj K) =
    A₃.map (e'.counit.app K))
  (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.inv.app (l.obj M) ≫ t.map (a.inv.app M) =
    a'.inv.app (g.obj M) ≫ p'.map (c.inv.app M) ≫ ϑ.app (A₀.obj M))

include a a' hb hb' hsq in
private theorem comparison_mate_transport (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) ≫ b'.app (h.obj K) ≫
      s'.map (c'.inv.app K) =
    c.inv.app (r.obj K) ≫ q.map (b.app K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).natTrans.app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.inv.app (g.obj (r.obj K)))).1
  have hn := a'.inv.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.inv.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b.app K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end

private theorem unpack_comparison_reverse
    {A B B' C P Q Q' R : Type*} [Category A] [Category B] [Category B']
    [Category C] [Category P] [Category Q] [Category Q'] [Category R]
    (L₁ : A ⥤ B) (L₂ : B ⥤ C) (L₁' : A ⥤ B') (L₂' : B' ⥤ C)
    (K₀ : A ⥤ P) (K₁ : B ⥤ Q) (K₁' : B' ⥤ Q') (K₂ : C ⥤ R)
    (R₁ : P ⥤ Q) (R₂ : Q ⥤ R) (R₁' : P ⥤ Q') (R₂' : Q' ⥤ R)
    (c₂ : K₁ ⋙ R₂ ≅ L₂ ⋙ K₂) (c₁ : K₀ ⋙ R₁ ≅ L₁ ⋙ K₁)
    (c₂' : K₁' ⋙ R₂' ≅ L₂' ⋙ K₂) (c₁' : K₀ ⋙ R₁' ≅ L₁' ⋙ K₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂')
    (F : A) (h : ComparisonSquareComponent
      { L₁ := L₁, L₂ := L₂, L₁' := L₁', L₂' := L₂', K₀ := K₀,
        K₁ := K₁, K₁' := K₁', K₂ := K₂, R₁ := R₁, R₂ := R₂,
        R₁' := R₁', R₂' := R₂', c₂ := c₂.symm, c₁ := c₁.symm,
        c₂' := c₂'.symm, c₁' := c₁'.symm, se := se, sp := sp } F) :
      K₂.map (se.hom.app F) ≫ c₂'.inv.app (L₁'.obj F) ≫ R₂'.map (c₁'.inv.app F) =
    c₂.inv.app (L₁.obj F) ≫ R₂.map (c₁.inv.app F) ≫ sp.hom.app (K₀.obj F) := h.symm

section
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace CategoryTheory.Functor

variable {B C B' C' B₀ C₀ B₀' C₀' : Type*}
  [Category* B] [Category* C] [Category* B'] [Category* C']
  [Category* B₀] [Category* C₀] [Category* B₀'] [Category* C₀']
  [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [EnoughInjectives B] [EnoughInjectives B']
  [EnoughInjectives B₀] [EnoughInjectives B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

private theorem cube_forward_comparison
    (e : G ⋙ Q ⟶ P ⋙ H) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G ⋙ V ⟶ U ⋙ G₀) (b : H ⋙ V' ⟶ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q ⋙ V') (d : U ⋙ P₀ ≅ P ⋙ U')
    (h : ∀ F : B, V'.map (e.app F) ≫ b.app (P.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G.obj F) ≫ Q₀.map (a.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory.Plus B) :
    D+(V').map ((rightDerivedFunctorPlusBaseChange e).app K) ≫
        (rightDerivedFunctorPlusBaseChange b).app (D+(P).obj K) =
      ((mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
        mapDerivedCategoryPlusNatIso c ≪≫ mapDerivedCategoryPlusCompIso Q V').inv.app
          (R+(G).obj K) ≫
        D+(Q₀).map ((rightDerivedFunctorPlusBaseChange a).app K) ≫
        (rightDerivedFunctorPlusBaseChange e₀).app (D+(U).obj K) ≫
        R+(H₀).map (((mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
          mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso P U').hom.app K) := by
  have hc := rightDerivedFunctorPlusBaseChange_cube G H G₀ H₀ P Q P₀ Q₀ U V U' V'
    e e₀ a b c d h K
  have hfinal := congrArg (fun z ↦ z ≫
    R+(H₀).map (((mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
      mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso P U').hom.app K)) hc
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hfinal
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hfinal
  exact hfinal

end CategoryTheory.Functor
end

namespace AlgebraicGeometry.Scheme

section

variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem underived_comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h

@[irreducible] private def flip_comparison_square
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare u f' f g) : ChosenCartesianSquare f' u g f :=
  { toCommSq := sq.toCommSq.flip
    isoPullback := sq.isoPullback ≪≫ pullbackSymmetry f g
    hom_fst := by simp [sq.hom_snd]
    hom_snd := by simp [sq.hom_fst] }

private theorem ordinary_comparison_rectangle
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare u f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').map ((Etale.baseChangeMap (ModuleCat.{u + 1}
        Λ) sq.toCommSq).app F) ≫
        (lowerStarComparisonUpperStarBaseChange f' (ModuleCat.{u + 1} Λ)).app ((Etale.upperStar
          (ModuleCat.{u + 1} Λ) u).obj F) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').map
          ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u).inv.app F) =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj F) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
          ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app F) ≫
        (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
          (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm).hom).natTrans.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F) := by
  have hsq (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').map ((Etale.squareUpperStarIso (ModuleCat.{u
        + 1} Λ) sq.toCommSq).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u).inv.app ((Etale.upperStar
          (ModuleCat.{u + 1} Λ) f).obj M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).map ((comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} Λ) f).inv.app M) =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').inv.app ((Etale.upperStar
        (ModuleCat.{u + 1} Λ) g).obj M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map ((comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} Λ) g).inv.app M) ≫
        (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj M) := by
    as_aux_lemma =>
      have hc := comparison_square_component_of_commRing Λ sq M
      rw [BetaSiteTransportProof.comparison_square_data_flip_eq Λ
        (flip_comparison_square sq) sq] at hc
      exact unpack_comparison_reverse _ _ _ _ _ _ _ _ _ _ _ _
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f')
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)
        (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq)
        (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm) M hc
  have ht := comparison_mate_transport
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))
    (lowerStarComparisonUpperStarBaseChange f' (ModuleCat.{u + 1} Λ))
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm).hom
    (underived_comparison_counit Λ f)
    (underived_comparison_counit Λ f') hsq F
  simpa only [Etale.baseChangeMap, Iso.symm_hom] using ht

private theorem derived_etale_exchange_eq
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq u f' f g) :
    Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rfl

private theorem canonical_mate_eq {U V : Scheme.{u}} (f : U ⟶ V) :
    comparisonDirectImageCanonicalMate Λ f =
      Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) := by
  rfl

private theorem pullback_plus_iso_eq {U V : Scheme.{u}} (f : U ⟶ V) :
    directImageComparisonPullbackPlusIso Λ f =
      (Functor.mapDerivedCategoryPlusCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) := by
  rfl

end

private theorem derived_comparison_rectangle
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare u f' f g)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlus.map
        ((Etale.derivedBaseChangeMapPlus
          (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
      (comparisonDirectImageCanonicalMate Λ f').app
        ((Etale.upperStar
          (ModuleCat.{u + 1} Λ) u).mapDerivedCategoryPlus.obj K) =
    (directImageComparisonPullbackPlusIso Λ g).inv.app
        ((Etale.lowerStar
          (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K) ≫
      (ProEtale.upperStar
        (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.map
        ((comparisonDirectImageCanonicalMate Λ f).app K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (mateEquiv
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
          (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm).hom).natTrans).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K) ≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} Λ) f').rightDerivedFunctorPlus.map
        ((directImageComparisonPullbackPlusIso Λ u).hom.app K) := by
  let ep := (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm).hom).natTrans
  have hc := ordinary_comparison_rectangle Λ sq
  have hd := Functor.cube_forward_comparison
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (Etale.lowerStar (ModuleCat.{u + 1} Λ) f')
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f) (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f')
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u) (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u) (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X') (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y')
    (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) ep
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))
    (lowerStarComparisonUpperStarBaseChange f' (ModuleCat.{u + 1} Λ))
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u) hc K
  simpa only [derived_etale_exchange_eq, canonical_mate_eq,
    pullback_plus_iso_eq, ep] using hd

/-- The bounded-below discrete site comparison square for a chosen cartesian square.

Source: blueprint `sk-lem-sbc-exchange-compatibility`, site-comparison clause.
Proof: establish the ordinary comparison rectangle by transposing under the
pro-etale `f'` adjunction and using pullback comparison coherence and the two
comparison counit equations. Apply the proved right-derived cube theorem.
Identify its pro-etale face with `sbcDiscreteExchangePlus` by derived mate
compatibility, then postcompose with the forward pullback comparison.
(blueprint: lem-sbc-exchange-site-comparison)
-/
theorem sbcExchangeSiteComparison
    (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : ChosenCartesianSquare u f' f g)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y').mapDerivedCategoryPlus.map
        ((Etale.derivedBaseChangeMapPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app K) ≫
      (comparisonDirectImageCanonicalMate (ULift.{u + 1, u} A) f').app
        ((Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus.obj K) =
    (directImageComparisonPullbackPlusIso (ULift.{u + 1, u} A) g).inv.app
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctorPlus.obj K) ≫
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlus.map
        ((comparisonDirectImageCanonicalMate (ULift.{u + 1, u} A) f).app K) ≫
      (sbcDiscreteExchangePlus A sq).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategoryPlus.obj K) ≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').rightDerivedFunctorPlus.map
        ((directImageComparisonPullbackPlusIso (ULift.{u + 1, u} A) u).hom.app K) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let ep := (mateEquiv (ProEtale.upperStarLowerStarAdjunction B f)
    (ProEtale.upperStarLowerStarAdjunction B f')
    (ProEtale.upperStarCompIso B sq.w.symm).hom).natTrans
  have h := derived_comparison_rectangle (ULift.{u + 1, u} A) sq K
  have hep : Functor.rightDerivedFunctorPlusBaseChange ep = sbcDiscreteExchangePlus A sq := by
    as_aux_lemma =>
      dsimp only [ep, sbcDiscreteExchangePlus]
      rw [derived_mate_eq, Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
        Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  rw [hep] at h
  exact h

end AlgebraicGeometry.Scheme
