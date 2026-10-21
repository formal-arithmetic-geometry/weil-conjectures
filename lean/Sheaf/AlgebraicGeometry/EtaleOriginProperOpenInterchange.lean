/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q113, F7
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
public import Sheaf.Paper.UnboundedProperOpenInterchange
public import Sheaf.Paper.ProperOpenCoefficientMate
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Etale-origin proper/open interchange

Source: retained repaired proof of blueprint main-20261015,
`prop-exc-base-change-proper`, Step 7; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange).

The five arrows use the published fixed-scalar comparisons, transported through the
canonical intrinsic realization. No ambient exceptional adjunction is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme


variable (A : Type u) [CommRing A] [Finite A]

/-- The specified etale interchange, selected together with its full representative and
open-adjunction normalization. Those conditions determine the map on all objects.
Source: Stacks Tag 0F7B, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenEtaleInterchange {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)] :
    (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory ≅
    (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor :=
  Etale.properOpenCoefficientInterchange (ULift.{u + 1, u} A)
    (IsPullback.of_hasPullback p i)



/-- The five-arrow site-transport composite. The two intervening Plus compatibility
isomorphisms merely identify termwise open extension before and after inclusion into D.
Source: retained blueprint Step 7, five-arrow display; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginProperOpenIso {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedOpen A i).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) :=
  let ke := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)
  let pe := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)
  (sfIntrinsicDerivedOpen A i).mapIso
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).symm ≪≫
    (etaleOriginOpenExtensionComparison A i).symm.app (re.rightDerivedFunctor.obj K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      ((etaleOriginOpenEtaleInterchange A p i).app K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      (pe.rightDerivedFunctor.mapIso (ke.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A p (ke.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((etaleOriginOpenComparison A V).mapIso (ke.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A (pullback.fst p i)).app K.obj)


/-- Conjugation by the retained pair (K, alpha) specifying an etale origin. This is the
formula in the node, with no choice of witness made by the definition.
Source: retained blueprint Step 7, witness display; Stacks Tag 099R
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def witnessedEtaleOriginProperOpenIso {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)]
    {M : proEtaleDerivedCategory (pullback p i) A}
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (alpha : (etaleOriginOpenComparison A (pullback p i)).obj K.obj ≅ M) :
    (sfIntrinsicDerivedOpen A i).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj M) :=
  (sfIntrinsicDerivedOpen A i).mapIso
      ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).mapIso alpha.symm) ≪≫
    etaleOriginProperOpenIso A p i K ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((sfIntrinsicDerivedOpen A (pullback.fst p i)).mapIso alpha)


/-- The already recorded restriction normalization, oriented as lambda rather than its
inverse. Its inverse is exactly the published open-unit followed by inverse restriction.
Source: retained blueprint Step 7, restriction display; Stacks Tags 09AE and 09BN
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenLambda {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsOpenImmersion i] :
    sfIntrinsicDerivedOpen A (pullback.fst p i) ⋙ proEtaleConstantDerivedDirectImage p A ⋙
        sfIntrinsicDerivedPullback A i ≅
      proEtaleConstantDerivedDirectImage (pullback.snd p i) A :=
  (@asIso _ _ _ _ (proEtaleOpenRestrictionLambdaInverse p i A)
    (proEtaleDerivedOpenRestriction p i A).2.2).symm


attribute [local irreducible] etaleOriginOpenComparison etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  etaleOriginProperOpenIso
  sfIntrinsicDerivedEquivalence sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek

private lemma open_mate_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (e : L ⊣ R) (d : L' ⊣ R') {A : C ⥤ C'} {B : D ⥤ D'}
    (c : L ⋙ B ≅ A ⋙ L') {X : C} {Y : D} {X' : C'} {Y' : D'}
    (b : A.obj X ≅ X') (v : B.obj Y ≅ Y') (f : L.obj X ⟶ Y) :
    d.homEquiv X' Y'
        (L'.map b.inv ≫ c.inv.app X ≫ B.map f ≫ v.hom) =
      b.inv ≫ A.map (e.homEquiv X Y f) ≫
        (mateEquiv e d (TwoSquare.mk _ _ _ _ c.inv)).natTrans.app Y ≫
          R'.map v.hom := by
  let a := (mateEquiv e d (TwoSquare.mk _ _ _ _ c.inv)).natTrans
  have hu := unit_mateEquiv e d (TwoSquare.mk _ _ _ _ c.inv) X
  change A.map (e.unit.app X) ≫ a.app (L.obj X) =
    d.unit.app (A.obj X) ≫ R'.map (c.inv.app X) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := d.unit.naturality b.inv
  change b.inv ≫ d.unit.app (A.obj X) =
    d.unit.app X' ≫ R'.map (L'.map b.inv) at hn
  rw [← reassoc_of% hn, ← reassoc_of% hu]
  have ha := a.naturality f
  change A.map (R.map f) ≫ a.app Y = a.app (L.obj X) ≫ R'.map (B.map f) at ha
  rw [← reassoc_of% ha]


/-- Site transport preserves the canonical Cartesian proper/open interchange on every
bounded-below input of etale origin: invertibility, independence of the entire witness,
naturality for every morphism between witnessed objects, and both open-adjunction
normalizations. The first normalization includes the open unit identifying its source.
No ambient exceptional adjoint or all-sheaf finite-CD datum is a hypothesis.
Source: retained repaired blueprint proof of prop-exc-base-change-proper, Step 7;
Stacks Tags 099R and 0F7B (blueprint: lem-exc-etale-origin-proper-open-interchange).

Proof:
1. Transpose the five-arrow isomorphism under the open adjunction. The unit equation
   for mateEquiv, naturality, and the specified etale interchange normalization express
   its transpose using inverse etale restriction and the open restriction comparison.
2. Apply etaleOriginOpenRestriction_transport to identify this composite with the
   intrinsic lambda inverse. Cancel the source direct-image comparison. Injectivity of
   the open homEquiv identifies the five-arrow map with i! of lambda inverse followed
   by the open counit.
3. This counit formula defines a natural transformation on all intrinsic objects.
   Naturality moves any witness isomorphism through it; functoriality then cancels the
   witness with its inverse. Every witnessed map equals this canonical transformation
   at M. This proves witness independence and naturality for all ambient morphisms.
4. The adjunction inverse identity gives the unit-normalized equation after composing
   with lambda. The counit formula gives the final equation. Invertibility follows from
   the explicit isomorphisms. No ambient exceptional adjoint or finite-CD bound is used. -/
theorem etaleOriginProperOpenInterchange (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)] :
    (∀ K, IsIso (etaleOriginProperOpenIso A p i K).hom) ∧
    ∀ (M : proEtaleDerivedCategory (pullback p i) A)
      (K : DerivedCategory.Plus
        (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (alpha : (etaleOriginOpenComparison A (pullback p i)).obj K.obj ≅ M),
      IsIso (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ∧
      (∀ (L : DerivedCategory.Plus
          (Sheaf (pullback p i).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (beta : (etaleOriginOpenComparison A (pullback p i)).obj L.obj ≅ M),
        (witnessedEtaleOriginProperOpenIso A p i K alpha).hom =
          (witnessedEtaleOriginProperOpenIso A p i L beta).hom) ∧
      (∀ (N : proEtaleDerivedCategory (pullback p i) A)
        (L : DerivedCategory.Plus
          (Sheaf (pullback p i).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (beta : (etaleOriginOpenComparison A (pullback p i)).obj L.obj ≅ N) (f : M ⟶ N),
        (sfIntrinsicDerivedOpen A i).map
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).map f) ≫
          (witnessedEtaleOriginProperOpenIso A p i L beta).hom =
        (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ≫
          (proEtaleConstantDerivedDirectImage p A).map
            ((sfIntrinsicDerivedOpen A (pullback.fst p i)).map f)) ∧
      ((exceptionalOpenAdjunction i A).unit.app
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≫
          (sfIntrinsicDerivedPullback A i).map
            (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ≫
          (etaleOriginOpenLambda A p i).hom.app M = 𝟙 _) ∧
      ((witnessedEtaleOriginProperOpenIso A p i K alpha).hom =
        (sfIntrinsicDerivedOpen A i).map
            ((proEtaleOpenRestrictionLambdaInverse p i A).app M) ≫
          (exceptionalOpenAdjunction i A).counit.app
            ((proEtaleConstantDerivedDirectImage p A).obj
              ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj M))) := by
  let r := proEtaleConstantDerivedDirectImage (pullback.snd p i) A
  let k := sfIntrinsicDerivedOpen A (pullback.fst p i)
  let q := proEtaleConstantDerivedDirectImage p A
  let j := sfIntrinsicDerivedOpen A i
  let adj := exceptionalOpenAdjunction i A
  let lam := proEtaleOpenRestrictionLambdaInverse p i A
  let c : r ⋙ j ⟶ k ⋙ q :=
    whiskerRight lam j ≫ whiskerLeft (k ⋙ q) adj.counit
  have hc (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
      (etaleOriginProperOpenIso A p i K).hom =
        c.app ((etaleOriginOpenComparison A (pullback p i)).obj K.obj) := by
    let ae := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
    obtain ⟨le, hle, hge⟩ :=
      (Etale.unboundedProperOpenInterchange (ULift.{u + 1, u} A)).choose_spec.choose_spec.2.2.1
        (pullback.fst p i) (pullback.snd p i) p i (IsPullback.of_hasPullback p i)
    have hgamma : ae.homEquiv _ _ ((etaleOriginOpenEtaleInterchange A p i).hom.app K.obj) =
        le.inv.app K.obj := by
      have hg := hge K.obj
      rw [etaleOriginOpenEtaleInterchange,
        Etale.properOpenCoefficientInterchange_eq_recorded, hg]
      exact (ae.homEquiv _ _).apply_symm_apply (le.inv.app K.obj)
    have ht := open_mate_transport ae adj
      (etaleOriginOpenExtensionComparison A i)
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K)
      (etaleOriginOpenTargetComparison A p i K)
      ((etaleOriginOpenEtaleInterchange A p i).hom.app K.obj)
    dsimp only [Functor.comp_obj] at hgamma
    rw [hgamma] at ht
    have hr := etaleOriginOpenRestriction_transport A p i K (le.app K.obj) (hle K.obj)
    have htrans : adj.homEquiv _ _ (etaleOriginProperOpenIso A p i K).hom =
        lam.app ((etaleOriginOpenComparison A (pullback p i)).obj K.obj) := by
      change adj.homEquiv _ _ _ = _ at ht
      change _ = (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).inv ≫
        (etaleOriginOpenComparison A W).map (le.app K.obj).inv ≫
          (etaleOriginOpenRestrictionMate A i).app _ ≫
            (sfIntrinsicDerivedPullback A i).map
              (etaleOriginOpenTargetComparison A p i K).hom at ht
      rw [hr] at ht
      simpa only [etaleOriginProperOpenIso, etaleOriginOpenTargetComparison,
        Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
        Category.assoc, Iso.inv_hom_id_assoc] using ht
    exact (adj.homEquiv _ _).injective
      (htrans.trans ((adj.homEquiv _ _).apply_symm_apply _).symm)
  have hw (M : proEtaleDerivedCategory (pullback p i) A)
      (K : DerivedCategory.Plus
        (Sheaf (pullback p i).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (alpha : (etaleOriginOpenComparison A (pullback p i)).obj K.obj ≅ M) :
      (witnessedEtaleOriginProperOpenIso A p i K alpha).hom = c.app M := by
    dsimp only [witnessedEtaleOriginProperOpenIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [hc]
    change (r ⋙ j).map alpha.inv ≫ c.app _ ≫ (k ⋙ q).map alpha.hom = _
    rw [c.naturality_assoc, ← Functor.map_comp]
    simp
  refine ⟨fun K ↦ inferInstance, fun M K alpha ↦ ⟨inferInstance, ?_, ?_, ?_, ?_⟩⟩
  · intro L beta
    rw [hw M K alpha, hw M L beta]
  · intro N L beta f
    rw [hw M K alpha, hw N L beta]
    exact c.naturality f
  · rw [hw M K alpha]
    change adj.unit.app (r.obj M) ≫ (sfIntrinsicDerivedPullback A i).map
      (j.map (lam.app M) ≫ adj.counit.app ((k ⋙ q).obj M)) ≫
        (etaleOriginOpenLambda A p i).hom.app M = _
    have ht := (adj.homEquiv (r.obj M) ((k ⋙ q).obj M)).apply_symm_apply
      (lam.app M)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at ht
    change adj.unit.app (r.obj M) ≫ (sfIntrinsicDerivedPullback A i).map
      ((sfIntrinsicDerivedOpen A i).map (lam.app M) ≫
        adj.counit.app ((k ⋙ q).obj M)) ≫ _ = _
    calc
      _ = lam.app M ≫ (etaleOriginOpenLambda A p i).hom.app M := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ (etaleOriginOpenLambda A p i).hom.app M) ht
      _ = 𝟙 _ := (etaleOriginOpenLambda A p i).inv_hom_id_app M
  · exact hw M K alpha

end AlgebraicGeometry.Scheme
