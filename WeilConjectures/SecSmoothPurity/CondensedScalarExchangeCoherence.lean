/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
import all WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.AlgebraicGeometry.ScalarPullbackMateInverseNormalized
import WeilConjectures.SixFunctors.ModCondensedCachedInstances
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Condensed scalar exchange coherence

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/
lem-fix-operation-reduction.proof.md, paragraphs 2--3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofHasKInjectiveResolutions

private theorem identity_of_composition
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B)
    (i : P ≅ 𝟭 A) (j : Q ≅ 𝟭 B)
    (c : P ≅ P ⋙ P) (d : Q ≅ Q ⋙ Q)
    (hc : ∀ K, c.hom.app K ≫ P.map (i.hom.app K) = 𝟙 _)
    (hd : ∀ K, d.hom.app K ≫ Q.map (j.hom.app K) = 𝟙 _)
    (b : T ⋙ Q ≅ P ⋙ T)
    (h : ∀ K, d.hom.app (T.obj K) ≫ Q.map (b.hom.app K) ≫ b.hom.app (P.obj K) =
      b.hom.app K ≫ T.map (c.hom.app K)) (K : A) :
    b.hom.app K = j.hom.app (T.obj K) ≫ T.map (i.inv.app K) := by
  have hn := b.hom.naturality (i.hom.app K)
  dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_obj] at hn
  have he := congrArg (fun z => z ≫ T.map (P.map (i.hom.app K))) (h K)
  simp only [Category.assoc] at he
  rw [← hn, ← T.map_comp, hc, T.map_id] at he
  erw [Category.comp_id] at he
  have he' : d.hom.app (T.obj K) ≫ Q.map (b.hom.app K ≫ T.map (i.hom.app K)) = 𝟙 _ := by
    apply (cancel_mono (b.hom.app K)).1
    simpa only [Q.map_comp, Category.assoc, Category.id_comp (obj := B),
      Category.comp_id (obj := B)] using he
  have hh : Q.map (b.hom.app K ≫ T.map (i.hom.app K)) =
      Q.map (j.hom.app (T.obj K)) := by
    apply (cancel_epi (d.hom.app (T.obj K))).1
    exact he'.trans (hd _).symm
  have hh' : b.hom.app K ≫ T.map (i.hom.app K) = j.hom.app (T.obj K) := by
    have hn' := j.hom.naturality (b.hom.app K ≫ T.map (i.hom.app K))
    have hn'' := j.hom.naturality (j.hom.app (T.obj K))
    rw [hh] at hn'
    exact (cancel_epi (j.hom.app _)).1 (hn'.symm.trans hn'')
  apply (cancel_mono (T.map (i.hom.app K))).1
  rw [hh']
  simp only [Category.assoc, ← T.map_comp, Iso.inv_hom_id_app]
  erw [T.map_id]
  exact (Category.comp_id _).symm

/-- The canonical identity geometric unitor, with the existing scalar interface exposed.
Source: inverse-image identity, blueprint operation reduction, paragraph 3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence). -/
def exchangeScalarIdentity
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) : L R (𝟙 X) ≅ 𝟭 _ := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarId R X

private def identityPullbackCompositor
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) :
    L R (𝟙 X) ≅ L R (𝟙 X) ⋙ L R (𝟙 X) :=
  (eqToIso (congrArg (fun q => L R q) (Category.id_comp (𝟙 X)))).symm ≪≫
    scalarPullbackComposition R (𝟙 X) (𝟙 X)

section IdentityUnit

attribute [local semireducible] L
attribute [local implicit_reducible] L CondensedRing.moduleObjectDerivedPullback

private theorem identityPullbackCompositor_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u})
    (M : DerivedCategory (Modules R X)) :
    (identityPullbackCompositor R X).hom.app M ≫
      (L R (𝟙 X)).map ((exchangeScalarIdentity R X).hom.app M) = 𝟙 _ := by
  have hu : (scalarPullbackComposition R (𝟙 X) (𝟙 X)).hom.app M ≫
      (L R (𝟙 X)).map ((exchangeScalarIdentity R X).hom.app M) =
      (eqToIso (congrArg (fun q => L R q) (Category.id_comp (𝟙 X)))).hom.app M := by
    unfold scalarPullbackComposition exchangeScalarIdentity L
      CondensedRing.moduleObjectDerivedPullback
    simpa only [id_eq, eqToIso.hom, eqToHom_app] using
      CondensedRing.leftDerivedUpperStarComp_id_right_app R (𝟙 X) M
  dsimp only [identityPullbackCompositor, Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, hu]
  exact Iso.inv_hom_id_app _ M

end IdentityUnit

private theorem identityPullbackCompositor_scalar
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D a V ⋙ L S h ≅ L R h ⋙ D a U)
    (hb : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized a h (b h))
    (X : Scheme.{u}) (M : DerivedCategory (Modules R X)) :
    (identityPullbackCompositor S X).hom.app ((D a X).obj M) ≫
      (L S (𝟙 X)).map ((b (𝟙 X)).hom.app M) ≫
      (b (𝟙 X)).hom.app ((L R (𝟙 X)).obj M) =
    (b (𝟙 X)).hom.app M ≫
      (D a X).map ((identityPullbackCompositor R X).hom.app M) := by
  dsimp only [identityPullbackCompositor, Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [scalar_comp_hom a (𝟙 X) (𝟙 X) b hb M]
  have hn := scalar_congr a (Category.id_comp (𝟙 X)).symm b M
  simp only [Iso.symm_hom, eqToIso.inv, eqToIso.hom] at hn ⊢
  rw [reassoc_of% hn]
  simp only [(D a X).map_comp]

/-- The same normalized scalar comparison in the compact-support coefficient interface.
It is the inverse of the specified scalar-unit mate, conjugated by the canonical
identification of total derived inverse image with its exact localization.
Source: blueprint operation reduction, paragraphs 2--3; scalar-six pullback (1).
(blueprint: lem-fix-condensed-scalar-exchange-coherence). -/
def compactExchangeLambda {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixChange a Y ⋙ detSfDerivedPullback S.X f ≅
      detSfDerivedPullback R.X f ⋙ scalarSixChange a X :=
  Functor.isoWhiskerLeft (scalarSixChange a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f) ≪≫
    (scalarDirectImagePullbackData.theta a f).symm ≪≫
    Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f).symm
      (scalarSixChange a X)

private abbrev sectionDerived
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology T) _)

private theorem cancel_mate_rectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    {a : A₁ ⥤ A₃} {T₃ : A₃ ⥤ B₃} {cb : B₀ ⥤ B₂}
    {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂} {T₂ : A₂ ⥤ B₂}
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (lc : T₀ ⋙ cb ≅ c ⋙ T₂)
    (e : rf ⋙ c ⟶ a ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (h : ∀ J, mateRouteLeft cb r eb la J = mateRouteRight T₂ lc.hom e t J) :
    Functor.whiskerRight e T₂ ≫ Functor.whiskerLeft a t =
      Functor.whiskerLeft rf lc.inv ≫ Functor.whiskerRight r cb ≫
        Functor.whiskerLeft T₁ eb ≫ Functor.whiskerRight la rgb := by
  ext J
  change T₂.map (e.app J) ≫ t.app (a.obj J) =
    lc.inv.app (rf.obj J) ≫ cb.map (r.app J) ≫ eb.app (T₁.obj J) ≫
      rgb.map (la.app J)
  apply ((lc.app (rf.obj J)).eq_inv_comp).2
  change mateRouteRight T₂ lc.hom e t J = mateRouteLeft cb r eb la J
  exact (h J).symm

private theorem normalizedScalarExchange
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D a V ⋙ L Λ' h ≅ L Λ h ⋙ D a U)
    (hb : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized a h (b h))
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    Functor.whiskerRight (scalarAmbientExchange Λ sq) (D a Y') ≫
        Functor.whiskerLeft (L Λ u) (rho a f' (b f')) =
      Functor.whiskerLeft (F Λ f) (b v).inv ≫
        Functor.whiskerRight (rho a f (b f)) (L Λ' v) ≫
        Functor.whiskerLeft (D a X) (scalarAmbientExchange Λ' sq) ≫
        Functor.whiskerRight (b u).hom (F Λ' f') := by
  let : ∀ T : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T) := sectionDerived Λ
  let : ∀ T : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T) := sectionDerived Λ'
  exact cancel_mate_rectangle
    (rho a f (b f)) (scalarAmbientExchange Λ' sq) (b u).hom
    (b v) (scalarAmbientExchange Λ sq) (rho a f' (b f'))
    (fun K => (scalar_geometric_exchange_rectangle a sq b hb K).1)


/-- Composition, identity, Cartesian cube and ordinary exchange compatibility of
normalized scalar pullback. The last equation is one of natural transformations.
Source: latest blueprint operation reduction, paragraph 3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence).

Proof, steps 1--4 of the node: the existing normalized scalar composition equation
and cancellation of the geometric compositor give composition. At identity arrows,
composition and naturality, together with the canonical geometric right-unit law,
force the stated unitor equation. Scalar pullback square coherence gives the cube.
Take the internal component of the existing geometric exchange rectangle, then
apply an abstract categorical cancellation lemma for the invertible bottom-edge
pullback comparison to obtain the final natural transformation equation. The section
derived-category instances needed to invoke that theorem follow from the existing
Grothendieck theorem. No exchange or direct-image mate is inverted. -/
theorem condensedScalarExchangeCoherence
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D a V ⋙ L Λ' h ≅ L Λ h ⋙ D a U)
    (_hb : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized a h (b h)) :
    (∀ {X Z Y : Scheme.{u}} (j : X ⟶ Z) (r : Z ⟶ Y)
      (K : DerivedCategory (Modules Λ Y)),
      (b (j ≫ r)).hom.app K =
        (scalarPullbackComposition Λ' j r).hom.app ((D a Y).obj K) ≫
          (L Λ' j).map ((b r).hom.app K) ≫
          (b j).hom.app ((L Λ r).obj K) ≫
          (D a X).map ((scalarPullbackComposition Λ j r).inv.app K)) ∧
    (∀ (X : Scheme.{u}) (K : DerivedCategory (Modules Λ X)),
      (b (𝟙 X)).hom.app K =
        (exchangeScalarIdentity Λ' X).hom.app ((D a X).obj K) ≫
          (D a X).map ((exchangeScalarIdentity Λ X).inv.app K)) ∧
    (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v)
      (K : DerivedCategory (Modules Λ Y)),
      (L Λ' f').map ((b v).hom.app K) ≫
          (b f').hom.app ((L Λ v).obj K) ≫
          (D a X').map ((scalarPullbackSquare Λ sq).hom.app K) =
        (scalarPullbackSquare Λ' sq).hom.app ((D a Y).obj K) ≫
          (L Λ' u).map ((b f).hom.app K) ≫ (b u).hom.app ((L Λ f).obj K)) ∧
    (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v),
      Functor.whiskerRight (scalarAmbientExchange Λ sq) (D a Y') ≫
          Functor.whiskerLeft (L Λ u) (rho a f' (b f')) =
        Functor.whiskerLeft (F Λ f) (b v).inv ≫
          Functor.whiskerRight (rho a f (b f)) (L Λ' v) ≫
          Functor.whiskerLeft (D a X) (scalarAmbientExchange Λ' sq) ≫
          Functor.whiskerRight (b u).hom (F Λ' f')) := by
  constructor
  · intro X Z Y j r K
    have h := scalar_comp_hom a j r b _hb K
    apply (cancel_mono ((D a X).map
      ((scalarPullbackComposition Λ j r).hom.app K))).1
    simp only [Category.assoc]
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    erw [(D a X).map_id]
    simpa only [CategoryTheory.Functor.comp_obj, Category.comp_id] using h.symm
  · constructor
    · intro X K
      exact identity_of_composition (D a X) (L Λ (𝟙 X)) (L Λ' (𝟙 X))
        (exchangeScalarIdentity Λ X) (exchangeScalarIdentity Λ' X)
        (identityPullbackCompositor Λ X) (identityPullbackCompositor Λ' X)
        (identityPullbackCompositor_unit Λ X) (identityPullbackCompositor_unit Λ' X)
        (b (𝟙 X)) (identityPullbackCompositor_scalar a b _hb X) K
    · constructor
      · intro X' X Y' Y u v f f' sq K
        exact scalar_pullback_square_coherence a sq b _hb K
      · intro X' X Y' Y u v f f' sq
        exact normalizedScalarExchange a b _hb sq

/-- Horizontal and vertical pasting for the specified geometric exchange mates.
Together with the scalar comparison composition and cube equations, these are
pasting coherence of the scalar/exchange rectangle. Composite adjunctions and
pullback squares retain their canonical geometric compositors.
Source: latest blueprint operation reduction, paragraph 3; mate-pasting (1),(2).
(blueprint: lem-fix-condensed-scalar-exchange-coherence).

Proof: scalarAmbientExchange is by definition the mate of scalarPullbackSquare
under the geometric adjunctions. Horizontal pasting is then the generic mate law
mateEquiv_vcomp, and vertical pasting is mateEquiv_hcomp for the composite
adjunctions; both hold for any squares, so no scalar or geometric hypothesis is
used. No exchange or direct-image mate is assumed invertible. -/
theorem condensedScalarExchangePasting
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (∀ {X₂ X₁ X₀ Y₂ Y₁ Y₀ : Scheme.{u}}
      {u₁ : X₁ ⟶ X₀} {u₂ : X₂ ⟶ X₁}
      {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
      {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
      (s₁ : ChosenCartesianSquare u₁ f₁ f₀ v₁)
      (s₂ : ChosenCartesianSquare u₂ f₂ f₁ v₂),
      mateEquiv (adj R f₀) (adj R f₂)
          (TwoSquare.hComp
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)) =
        TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₁))
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₂))) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}}
      {u : X' ⟶ X} {v : Y' ⟶ Y} {w : Z' ⟶ Z}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
      (s₁ : ChosenCartesianSquare u f' f v)
      (s₂ : ChosenCartesianSquare v g' g w),
      mateEquiv ((adj R g).comp (adj R f)) ((adj R g').comp (adj R f'))
          (TwoSquare.vComp
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)) =
        TwoSquare.hComp
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₁))
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₂))) := by
  constructor
  · intro X₂ X₁ X₀ Y₂ Y₁ Y₀ u₁ u₂ v₁ v₂ f₀ f₁ f₂ s₁ s₂
    exact congrArg TwoSquare.natTrans
      (mateEquiv_vcomp (adj R f₀) (adj R f₁) (adj R f₂)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom))
  · intro X' X Y' Y Z' Z u v w f f' g g' s₁ s₂
    exact congrArg TwoSquare.natTrans
      (mateEquiv_hcomp (adj R g) (adj R g') (adj R f) (adj R f')
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom))

end AlgebraicGeometry.ProEtale.QuotientChange

open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances


attribute [local irreducible] DerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofHasKInjectiveResolutions

private local instance compactRingComm (R : ScalarSixRing.{u}) : IsCommMonObj R.X := R.comm

private local instance compactMapMon {R S : ScalarSixRing.{u}} (a : R ⟶ S) :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
@[irreducible] private def compactOpenScalarIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ scalarSixChange a Z ≅
      scalarSixChange a X ⋙ (openImmersionLowerShriek Λ'.X j).mapDerivedCategory := by
  with_unfolding_all
    exact @derivedOpenImmersionShriekIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom X Z j inferInstance

private theorem compactScalarMapFormula {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    scalarCompactSupportMap a j p =
      Functor.whiskerLeft (openImmersionLowerShriek R.X j).mapDerivedCategory
          (scalarDirectImageMate a p) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (compactOpenScalarIso a j).hom (RootCoordinateFace.lower S.X p) ≫
        (Functor.associator _ _ _).hom := by
  delta scalarCompactSupportMap compactOpenScalarIso
  with_unfolding_all rfl


private theorem compactScalarOpenUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {TX : A ⥤ C} {RX : C ⥤ A} {TZ : B ⥤ D} {RZ : D ⥤ B}
    (a : J ⊣ P) (b : J' ⊣ P') (c : TX ⊣ RX) (d : TZ ⊣ RZ)
    (e : P' ⋙ RX ≅ RZ ⋙ P) (K : A) :
    b.unit.app (TX.obj K) ≫ P'.map
        (((conjugateIsoEquiv (c.comp b) (a.comp d)).symm e).inv.app K) =
      TX.map (a.unit.app K) ≫ (Adjunction.pushHomOfComapIso d c e).app (J.obj K) := by
  let δ := (conjugateIsoEquiv (c.comp b) (a.comp d)).symm e
  have he : conjugateEquiv (a.comp d) (c.comp b) δ.inv = e.inv := by
    exact congrArg Iso.inv ((conjugateIsoEquiv (c.comp b) (a.comp d)).apply_symm_apply e)
  have hm : (mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans =
      Adjunction.pushHomOfComapIso d c e := by
    have ht := iterated_mateEquiv_conjugateEquiv a b c d (.mk _ _ _ _ δ.inv)
    rw [he] at ht
    have hs : mateEquiv d c (mateEquiv a b (.mk _ _ _ _ δ.inv)) =
        .mk _ _ _ _ e.inv := by
      ext N
      exact congr_app ht N
    exact congrArg TwoSquare.natTrans ((mateEquiv d c).eq_symm_apply.mpr hs)
  have hu := unit_mateEquiv a b (.mk _ _ _ _ δ.inv) K
  change TX.map (a.unit.app K) ≫
      ((mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans).app (J.obj K) =
    b.unit.app (TX.obj K) ≫ P'.map (δ.inv.app K) at hu
  rw [hm] at hu
  exact hu.symm

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem compactCondensedScalarOpenUnit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j).unit.app
        ((scalarSixChange a X).obj K) ≫
      (scalarSixPull Λ' j).map
        ((compactOpenScalarIso a j).inv.app K) =
      (scalarSixChange a X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app K) ≫
      (scalarDirectImagePullbackData.theta a j).hom.app
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) := by
  with_unfolding_all
    rw [scalarDirectImagePullbackData.thetaNormalization]
    exact compactScalarOpenUnit
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j)
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z))
      (@derivedComapUpperStarIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom X Z j) K


end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.QuotientChange

private theorem compactExactAdjunction_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f) =
      (CondensedRing.upperStarLowerStarAdjunction R f
        ).mapDerivedCategoryRightDerivedAdjunction := by
  have hd : CondensedRing.derivedUpperStarLowerStarAdjunction R f =
      ((CondensedRing.upperStarLowerStarAdjunction R f).mapDerivedCategoryRightDerivedAdjunction
        ).ofNatIsoLeft (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f)
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (CondensedRing.upperStar R f)).symm
  rw [hd]
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]

private theorem compactMateTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {R : D ⥤ C} {M M' : E ⥤ F} {S : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) (e : L ≅ L') (e' : M ≅ M')
    {G : C ⥤ E} {H : D ⥤ F} (t : G ⋙ M' ⟶ L' ⋙ H) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G e'.hom ≫ t ≫ Functor.whiskerRight e.inv H))).natTrans =
      (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft e')
        (TwoSquare.mk _ _ _ _ t)).natTrans := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc]

private theorem compactMateRightTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P P₀ : B ⥤ A} {J' : C ⥤ D} {P' P₀' : D ⥤ C}
    (a : J ⊣ P) (b : J' ⊣ P') (e : P₀ ≅ P) (e' : P₀' ≅ P')
    {G : A ⥤ C} {H : B ⥤ D} (t : P₀ ⋙ G ⟶ H ⋙ P₀') :
    ((mateEquiv (a.ofNatIsoRight e.symm) (b.ofNatIsoRight e'.symm)).symm
        (.mk _ _ _ _ t)).natTrans =
      ((mateEquiv a b).symm (.mk _ _ _ _
        (Functor.whiskerRight e.inv G ≫ t ≫ Functor.whiskerLeft H e'.hom))).natTrans := by
  ext K
  simp [mateEquiv_symm_apply, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, Category.assoc]

private theorem compactInverseMateFormula
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    (a : J ⊣ P) (b : J' ⊣ P')
    {G : A ⥤ C} {H : B ⥤ D} (θ : P ⋙ G ≅ H ⋙ P') :
    (Functor.leftUnitor _).inv ≫ Functor.whiskerRight a.unit (G ⋙ J') ≫
        (Functor.squareTransport J J' θ).hom ≫
        Functor.whiskerLeft (J ⋙ H) b.counit ≫ (Functor.rightUnitor _).hom =
      ((mateEquiv a b).symm (.mk _ _ _ _ θ.hom)).natTrans := by
  ext K
  simp [mateEquiv_symm_apply]

private theorem compactInverseMateUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    (a : J ⊣ P) (b : J' ⊣ P')
    {G : A ⥤ C} {H : B ⥤ D} (t : P ⋙ G ⟶ H ⋙ P') (K : A) :
    b.unit.app (G.obj K) ≫
        P'.map (((mateEquiv a b).symm (.mk P H G P' t)).natTrans.app K) =
      G.map (a.unit.app K) ≫ t.app (J.obj K) := by
  exact (unit_mateEquiv_symm a b (.mk P H G P' t) K).symm

private theorem compactUnitTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P P₀ : B ⥤ A} {J' : C ⥤ D} {P' P₀' : D ⥤ C}
    (a : J ⊣ P) (b : J' ⊣ P') (e : P₀ ≅ P) (e' : P₀' ≅ P')
    {TX : A ⥤ C} {TZ : B ⥤ D} (β : J ⋙ TZ ≅ TX ⋙ J')
    (θ : P ⋙ TX ≅ TZ ⋙ P')
    (h : ∀ K, b.unit.app (TX.obj K) ≫ P'.map (β.inv.app K) =
      TX.map (a.unit.app K) ≫ θ.hom.app (J.obj K)) (K : A) :
    (b.ofNatIsoRight e'.symm).unit.app (TX.obj K) ≫ P₀'.map (β.inv.app K) =
      TX.map ((a.ofNatIsoRight e.symm).unit.app K) ≫
        (Functor.isoWhiskerLeft TZ e' ≪≫ θ.symm ≪≫
          Functor.isoWhiskerRight e.symm TX).inv.app (J.obj K) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Functor.whiskerRight_app, Category.assoc]
  rw [← e'.inv.naturality]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [reassoc_of% h]
  simp only [← TX.map_comp_assoc, Iso.inv_hom_id_app, TX.map_id, Category.id_comp]

private theorem compactOpenMateCube
    {C D E F Cb Db Eb Fb : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category Cb] [Category Db] [Category Eb] [Category Fb]
    {LA : C ⥤ D} {JA : D ⥤ C} {LA' : E ⥤ F} {JA' : F ⥤ E}
    {LB : Cb ⥤ Db} {JB : Db ⥤ Cb} {LB' : Eb ⥤ Fb} {JB' : Fb ⥤ Eb}
    (a : LA ⊣ JA) (a' : LA' ⊣ JA') (b : LB ⊣ JB) (b' : LB' ⊣ JB')
    {HA : C ⥤ E} {GA : D ⥤ F} {HB : Cb ⥤ Eb} {GB : Db ⥤ Fb}
    {S : C ⥤ Cb} {Q : D ⥤ Db} {S' : E ⥤ Eb} {Q' : F ⥤ Fb}
    (β : LA ⋙ Q ≅ S ⋙ LB) (β' : LA' ⋙ Q' ≅ S' ⋙ LB')
    (dA : HA ⋙ LA' ≅ LA ⋙ GA) (dB : HB ⋙ LB' ≅ LB ⋙ GB)
    (lj : Q ⋙ JB ≅ JA ⋙ S) (lj' : Q' ⋙ JB' ≅ JA' ⋙ S')
    (lh : S ⋙ HB ≅ HA ⋙ S') (lg : Q ⋙ GB ≅ GA ⋙ Q')
    (cA : JA ⋙ HA ≅ GA ⋙ JA') (cB : JB ⋙ HB ≅ GB ⋙ JB')
    (hi : ∀ M, b.unit.app (S.obj M) ≫ JB.map (β.inv.app M) =
      S.map (a.unit.app M) ≫ lj.inv.app (LA.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ JB'.map (β'.inv.app M) =
      S'.map (a'.unit.app M) ≫ lj'.inv.app (LA'.obj M))
    (hdA : ∀ M, a'.unit.app (HA.obj M) ≫ JA'.map (dA.hom.app M) =
      HA.map (a.unit.app M) ≫ cA.hom.app (LA.obj M))
    (hdB : ∀ M, b'.unit.app (HB.obj M) ≫ JB'.map (dB.hom.app M) =
      HB.map (b.unit.app M) ≫ cB.hom.app (LB.obj M))
    (hc : Functor.whiskerRight cA.hom S' ≫
        Functor.whiskerLeft GA lj'.inv ≫ Functor.whiskerRight lg.inv JB' =
      Functor.whiskerLeft JA lh.inv ≫ Functor.whiskerRight lj.inv HB ≫
        Functor.whiskerLeft Q cB.hom)
    (M : C) :
    GB.map (β.hom.app M) ≫ dB.inv.app (S.obj M) ≫ LB'.map (lh.hom.app M) =
      lg.hom.app (LA.obj M) ≫ Q'.map (dA.inv.app M) ≫ β'.hom.app (HA.obj M) := by
  have h :
      LB'.map (lh.inv.app M) ≫ dB.hom.app (S.obj M) ≫ GB.map (β.inv.app M) =
        β'.inv.app (HA.obj M) ≫ Q'.map (dA.hom.app M) ≫ lg.inv.app (LA.obj M) := by
    set_option backward.isDefEq.respectTransparency true in
      apply (b'.homEquiv _ _).injective
      simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
      have hn := b'.unit.naturality (lh.inv.app M)
      dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
      rw [← reassoc_of% hn, reassoc_of% hdB]
      have hn := cB.hom.naturality (β.inv.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [← hn, ← HB.map_comp_assoc, hi, HB.map_comp, Category.assoc]
      have hn := lh.inv.naturality (a.unit.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [← reassoc_of% hn]
      rw [reassoc_of% hi']
      have hn := lj'.inv.naturality (dA.hom.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [← reassoc_of% hn, ← S'.map_comp_assoc, hdA, S'.map_comp, Category.assoc]
      have hc' := congr_app hc (LA.obj M)
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp_obj] at hc'
      rw [hc']
  let l := LB'.mapIso (lh.symm.app M) ≪≫ dB.app (S.obj M) ≪≫ GB.mapIso (β.symm.app M)
  let r := β'.symm.app (HA.obj M) ≪≫ Q'.mapIso (dA.app M) ≪≫ lg.symm.app (LA.obj M)
  have hh : l.hom = r.hom := h
  have hinv := congrArg Iso.inv (Iso.ext hh : l = r)
  simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.symm_inv, Category.assoc] using hinv

private def compactBalanced {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    D (Λ := R.X) (Λ' := S.X) a.hom.hom V ⋙ L S.X f ≅
      L R.X f ⋙ D (Λ := R.X) (Λ' := S.X) a.hom.hom U := by
  unfold D L
  exact compactExchangeLambda a f

private theorem compactBalanced_normalized {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    PullNormalized (Λ := R.X) (Λ' := S.X) a.hom.hom f (compactBalanced a f) := by
  obtain ⟨q, hq, hnorm⟩ :=
    DiagonalCoefficients.scalar_pullback_mate_inverse_normalized
      (R := R.X) (T := S.X) a.hom.hom f
  have hcmp : DiagonalCoefficients.scalarPullbackComparison
      (R := R.X) (T := S.X) a.hom.hom f = (compactExchangeLambda a f).inv := by
    let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := R.X) (Λ' := S.X) a.hom.hom V)
    let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := R.X) (Λ' := S.X) a.hom.hom U)
    let t := (mateEquiv adjY adjX).symm
      (TwoSquare.mk _ _ _ _ (derivedComapUpperStarIso (Λ := R.X) (Λ' := S.X) a.hom.hom f).inv)
    let eR := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f
    let eS := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f).symm
    have he : (t.whiskerTop eR.hom).whiskerBottom eS.hom =
        (mateEquiv adjY adjX).symm (TwoSquare.mk _ _ _ _
          (DiagonalCoefficients.scalarRestrictionPullbackIso
            (R := R.X) (T := S.X) a.hom.hom f).inv) := by
      apply (mateEquiv adjY adjX).injective
      simp only [t, mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
      ext M
      dsimp only [eR, eS, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
        TwoSquare.mk, TwoSquare.natTrans]
      simp only [DiagonalCoefficients.scalarRestrictionPullbackIso,
        DiagonalCoefficients.derivedUpper,
        Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
        Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Category.assoc, Equiv.apply_symm_apply]
    have h := congrArg TwoSquare.natTrans he
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
      TwoSquare.natTrans] at h
    simp only [t, adjY, adjX, eR, eS, DiagonalCoefficients.scalarPullbackComparison,
      Adjunction.pushHomOfComapIso, compactExchangeLambda, Iso.trans_inv,
      Iso.symm_inv, Iso.symm_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      scalarDirectImagePullbackData.thetaNormalization, scalarSixPullHom,
      TwoSquare.mk, TwoSquare.natTrans, Category.assoc,
      scalarSixChange, scalarSixAdjunctionLeft, scalarSixPull,
      DiagonalCoefficients.derivedUpper, DiagonalCoefficients.derivedScalars] at h ⊢
    convert h.symm using 2
  have heq : q = compactBalanced a f := by
    apply Iso.ext_inv
    rw [hq]
    with_unfolding_all exact hcmp
  rw [← heq]
  exact hnorm

set_option maxHeartbeats 800000 in
-- Compare the folded scalar and geometric functors before applying mate transport.
private theorem compactRho_eq {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    rho (Λ := R.X) (Λ' := S.X) a.hom.hom f (compactBalanced a f) =
      (by unfold F D; exact scalarDirectImageMate a f) := by
  have ht := compactMateTransport
    (CondensedRing.derivedUpperStarLowerStarAdjunction R.X f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction S.X f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f)
    (scalarDirectImagePullbackData.theta a f).inv
  rw [compactExactAdjunction_eq, compactExactAdjunction_eq] at ht
  delta rho compactBalanced adj L F D scalarSixChange scalarSixAdjunctionLeft
    CondensedRing.moduleObjectDerivedPullback CondensedRing.moduleObjectDerivedPushforward
    scalarDirectImageMate RootCoordinateFace.adjunction RootCoordinateFace.upper
  with_unfolding_all exact ht

@[irreducible] private def compactOpenAdj
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek R j).mapDerivedCategory ⊣ detSfDerivedPullback R j := by
  exact (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R j).symm

private theorem compactOpenScalarUnit {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategory (Modules R.X U)) :
    (compactOpenAdj S.X j).unit.app ((scalarSixChange a U).obj K) ≫
        (detSfDerivedPullback S.X j).map ((CondensedRing.compactOpenScalarIso a j).inv.app K) =
      (scalarSixChange a U).map ((compactOpenAdj R.X j).unit.app K) ≫
        (compactExchangeLambda a j).inv.app
          ((CondensedRing.openImmersionLowerShriek R.X j).mapDerivedCategory.obj K) := by
  have h := compactUnitTransport
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R.X j)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction S.X j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X j)
    (CondensedRing.compactOpenScalarIso a j)
    (scalarDirectImagePullbackData.theta a j)
    (CondensedRing.compactCondensedScalarOpenUnit a j) K
  simpa only [compactOpenAdj, compactExchangeLambda, id_eq] using h

private theorem compactD_functor_eq {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    (X : Scheme.{u}) :
    D (Λ := R.X) (Λ' := S.X) a.hom.hom X = scalarSixChange a X := by
  delta D extension scalarSixChange scalarSixAdjunctionLeft
  rfl

private theorem compactL_functor_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L R f = detSfDerivedPullback R f := by
  delta L CondensedRing.moduleObjectDerivedPullback detSfDerivedPullback
  rfl

private theorem compactF_functor_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F R f = RootCoordinateFace.lower R f := by
  delta F RootCoordinateFace.lower
  rfl

private theorem compactCompHEq {C : Type*} [Category C] {A B Z A' B' Z' : C}
    (hA : A = A') (hB : B = B') (hZ : Z = Z')
    {f : A ⟶ B} {g : B ⟶ Z} {f' : A' ⟶ B'} {g' : B' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hA
  cases hB
  cases hZ
  cases hf
  cases hg
  rfl

private theorem compactAdj_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adj R f = (by
      delta F L CondensedRing.moduleObjectDerivedPullback
        CondensedRing.moduleObjectDerivedPushforward
      exact CondensedRing.derivedUpperStarLowerStarAdjunction R f) := by
  delta adj
  rfl

private theorem compactSquare_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    scalarPullbackSquare R sq = (by
      delta L CondensedRing.moduleObjectDerivedPullback
      exact condensedAmbientPullbackComparison R sq) := by
  delta scalarPullbackSquare scalarPullbackComposition L
    CondensedRing.moduleObjectDerivedPullback condensedAmbientPullbackComparison
  rfl

set_option maxHeartbeats 800000 in
-- Identify mates after rewriting their adjunctions and input squares.
private theorem compactAmbientExchange_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    scalarAmbientExchange R sq = (by
      delta F L CondensedRing.moduleObjectDerivedPullback
        CondensedRing.moduleObjectDerivedPushforward
      exact condensedAmbientExchange R sq) := by
  let m (a : L R f ⊣ F R f) (b : L R f' ⊣ F R f')
      (t : L R v ⋙ L R f' ⟶ L R f ⋙ L R u) :
      F R f ⋙ L R v ⟶ L R u ⋙ F R f' :=
    (mateEquiv a b (.mk _ _ _ _ t)).natTrans
  have h₁ := congrArg₂
    (fun (a : L R f ⊣ F R f) (b : L R f' ⊣ F R f') =>
      m a b (scalarPullbackSquare R sq).hom)
    (compactAdj_eq R f) (compactAdj_eq R f')
  have h₂ := congrArg
    (fun t => m
      (by delta L F; exact CondensedRing.derivedUpperStarLowerStarAdjunction R f)
      (by delta L F; exact CondensedRing.derivedUpperStarLowerStarAdjunction R f') t)
    (congrArg Iso.hom (compactSquare_eq R sq))
  have h := h₁.trans h₂
  delta scalarAmbientExchange condensedAmbientExchange
  dsimp only [m, id] at h ⊢
  delta L F CondensedRing.moduleObjectDerivedPullback
    CondensedRing.moduleObjectDerivedPushforward at h ⊢
  exact h

private theorem compactBalanced_heq {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    HEq (compactBalanced a f) (compactExchangeLambda a f) := by
  delta compactBalanced L D extension CondensedRing.moduleObjectDerivedPullback
  with_unfolding_all rfl

private theorem compactSquare_heq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    HEq (scalarPullbackSquare R sq) (condensedAmbientPullbackComparison R sq) := by
  have h := heq_of_eq (compactSquare_eq R sq)
  beta_reduce at h
  delta L CondensedRing.moduleObjectDerivedPullback id at h ⊢
  exact h

private theorem compactAmbient_heq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    HEq (scalarAmbientExchange R sq) (condensedAmbientExchange R sq) := by
  have h := heq_of_eq (compactAmbientExchange_eq R sq)
  beta_reduce at h
  delta F L CondensedRing.moduleObjectDerivedPullback
    CondensedRing.moduleObjectDerivedPushforward id at h ⊢
  exact h

private theorem compactRho_heq {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    HEq (rho (Λ := R.X) (Λ' := S.X) a.hom.hom f (compactBalanced a f))
      (scalarDirectImageMate a f) := by
  have h := heq_of_eq (compactRho_eq a f)
  beta_reduce at h
  delta F D extension scalarSixChange scalarSixAdjunctionLeft RootCoordinateFace.lower
    CondensedRing.moduleObjectDerivedPushforward id at h ⊢
  exact h

private theorem compactIsoHomHEq {C D : Type*} [Category C] [Category D]
    {F G F' G' : C ⥤ D} {i : F ≅ G} {j : F' ≅ G'}
    (hF : F = F') (hG : G = G') (hi : HEq i j) : HEq i.hom j.hom := by
  cases hF
  cases hG
  cases hi
  rfl

private theorem compactIsoInvHEq {C D : Type*} [Category C] [Category D]
    {F G F' G' : C ⥤ D} {i : F ≅ G} {j : F' ≅ G'}
    (hF : F = F') (hG : G = G') (hi : HEq i j) : HEq i.inv j.inv := by
  cases hF
  cases hG
  cases hi
  rfl

private theorem compactWhiskerRightHEq {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F G F' G' : C ⥤ D} {i : F ⟶ G} {j : F' ⟶ G'} {H H' : D ⥤ E}
    (hF : F = F') (hG : G = G') (hi : HEq i j) (hH : H = H') :
    HEq (Functor.whiskerRight i H) (Functor.whiskerRight j H') := by
  cases hF
  cases hG
  cases hi
  cases hH
  rfl

private theorem compactWhiskerLeftHEq {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G H G' H' : D ⥤ E} {i : G ⟶ H} {j : G' ⟶ H'}
    (hF : F = F') (hG : G = G') (hH : H = H') (hi : HEq i j) :
    HEq (Functor.whiskerLeft F i) (Functor.whiskerLeft F' j) := by
  cases hF
  cases hG
  cases hH
  cases hi
  rfl

private theorem compactInvertRoutes {C : Type*} [Category C]
    {A B D E B' D' : C} (i : A ≅ B) (j : B ≅ D) (k : D ≅ E)
    (i' : A ≅ B') (j' : B' ≅ D') (k' : D' ≅ E)
    (h : i.hom ≫ j.hom ≫ k.hom = i'.hom ≫ j'.hom ≫ k'.hom) :
    k.inv ≫ j.inv ≫ i.inv = k'.inv ≫ j'.inv ≫ i'.inv := by
  have he : i ≪≫ j ≪≫ k = i' ≪≫ j' ≪≫ k' := by
    apply Iso.ext
    exact h
  have hi := congrArg Iso.inv he
  simpa only [Iso.trans_inv, Category.assoc] using hi

private theorem compactSourceInverseSquare
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D (Λ := R) (Λ' := S) a V ⋙ L S h ≅ L R h ⋙ D (Λ := R) (Λ' := S) a U)
    (hb : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized a h (b h))
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v)
    (M : DerivedCategory (Modules R Y)) :
    (D (Λ := R) (Λ' := S) a X').map ((scalarPullbackSquare R sq).inv.app M) ≫
        (b f').inv.app ((L R v).obj M) ≫ (L S f').map ((b v).inv.app M) =
      (b u).inv.app ((L R f).obj M) ≫ (L S u).map ((b f).inv.app M) ≫
        (scalarPullbackSquare S sq).inv.app ((D (Λ := R) (Λ' := S) a Y).obj M) := by
  have h := compactInvertRoutes
    ((L S f').mapIso ((b v).app M))
    ((b f').app ((L R v).obj M))
    ((D (Λ := R) (Λ' := S) a X').mapIso ((scalarPullbackSquare R sq).app M))
    ((scalarPullbackSquare S sq).app ((D (Λ := R) (Λ' := S) a Y).obj M))
    ((L S u).mapIso ((b f).app M))
    ((b u).app ((L R f).obj M))
    (by
      simpa only [Functor.mapIso_hom, Iso.app_hom] using
        scalar_pullback_square_coherence a sq b hb M)
  simpa only [Functor.mapIso_inv, Iso.app_inv] using h

private theorem compactSourceInverseNat
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D (Λ := R) (Λ' := S) a V ⋙ L S h ≅ L R h ⋙ D (Λ := R) (Λ' := S) a U)
    (hb : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized a h (b h))
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    Functor.whiskerRight (scalarPullbackSquare R sq).inv (D (Λ := R) (Λ' := S) a X') ≫
        Functor.whiskerLeft (L R v) (b f').inv ≫
        Functor.whiskerRight (b v).inv (L S f') =
      Functor.whiskerLeft (L R f) (b u).inv ≫
        Functor.whiskerRight (b f).inv (L S u) ≫
        Functor.whiskerLeft (D (Λ := R) (Λ' := S) a Y) (scalarPullbackSquare S sq).inv := by
  ext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using
    compactSourceInverseSquare R S a b hb sq M

set_option maxHeartbeats 1600000 in
-- Transport the inverse cube as a natural transformation before evaluating it.
private theorem compactInverseNat {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {v : Y' ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (sq : ChosenCartesianSquare u f' f v) :
    Functor.whiskerRight (condensedAmbientPullbackComparison R.X sq).inv
        (scalarSixChange a X') ≫
        Functor.whiskerLeft (detSfDerivedPullback R.X v) (compactExchangeLambda a f').inv ≫
        Functor.whiskerRight (compactExchangeLambda a v).inv (detSfDerivedPullback S.X f') =
      Functor.whiskerLeft (detSfDerivedPullback R.X f) (compactExchangeLambda a u).inv ≫
        Functor.whiskerRight (compactExchangeLambda a f).inv (detSfDerivedPullback S.X u) ≫
        Functor.whiskerLeft (scalarSixChange a Y)
          (condensedAmbientPullbackComparison S.X sq).inv := by
  have dY : D (Λ := R.X) (Λ' := S.X) a.hom.hom Y = scalarSixChange a Y :=
    compactD_functor_eq a Y
  have dY' : D (Λ := R.X) (Λ' := S.X) a.hom.hom Y' = scalarSixChange a Y' :=
    compactD_functor_eq a Y'
  have dX : D (Λ := R.X) (Λ' := S.X) a.hom.hom X = scalarSixChange a X :=
    compactD_functor_eq a X
  have dX' : D (Λ := R.X) (Λ' := S.X) a.hom.hom X' = scalarSixChange a X' :=
    compactD_functor_eq a X'
  have vR : L R.X v = detSfDerivedPullback R.X v := compactL_functor_eq R.X v
  have vS : L S.X v = detSfDerivedPullback S.X v := compactL_functor_eq S.X v
  have fR : L R.X f = detSfDerivedPullback R.X f := compactL_functor_eq R.X f
  have fS : L S.X f = detSfDerivedPullback S.X f := compactL_functor_eq S.X f
  have fR' : L R.X f' = detSfDerivedPullback R.X f' := compactL_functor_eq R.X f'
  have fS' : L S.X f' = detSfDerivedPullback S.X f' := compactL_functor_eq S.X f'
  have uR : L R.X u = detSfDerivedPullback R.X u := compactL_functor_eq R.X u
  have uS : L S.X u = detSfDerivedPullback S.X u := compactL_functor_eq S.X u
  have eA := congrArg₂ Functor.comp (congrArg₂ Functor.comp fR uR) dX'
  have eB := congrArg₂ Functor.comp (congrArg₂ Functor.comp vR fR') dX'
  have eC := congrArg₂ Functor.comp vR (congrArg₂ Functor.comp dY' fS')
  have eZ := congrArg₂ Functor.comp (congrArg₂ Functor.comp dY vS) fS'
  have eB' := congrArg₂ Functor.comp fR (congrArg₂ Functor.comp dX uS)
  have eC' := congrArg₂ Functor.comp (congrArg₂ Functor.comp dY fS) uS
  have hl₁ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp fR uR) (congrArg₂ Functor.comp vR fR')
    (compactIsoInvHEq (congrArg₂ Functor.comp vR fR')
      (congrArg₂ Functor.comp fR uR) (compactSquare_heq R.X sq)) dX'
  have hl₂ := compactWhiskerLeftHEq vR
    (congrArg₂ Functor.comp fR' dX') (congrArg₂ Functor.comp dY' fS')
    (compactIsoInvHEq (congrArg₂ Functor.comp dY' fS')
      (congrArg₂ Functor.comp fR' dX') (compactBalanced_heq a f'))
  have hl₃ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp vR dY') (congrArg₂ Functor.comp dY vS)
    (compactIsoInvHEq (congrArg₂ Functor.comp dY vS)
      (congrArg₂ Functor.comp vR dY') (compactBalanced_heq a v)) fS'
  have hr₁ := compactWhiskerLeftHEq fR
    (congrArg₂ Functor.comp uR dX') (congrArg₂ Functor.comp dX uS)
    (compactIsoInvHEq (congrArg₂ Functor.comp dX uS)
      (congrArg₂ Functor.comp uR dX') (compactBalanced_heq a u))
  have hr₂ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp fR dX) (congrArg₂ Functor.comp dY fS)
    (compactIsoInvHEq (congrArg₂ Functor.comp dY fS)
      (congrArg₂ Functor.comp fR dX) (compactBalanced_heq a f)) uS
  have hr₃ := compactWhiskerLeftHEq dY
    (congrArg₂ Functor.comp fS uS) (congrArg₂ Functor.comp vS fS')
    (compactIsoInvHEq (congrArg₂ Functor.comp vS fS')
      (congrArg₂ Functor.comp fS uS) (compactSquare_heq S.X sq))
  have hl := compactCompHEq eA eB eZ hl₁ (compactCompHEq eB eC eZ hl₂ hl₃)
  have hr := compactCompHEq eA eB' eZ hr₁ (compactCompHEq eB' eC' eZ hr₂ hr₃)
  have h := compactSourceInverseNat R.X S.X a.hom.hom
    (fun h => compactBalanced a h) (fun h => compactBalanced_normalized a h) sq
  exact eq_of_heq (hl.symm.trans ((heq_of_eq h).trans hr))

private def compactOpenSquare
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    ChosenCartesianSquare (pullback.fst f v) (c.baseChange v).i c.i
      (pullback.fst c.g v) :=
  let sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)
  { toCommSq := sq.toCommSq
    isoPullback := sq.isoPullback
    hom_fst := sq.isoPullback_hom_fst
    hom_snd := sq.isoPullback_hom_snd }

set_option maxHeartbeats 800000 in
-- Check the concrete derived functor endpoints of the transported inverse mate.
private theorem compactOpenBaseChange_mate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    detSfOpenBaseChangeMap R f v c =
      ((mateEquiv (compactOpenAdj R c.i) (compactOpenAdj R (c.baseChange v).i)).symm
        (.mk (detSfDerivedPullback R c.i) (detSfDerivedPullback R (pullback.fst c.g v))
          (detSfDerivedPullback R (pullback.fst f v))
          (detSfDerivedPullback R (c.baseChange v).i)
          (condensedAmbientPullbackComparison R (compactOpenSquare f v c)).inv)).natTrans := by
  let θ := condensedAmbientPullbackComparison R (compactOpenSquare f v c)
  let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R c.i
  let e' := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R (c.baseChange v).i
  let m := Functor.isoWhiskerRight e.symm
      (detSfDerivedPullback R (pullback.fst f v)) ≪≫ θ.symm ≪≫
    Functor.isoWhiskerLeft (detSfDerivedPullback R (pullback.fst c.g v)) e'
  have hf := compactInverseMateFormula
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R c.i)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R (c.baseChange v).i) m
  have ht := compactMateRightTransport
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R c.i)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R (c.baseChange v).i)
    e e' θ.inv
  have he : detSfOpenBaseChangeMap R f v c =
      ((mateEquiv
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R c.i)
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R (c.baseChange v).i)
        ).symm (.mk _ _ _ _ m.hom)).natTrans := by
    dsimp only [m, θ, e, e'] at hf ⊢
    delta detSfOpenBaseChangeMap compactOpenSquare at hf ⊢
    exact hf
  rw [he]
  simpa only [compactOpenAdj, m, θ, e, e', Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom] using ht.symm

set_option maxHeartbeats 800000 in
-- The unit equation compares the concrete composite derived functors.
private theorem compactOpenBaseChange_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f)
    (o : (CondensedRing.openImmersionLowerShriek R c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R (pullback.fst c.g v) ≅
      detSfDerivedPullback R (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek R (c.baseChange v).i).mapDerivedCategory)
    (ho : o.inv = detSfOpenBaseChangeMap R f v c)
    (K : DerivedCategory (Modules R X)) :
    (compactOpenAdj R (c.baseChange v).i).unit.app
        ((detSfDerivedPullback R (pullback.fst f v)).obj K) ≫
        (detSfDerivedPullback R (c.baseChange v).i).map (o.inv.app K) =
      (detSfDerivedPullback R (pullback.fst f v)).map ((compactOpenAdj R c.i).unit.app K) ≫
        (condensedAmbientPullbackComparison R (compactOpenSquare f v c)).inv.app
          ((CondensedRing.openImmersionLowerShriek R c.i).mapDerivedCategory.obj K) := by
  rw [ho, compactOpenBaseChange_mate]
  exact compactInverseMateUnit (compactOpenAdj R c.i) (compactOpenAdj R (c.baseChange v).i)
    (G := detSfDerivedPullback R (pullback.fst f v))
    (H := detSfDerivedPullback R (pullback.fst c.g v))
    (condensedAmbientPullbackComparison R (compactOpenSquare f v c)).inv K

section

attribute [local implicit_reducible] Compactification.baseChange
  Compactification.ofIsPullback CommMon.toMon scalarSixPull
  CondensedRing.moduleObjectDerivedPullback

attribute [local irreducible] Sheaf.monoidalCategory
  Mod.monoidalCategoryStruct Mod.monoidalClosed
attribute [local implicit_reducible] Mod.monoidalCategory Monoidal.induced
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory

set_option maxHeartbeats 1600000 in
-- The generic cube is instantiated at eight large derived module categories.
private theorem compactOpenExchange {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f)
    (oR : (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R.X (pullback.fst c.g v) ≅
      detSfDerivedPullback R.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory)
    (hoR : oR.inv = detSfOpenBaseChangeMap R.X f v c)
    (oS : (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback S.X (pullback.fst c.g v) ≅
      detSfDerivedPullback S.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory)
    (hoS : oS.inv = detSfOpenBaseChangeMap S.X f v c)
    (K : DerivedCategory (Modules R.X X)) :
    (detSfDerivedPullback S.X (pullback.fst c.g v)).map
        ((CondensedRing.compactOpenScalarIso a c.i).hom.app K) ≫
      oS.hom.app ((scalarSixChange a X).obj K) ≫
      (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory.map
        ((compactExchangeLambda a (pullback.fst f v)).hom.app K) =
    (compactExchangeLambda a (pullback.fst c.g v)).hom.app
        ((CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory.obj K) ≫
      (scalarSixChange a (pullback c.g v)).map (oR.hom.app K) ≫
      (CondensedRing.compactOpenScalarIso a (c.baseChange v).i).hom.app
        ((detSfDerivedPullback R.X (pullback.fst f v)).obj K) := by
  dsimp only [Compactification.baseChange, Compactification.ofIsPullback] at *
  have hR := compactOpenBaseChange_unit R.X f v c oR hoR
  have hS := compactOpenBaseChange_unit S.X f v c oS hoS
  exact compactOpenMateCube
    (LA := (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory)
    (JA := detSfDerivedPullback R.X c.i)
    (LA' := (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory)
    (JA' := detSfDerivedPullback R.X (c.baseChange v).i)
    (LB := (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory)
    (JB := detSfDerivedPullback S.X c.i)
    (LB' := (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory)
    (JB' := detSfDerivedPullback S.X (c.baseChange v).i)
    (HA := detSfDerivedPullback R.X (pullback.fst f v))
    (GA := detSfDerivedPullback R.X (pullback.fst c.g v))
    (HB := detSfDerivedPullback S.X (pullback.fst f v))
    (GB := detSfDerivedPullback S.X (pullback.fst c.g v))
    (S := scalarSixChange a X) (Q := scalarSixChange a c.Z)
    (S' := scalarSixChange a (pullback f v)) (Q' := scalarSixChange a (pullback c.g v))
    (compactOpenAdj R.X c.i) (compactOpenAdj R.X (c.baseChange v).i)
    (compactOpenAdj S.X c.i) (compactOpenAdj S.X (c.baseChange v).i)
    (CondensedRing.compactOpenScalarIso a c.i)
    (CondensedRing.compactOpenScalarIso a (c.baseChange v).i) oR.symm oS.symm
    (compactExchangeLambda a c.i) (compactExchangeLambda a (c.baseChange v).i)
    (compactExchangeLambda a (pullback.fst f v)) (compactExchangeLambda a (pullback.fst c.g v))
    (condensedAmbientPullbackComparison R.X (compactOpenSquare f v c)).symm
    (condensedAmbientPullbackComparison S.X (compactOpenSquare f v c)).symm
    (compactOpenScalarUnit a c.i) (compactOpenScalarUnit a (c.baseChange v).i)
    hR hS
    (compactInverseNat a (compactOpenSquare f v c)) K

private theorem compactOpenExchangeNat {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f)
    (oR : (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R.X (pullback.fst c.g v) ≅
      detSfDerivedPullback R.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory)
    (hoR : oR.inv = detSfOpenBaseChangeMap R.X f v c)
    (oS : (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback S.X (pullback.fst c.g v) ≅
      detSfDerivedPullback S.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory)
    (hoS : oS.inv = detSfOpenBaseChangeMap S.X f v c) :
    Functor.whiskerRight (CondensedRing.compactOpenScalarIso a c.i).hom
          (detSfDerivedPullback S.X (pullback.fst c.g v)) ≫
        Functor.whiskerLeft (scalarSixChange a X) oS.hom ≫
        Functor.whiskerRight (compactExchangeLambda a (pullback.fst f v)).hom
          (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory =
      Functor.whiskerLeft (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory
          (compactExchangeLambda a (pullback.fst c.g v)).hom ≫
        Functor.whiskerRight oR.hom (scalarSixChange a (pullback c.g v)) ≫
        Functor.whiskerLeft (detSfDerivedPullback R.X (pullback.fst f v))
          (CondensedRing.compactOpenScalarIso a (c.baseChange v).i).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using compactOpenExchange a f v c oR hoR oS hoS K


end

set_option maxHeartbeats 1600000 in
-- Transport the exchange factors using functor equalities before taking components.
private theorem compactProperNatTransport {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (v : Y' ⟶ Y) :
    Functor.whiskerRight (detSfProperBaseChangeMap R.X p v) (scalarSixChange a Y') ≫
        Functor.whiskerLeft (detSfDerivedPullback R.X (pullback.fst p v))
          (scalarDirectImageMate a (pullback.snd p v)) =
      Functor.whiskerLeft (RootCoordinateFace.lower R.X p) (compactExchangeLambda a v).inv ≫
        Functor.whiskerRight (scalarDirectImageMate a p) (detSfDerivedPullback S.X v) ≫
        Functor.whiskerLeft (scalarSixChange a Z) (detSfProperBaseChangeMap S.X p v) ≫
        Functor.whiskerRight (compactExchangeLambda a (pullback.fst p v)).hom
          (RootCoordinateFace.lower S.X (pullback.snd p v)) := by
  have dY : D (Λ := R.X) (Λ' := S.X) a.hom.hom Y = scalarSixChange a Y :=
    compactD_functor_eq a Y
  have dY' : D (Λ := R.X) (Λ' := S.X) a.hom.hom Y' = scalarSixChange a Y' :=
    compactD_functor_eq a Y'
  have dZ : D (Λ := R.X) (Λ' := S.X) a.hom.hom Z = scalarSixChange a Z :=
    compactD_functor_eq a Z
  have dZ' : D (Λ := R.X) (Λ' := S.X) a.hom.hom (pullback p v) =
      scalarSixChange a (pullback p v) := compactD_functor_eq a (pullback p v)
  have vR : L R.X v = detSfDerivedPullback R.X v := compactL_functor_eq R.X v
  have vS : L S.X v = detSfDerivedPullback S.X v := compactL_functor_eq S.X v
  have uR : L R.X (pullback.fst p v) = detSfDerivedPullback R.X (pullback.fst p v) :=
    compactL_functor_eq R.X (pullback.fst p v)
  have uS : L S.X (pullback.fst p v) = detSfDerivedPullback S.X (pullback.fst p v) :=
    compactL_functor_eq S.X (pullback.fst p v)
  have pR : F R.X p = RootCoordinateFace.lower R.X p := compactF_functor_eq R.X p
  have pS : F S.X p = RootCoordinateFace.lower S.X p := compactF_functor_eq S.X p
  have pR' : F R.X (pullback.snd p v) = RootCoordinateFace.lower R.X (pullback.snd p v) :=
    compactF_functor_eq R.X (pullback.snd p v)
  have pS' : F S.X (pullback.snd p v) = RootCoordinateFace.lower S.X (pullback.snd p v) :=
    compactF_functor_eq S.X (pullback.snd p v)
  have eA := congrArg₂ Functor.comp (congrArg₂ Functor.comp pR vR) dY'
  have eB := congrArg₂ Functor.comp (congrArg₂ Functor.comp uR pR') dY'
  have eZ := congrArg₂ Functor.comp uR (congrArg₂ Functor.comp dZ' pS')
  have eB' := congrArg₂ Functor.comp pR (congrArg₂ Functor.comp dY vS)
  have eC' := congrArg₂ Functor.comp (congrArg₂ Functor.comp dZ pS) vS
  have eD' := congrArg₂ Functor.comp dZ (congrArg₂ Functor.comp uS pS')
  have hl₁ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp pR vR) (congrArg₂ Functor.comp uR pR')
    (compactAmbient_heq R.X (detSfProperBaseChangeSquare p v)) dY'
  have hl₂ := compactWhiskerLeftHEq uR
    (congrArg₂ Functor.comp pR' dY') (congrArg₂ Functor.comp dZ' pS')
    (compactRho_heq a (pullback.snd p v))
  have hr₁ := compactWhiskerLeftHEq pR
    (congrArg₂ Functor.comp vR dY') (congrArg₂ Functor.comp dY vS)
    (compactIsoInvHEq (congrArg₂ Functor.comp dY vS)
      (congrArg₂ Functor.comp vR dY') (compactBalanced_heq a v))
  have hr₂ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp pR dY) (congrArg₂ Functor.comp dZ pS)
    (compactRho_heq a p) vS
  have hr₃ := compactWhiskerLeftHEq dZ
    (congrArg₂ Functor.comp pS vS) (congrArg₂ Functor.comp uS pS')
    (compactAmbient_heq S.X (detSfProperBaseChangeSquare p v))
  have hr₄ := compactWhiskerRightHEq
    (congrArg₂ Functor.comp dZ uS) (congrArg₂ Functor.comp uR dZ')
    (compactIsoHomHEq (congrArg₂ Functor.comp dZ uS)
      (congrArg₂ Functor.comp uR dZ') (compactBalanced_heq a (pullback.fst p v))) pS'
  have hl := compactCompHEq eA eB eZ hl₁ hl₂
  have hr := compactCompHEq eA eB' eZ hr₁
    (compactCompHEq eB' eC' eZ hr₂ (compactCompHEq eC' eD' eZ hr₃ hr₄))
  have h := normalizedScalarExchange (Λ := R.X) (Λ' := S.X) a.hom.hom
    (fun h => compactBalanced a h) (fun h => compactBalanced_normalized a h)
    (detSfProperBaseChangeSquare p v)
  beta_reduce at h
  have ht := hl.symm.trans ((heq_of_eq h).trans hr)
  exact eq_of_heq ht


private theorem compactNaturalPasting
    {A B C D E F A' B' C' D' E' F' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Category A'] [Category B'] [Category C'] [Category D'] [Category E'] [Category F']
    (J : A ⥤ B) (P : B ⥤ C) (V : C ⥤ D) (W : B ⥤ E) (Q : E ⥤ D)
    (U : A ⥤ F) (I : F ⥤ E)
    (J' : A' ⥤ B') (P' : B' ⥤ C') (V' : C' ⥤ D') (W' : B' ⥤ E') (Q' : E' ⥤ D')
    (U' : A' ⥤ F') (I' : F' ⥤ E')
    (TA : A ⥤ A') (TB : B ⥤ B') (TC : C ⥤ C')
    (TD : D ⥤ D') (TE : E ⥤ E') (TF : F ⥤ F')
    (lv : TC ⋙ V' ≅ V ⋙ TD) (lw : TB ⋙ W' ≅ W ⋙ TE) (lu : TA ⋙ U' ≅ U ⋙ TF)
    (bj : J ⋙ TB ≅ TA ⋙ J') (bi : I ⋙ TE ≅ TF ⋙ I')
    (r : P ⋙ TC ⟶ TB ⋙ P') (s : Q ⋙ TD ⟶ TE ⋙ Q')
    (b : P ⋙ V ⟶ W ⋙ Q) (b' : P' ⋙ V' ⟶ W' ⋙ Q')
    (o : J ⋙ W ≅ U ⋙ I) (o' : J' ⋙ W' ≅ U' ⋙ I')
    (hp : Functor.whiskerRight b TD ≫ Functor.whiskerLeft W s =
      Functor.whiskerLeft P lv.inv ≫ Functor.whiskerRight r V' ≫
        Functor.whiskerLeft TB b' ≫ Functor.whiskerRight lw.hom Q')
    (ho : Functor.whiskerRight bj.hom W' ≫ Functor.whiskerLeft TA o'.hom ≫
        Functor.whiskerRight lu.hom I' =
      Functor.whiskerLeft J lw.hom ≫ Functor.whiskerRight o.hom TE ≫
        Functor.whiskerLeft U bi.hom) :
    Functor.whiskerRight
          (Functor.whiskerLeft J b ≫ Functor.whiskerRight o.hom Q) TD ≫
        Functor.whiskerLeft U
          (Functor.whiskerLeft I s ≫ Functor.whiskerRight bi.hom Q') =
      Functor.whiskerLeft (J ⋙ P) lv.inv ≫
        Functor.whiskerRight
          (Functor.whiskerLeft J r ≫ Functor.whiskerRight bj.hom P') V' ≫
        Functor.whiskerLeft TA
          (Functor.whiskerLeft J' b' ≫ Functor.whiskerRight o'.hom Q') ≫
        Functor.whiskerRight lu.hom (I' ⋙ Q') := by
  ext K
  have hP := congr_app hp (J.obj K)
  have hO := congr_app ho K
  have hm := s.naturality (o.hom.app K)
  have hn := b'.naturality (bj.hom.app K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] at hP hO hm hn ⊢
  rw [reassoc_of% hm, reassoc_of% hP]
  conv_rhs => rw [reassoc_of% hn]
  simp only [← Q'.map_comp]
  rw [hO]



private theorem compactSupportBCFormula (R : ScalarSixRing.{u})
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f)
    (o : (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R.X (pullback.fst c.g v) ≅
      detSfDerivedPullback R.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory) :
    detSfCompactSupportBaseChangeComposite R.X f v c o =
      Functor.whiskerLeft (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory
          (detSfProperBaseChangeMap R.X c.g v) ≫
        Functor.whiskerRight o.hom (RootCoordinateFace.lower R.X (pullback.snd c.g v)) := by
  delta detSfCompactSupportBaseChangeComposite detSfCompactSupportExchangeData
    Functor.compactSupportExchangeData
  with_unfolding_all rfl


attribute [local implicit_reducible] CommMon.toMon Compactification.baseChange
  Compactification.ofIsPullback CondensedRing.moduleObjectDerivedPushforward

set_option maxHeartbeats 1600000 in
-- Use the same folded scalar comparison on both sides of the compact support map.
private theorem compactScalarMapSimple {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    scalarCompactSupportMap a j p =
      Functor.whiskerLeft (CondensedRing.openImmersionLowerShriek R.X j).mapDerivedCategory
          (scalarDirectImageMate a p) ≫
        Functor.whiskerRight (CondensedRing.compactOpenScalarIso a j).hom
          (RootCoordinateFace.lower S.X p) := by
  ext M
  simp only [CondensedRing.compactScalarMapFormula, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

set_option maxHeartbeats 1600000 in
-- Paste the proper and open equations before taking any components.
private theorem compactSupportExchangeNat {R S : ScalarSixRing.{u}} (a : R ⟶ S)
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f)
    (oR : (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R.X (pullback.fst c.g v) ≅
      detSfDerivedPullback R.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory)
    (hoR : oR.inv = detSfOpenBaseChangeMap R.X f v c)
    (oS : (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback S.X (pullback.fst c.g v) ≅
      detSfDerivedPullback S.X (pullback.fst f v) ⋙
        (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory)
    (hoS : oS.inv = detSfOpenBaseChangeMap S.X f v c) :
    Functor.whiskerRight (detSfCompactSupportBaseChangeComposite R.X f v c oR)
          (scalarSixChange a Y') ≫
        Functor.whiskerLeft (detSfDerivedPullback R.X (pullback.fst f v))
          (scalarCompactSupportMap a (c.baseChange v).i (c.baseChange v).g) =
      Functor.whiskerLeft (detSfCompactSupport R.X c) (compactExchangeLambda a v).inv ≫
        Functor.whiskerRight (scalarCompactSupportMap a c.i c.g) (detSfDerivedPullback S.X v) ≫
        Functor.whiskerLeft (scalarSixChange a X)
          (detSfCompactSupportBaseChangeComposite S.X f v c oS) ≫
        Functor.whiskerRight (compactExchangeLambda a (pullback.fst f v)).hom
          (detSfCompactSupport S.X (c.baseChange v)) := by
  rw [compactSupportBCFormula, compactSupportBCFormula,
    compactScalarMapSimple, compactScalarMapSimple]
  exact compactNaturalPasting
    (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory
    (RootCoordinateFace.lower R.X c.g) (detSfDerivedPullback R.X v)
    (detSfDerivedPullback R.X (pullback.fst c.g v))
    (RootCoordinateFace.lower R.X (pullback.snd c.g v))
    (detSfDerivedPullback R.X (pullback.fst f v))
    (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v).i).mapDerivedCategory
    (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory
    (RootCoordinateFace.lower S.X c.g) (detSfDerivedPullback S.X v)
    (detSfDerivedPullback S.X (pullback.fst c.g v))
    (RootCoordinateFace.lower S.X (pullback.snd c.g v))
    (detSfDerivedPullback S.X (pullback.fst f v))
    (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v).i).mapDerivedCategory
    (scalarSixChange a X) (scalarSixChange a c.Z) (scalarSixChange a Y)
    (scalarSixChange a Y') (scalarSixChange a (pullback c.g v))
    (scalarSixChange a (pullback f v))
    (compactExchangeLambda a v) (compactExchangeLambda a (pullback.fst c.g v))
    (compactExchangeLambda a (pullback.fst f v))
    (CondensedRing.compactOpenScalarIso a c.i)
    (CondensedRing.compactOpenScalarIso a (c.baseChange v).i)
    (scalarDirectImageMate a c.g) (scalarDirectImageMate a (pullback.snd c.g v))
    (detSfProperBaseChangeMap R.X c.g v) (detSfProperBaseChangeMap S.X c.g v) oR oS
    (compactProperNatTransport a c.g v) (compactOpenExchangeNat a f v c oR hoR oS hoS)



private theorem compactEvaluateExchange
    {A B C D E F G H : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    (P : A ⥤ B) (Q : C ⥤ D) (P' : E ⥤ F) (Q' : G ⥤ H)
    (U : A ⥤ C) (V : B ⥤ D) (U' : E ⥤ G) (V' : F ⥤ H)
    (T : A ⥤ E) (T' : C ⥤ G) (S : B ⥤ F) (S' : D ⥤ H)
    (s : P ⋙ S ⟶ T ⋙ P') (s' : Q ⋙ S' ⟶ T' ⋙ Q')
    (b : P ⋙ V ⟶ U ⋙ Q) (b' : P' ⋙ V' ⟶ U' ⋙ Q')
    (lv : S ⋙ V' ≅ V ⋙ S') (lu : T ⋙ U' ≅ U ⋙ T')
    (h : Functor.whiskerRight b S' ≫ Functor.whiskerLeft U s' =
      Functor.whiskerLeft P lv.inv ≫ Functor.whiskerRight s V' ≫
        Functor.whiskerLeft T b' ≫ Functor.whiskerRight lu.hom Q') (K : A) :
    S'.map (b.app K) ≫ s'.app (U.obj K) =
      lv.inv.app (P.obj K) ≫ V'.map (s.app K) ≫ b'.app (T.obj K) ≫
        Q'.map (lu.hom.app K) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using congr_app h K

set_option maxHeartbeats 1600000 in
-- Evaluate the pasted natural transformation on the constructible input.
/-- Compact-support scalar/exchange compatibility, using the very proper/open maps
specified by the compact-support dependencies. Each normalized open isomorphism
has inverse the published unit/square/counit map. The equation holds on every
compactification and its literal pullback, hence on the chosen functors after
canonical compactification comparisons. It is natural in the Dctf input.
Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/
lem-fix-operation-reduction.proof.md, paragraphs 2--3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence).

Proof: (5) For an open Cartesian square, the inverse of the scalar open comparison
is the open mate of inverse lambda: transpose again under scalar extension and
restriction to obtain the same identity on actions. The triangles cancel the
inserted units/counits. Mate pasting applied to the pullback cube then gives
open scalar/exchange compatibility.
(6) The proper scalar comparison is the geometric mate of the inverse of the
scalar-six pullback identification. Scalar-six derived pullback normalization
identifies it with the same balanced map lambda: transpose under the scalar
adjunction, where both are the identity-on-sections restriction square.
Uniqueness of transposition identifies their proper mates.
(7) Expand compact-support exchange as proper exchange followed by proper image
of open exchange, and scalarCompactSupportMap as proper scalar mate followed
by proper image of the open scalar comparison. Naturality moves the open
comparison through the proper mate. Apply the ordinary rectangle to the proper
square at j_!K, then the open square equality of (5). Naturality of proper
exchange gives the other route. Cancel only lambda_v.
(8) Compactification independence and composition of the scalar comparisons,
and compact-support exchange compatibility with the canonical compactification
comparisons, transport the equation to the specified functors. For pasting,
expand the proper/open factors; their mate-pasting equations give the outer
square, and the intermediate compactification comparisons cancel. All these
formulas are used only for the listed arrows, finite cd field and Dctf inputs. -/
theorem condensedScalarCompactExchangeCoherence
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : BaseFieldFiniteCD ell k)
    {R S : ScalarSixRing.{u}} (a : R ⟶ S) (_ha : ListedCoefficientMap ell a)
    {X Y Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f.left)
    (oR : (CondensedRing.openImmersionLowerShriek R.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback R.X (pullback.fst c.g v.left) ≅
      detSfDerivedPullback R.X (pullback.fst f.left v.left) ⋙
        (CondensedRing.openImmersionLowerShriek R.X (c.baseChange v.left).i).mapDerivedCategory)
    (_hoR : oR.inv = detSfOpenBaseChangeMap R.X f.left v.left c)
    (oS : (CondensedRing.openImmersionLowerShriek S.X c.i).mapDerivedCategory ⋙
        detSfDerivedPullback S.X (pullback.fst c.g v.left) ≅
      detSfDerivedPullback S.X (pullback.fst f.left v.left) ⋙
        (CondensedRing.openImmersionLowerShriek S.X (c.baseChange v.left).i).mapDerivedCategory)
    (_hoS : oS.inv = detSfOpenBaseChangeMap S.X f.left v.left c) :
    ∀ K : ConstantModelConstructibleFiniteTor R.X X.left,
      (scalarSixChange a Y'.left).map
          ((detSfCompactSupportBaseChangeComposite R.X f.left v.left c oR).app K.obj) ≫
        (scalarCompactSupportMap a (c.baseChange v.left).i
          (c.baseChange v.left).g).app
            ((detSfDerivedPullback R.X (pullback.fst f.left v.left)).obj K.obj) =
      (compactExchangeLambda a v.left).inv.app ((detSfCompactSupport R.X c).obj K.obj) ≫
        (detSfDerivedPullback S.X v.left).map
          ((scalarCompactSupportMap a c.i c.g).app K.obj) ≫
        (detSfCompactSupportBaseChangeComposite S.X f.left v.left c oS).app
          ((scalarSixChange a X.left).obj K.obj) ≫
        (detSfCompactSupport S.X (c.baseChange v.left)).map
          ((compactExchangeLambda a (pullback.fst f.left v.left)).hom.app K.obj) := by
  intro K
  have hK := compactEvaluateExchange
    (detSfCompactSupport R.X c) (detSfCompactSupport R.X (c.baseChange v.left))
    (detSfCompactSupport S.X c) (detSfCompactSupport S.X (c.baseChange v.left))
    (detSfDerivedPullback R.X (pullback.fst f.left v.left)) (detSfDerivedPullback R.X v.left)
    (detSfDerivedPullback S.X (pullback.fst f.left v.left)) (detSfDerivedPullback S.X v.left)
    (scalarSixChange a X.left) (scalarSixChange a (pullback f.left v.left))
    (scalarSixChange a Y.left) (scalarSixChange a Y'.left)
    (scalarCompactSupportMap a c.i c.g)
    (scalarCompactSupportMap a (c.baseChange v.left).i (c.baseChange v.left).g)
    (detSfCompactSupportBaseChangeComposite R.X f.left v.left c oR)
    (detSfCompactSupportBaseChangeComposite S.X f.left v.left c oS)
    (compactExchangeLambda a v.left) (compactExchangeLambda a (pullback.fst f.left v.left))
    (compactSupportExchangeNat a f.left v.left c oR _hoR oS _hoS) K.obj
  -- The generic evaluation keeps the component formula folded. Its instance
  -- certificates are compared by congruence, using proof irrelevance explicitly.
  -- Normalize only the thin aliases and the strictly associative functor composites;
  -- leave all derived functors folded. The resulting proof is kernel checked.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let hp ← Lean.Meta.getLocalDeclFromUserName `hK
      let reduceBy (n : Lean.Name) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let lemmaExpr ← Lean.Meta.mkConstWithFreshMVarLevels n
        let (_, _, body) ← Lean.Meta.forallMetaTelescopeReducing
          (← Lean.Meta.inferType lemmaExpr)
        unless body.isAppOfArity ``Eq 3 do throwError "Expected a reduction equation"
        let args := body.getAppArgs
        unless ← Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq args[1]! e) do
          throwError "Reduction equation does not match the outer expression"
        let result ← Lean.instantiateMVars args[2]!
        if result.hasMVar then throwError "Unresolved reduction equation"
        return result
      let normalize (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let mut e ← Lean.instantiateMVars e
        for _ in [:16] do
          e := e.consumeMData.headBeta
          let name := e.getAppFn.constName?
          if name == some ``ModuleRingedComparison.internalModules ||
              name == some ``Modules || name == some ``CommMon.toMon ||
              name == some ``AlgebraicGeometry.ProEtale.RootCoordinateFace.lower ||
              name == some ``CondensedRing.moduleObjectDerivedPushforward ||
              name == some ``CondensedRing.detSfCompactSupport ||
              name == some ``CondensedRing.rightDerivedLowerShriekOfCompactification ||
              name == some ``GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall ||
              name == some ``GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall ||
              name == some ``ProEtale.sheafMonoidalCategory then
            if let some e' ← Lean.Meta.unfoldDefinition? e then
              e ← Lean.instantiateMVars e'
              continue
          if name == some ``Functor.comp then
            let args := e.getAppArgs
            let idx := args.size - 2
            let fnName := args[idx]!.getAppFn.constName?
            if fnName == some ``CondensedRing.detSfCompactSupport ||
                fnName == some ``CondensedRing.rightDerivedLowerShriekOfCompactification then
              if let some f' ← Lean.Meta.unfoldDefinition? args[idx]! then
                e := Lean.mkAppN e.getAppFn (args.set! idx f')
                continue
            if fnName == some ``Functor.comp then
              e ← reduceBy ``Functor.assoc e
              continue
          if name == some ``NatTrans.app then
            let args := e.getAppArgs
            let natName := args[args.size - 2]!.getAppFn.constName?
            let rewriteName : Option Lean.Name :=
              if natName == some ``Functor.whiskerLeft then some ``Functor.whiskerLeft_app
              else if natName == some ``Functor.whiskerRight then some ``Functor.whiskerRight_app
              else if natName == some ``CategoryStruct.comp then some ``NatTrans.comp_app
              else none
            if let some rewriteName := rewriteName then
              e ← reduceBy rewriteName e
              continue
          let args := e.getAppArgs
          if name == some ``Functor.obj || name == some ``Functor.map then
            let offset := if name == some ``Functor.obj then 2 else 4
            if args.size < offset then break
            let idx := args.size - offset
            let fnName := args[idx]!.getAppFn.constName?
            if fnName == some ``CondensedRing.detSfCompactSupport ||
                fnName == some ``CondensedRing.rightDerivedLowerShriekOfCompactification then
              if let some f' ← Lean.Meta.unfoldDefinition? args[idx]! then
                e := Lean.mkAppN e.getAppFn (args.set! idx f')
                continue
            if fnName == some ``Functor.comp || fnName == some ``Functor.id then
              let isId := fnName == some ``Functor.id
              let rewriteName : Lean.Name := if name == some ``Functor.obj then
                (if isId then ``Functor.id_obj else ``Functor.comp_obj)
                else (if isId then ``Functor.id_map else ``Functor.comp_map)
              try
                e ← reduceBy rewriteName e
                continue
              catch _ => pure ()
          break
        return e
      let source ← normalize hp.type
      let target ← normalize (← goal.getType)
      let mut pending := [(source, target, false)]
      let mut proofs : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr := {}
      let mut congruences : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem := {}
      for _ in [:100000] do
        if pending.isEmpty then break
        let (a, b, ready) := pending.head!
        pending := pending.tail!
        let a ← normalize a
        let b ← normalize b
        let key := (a, b)
        if proofs.contains key then continue
        if a == b then
          proofs := proofs.insert key (← Lean.Meta.mkHEqRefl a)
        else if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
          proofs := proofs.insert key (← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b])
        else
          let f := a.getAppFn
          let xs := a.getAppArgs
          let ys := b.getAppArgs
          unless f == b.getAppFn && xs.size == ys.size && !xs.isEmpty do
            throwError "Unsupported scalar congruence presentation"
          if !ready then
            pending := (a, b, true) :: pending
            for x in xs, y in ys do
              pending := (x, y, false) :: pending
          else
            let congr ← match congruences[(f, xs.size)]? with
              | some congr => pure congr
              | none => Lean.Meta.mkHCongrWithArity f xs.size
            congruences := congruences.insert (f, xs.size) congr
            let mut proof := congr.proof
            for i in [:xs.size] do
              let child := (← normalize xs[i]!, ← normalize ys[i]!)
              let some h := proofs[child]? | throwError "Missing scalar congruence proof"
              let h ← if congr.argKinds[i]! == .eq then Lean.Meta.mkEqOfHEq h else pure h
              proof := Lean.mkAppN proof #[xs[i]!, ys[i]!, h]
            proofs := proofs.insert key proof
      let key := (source, target)
      let some proof := proofs[key]? | throwError "Scalar congruence traversal unfinished"
      let eq ← Lean.Meta.mkEqOfHEq proof
      let proof ← Lean.Meta.mkAppM ``Eq.mp #[eq, hp.toExpr]
      if proof.hasSorry || proof.hasMVar then throwError "Unfinished scalar congruence proof"
      goal.assign proof

end AlgebraicGeometry.ProEtale.QuotientChange
