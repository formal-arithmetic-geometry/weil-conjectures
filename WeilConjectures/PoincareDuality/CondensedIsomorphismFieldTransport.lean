/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-! # Isomorphism transport with direct condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.md, operations paragraph and first proof sentence
(blueprint: lem-pod-isomorphism-field-transport).

The ambient categories are the ordinary unbounded derived categories of internal modules.
The constructible categories are their native full subcategories. All comparison maps are
fixed by the existing pullback compositors, identity comparisons and scalar-adjunction mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical inverse-composition comparison, using the native derived compositor,
the equation g followed by its inverse, and the native identity comparison.
Source: the inverse-composition paragraph of the node
(blueprint: lem-pod-isomorphism-field-transport). -/
def isomorphismTransportCounit (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (g : X ≅ Y) :
    (upperStar Λ.X g.hom).leftDerivedFunctor ⋙ (upperStar Λ.X g.inv).leftDerivedFunctor ≅ 𝟭 _ :=
  (leftDerivedUpperStarComp Λ.X g.inv g.hom).symm ≪≫
    eqToIso (congrArg (fun f ↦ (upperStar Λ.X f).leftDerivedFunctor) g.inv_hom_id) ≪≫
      leftDerivedUpperStarId Λ.X Y

/-- A direct-condensed isomorphism transport package. The restriction uses the native
bounded-constructible predicate and its inclusion, and the unit and counit are fixed maps.
Exactness is stated in the ambient category, so no triangulated structure is imposed on
bounded constructible complexes for an arbitrary finite quotient ring.
Source: the second paragraph of the node
(blueprint: lem-pod-isomorphism-field-transport). -/
structure CondensedIsomorphismTransport (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y) where
  preserves : ∀ K, boundedConstructible (condensedRingObj Λ.X Y) K →
    boundedConstructible (condensedRingObj Λ.X X)
      (((upperStar Λ.X g.hom).leftDerivedFunctor).obj K)
  inverse_preserves : ∀ K, boundedConstructible (condensedRingObj Λ.X X) K →
    boundedConstructible (condensedRingObj Λ.X Y)
      (((upperStar Λ.X g.inv).leftDerivedFunctor).obj K)
  equivalence : BoundedConstructible (condensedRingObj Λ.X Y) ≌
    BoundedConstructible (condensedRingObj Λ.X X)
  forward : equivalence.functor ⋙ (boundedConstructible (condensedRingObj Λ.X X)).ι ≅
    (boundedConstructible (condensedRingObj Λ.X Y)).ι ⋙
      (upperStar Λ.X g.hom).leftDerivedFunctor
  inverse : equivalence.inverse ⋙ (boundedConstructible (condensedRingObj Λ.X Y)).ι ≅
    (boundedConstructible (condensedRingObj Λ.X X)).ι ⋙
      (upperStar Λ.X g.inv).leftDerivedFunctor
  first_triangle : ∀ K,
    ((upperStar Λ.X g.hom).leftDerivedFunctor).map
        ((isomorphismTransportCounit Λ g).inv.app K) ≫
      (isomorphismTransportCounit Λ g.symm).hom.app
        (((upperStar Λ.X g.hom).leftDerivedFunctor).obj K) = 𝟙 _
  second_triangle : ∀ K,
    (isomorphismTransportCounit Λ g).inv.app
        (((upperStar Λ.X g.inv).leftDerivedFunctor).obj K) ≫
      ((upperStar Λ.X g.inv).leftDerivedFunctor).map
        ((isomorphismTransportCounit Λ g.symm).hom.app K) = 𝟙 _
  triangulated : ((upperStar Λ.X g.hom).leftDerivedFunctor).IsTriangulated
  inverse_triangulated : ((upperStar Λ.X g.inv).leftDerivedFunctor).IsTriangulated
  tensor_comparison : ∀ K M,
    IsIso (Functor.OplaxMonoidal.δ (upperStar Λ.X g.hom).leftDerivedFunctor K M)
  inverse_tensor_comparison : ∀ K M,
    IsIso (Functor.OplaxMonoidal.δ (upperStar Λ.X g.inv).leftDerivedFunctor K M)
  hom_comparison : ∀ K,
    IsIso (Functor.LaxMonoidal.ihomComparison
      ((upperStar Λ.X g.hom).leftDerivedFunctor) K).natTrans
  hom_natural_first : ∀ {K K'} (f : K' ⟶ K) M,
    (upperStar Λ.X g.hom).leftDerivedFunctor.map ((MonoidalClosed.pre f).app M) ≫
        (Functor.LaxMonoidal.ihomComparison
          (upperStar Λ.X g.hom).leftDerivedFunctor K').natTrans.app M =
      (Functor.LaxMonoidal.ihomComparison
        (upperStar Λ.X g.hom).leftDerivedFunctor K).natTrans.app M ≫
        (MonoidalClosed.pre ((upperStar Λ.X g.hom).leftDerivedFunctor.map f)).app
          ((upperStar Λ.X g.hom).leftDerivedFunctor.obj M)
  inverse_hom_comparison : ∀ K,
    IsIso (Functor.LaxMonoidal.ihomComparison
      ((upperStar Λ.X g.inv).leftDerivedFunctor) K).natTrans


/-- Conjugate the canonical scalar mate by the exact termwise pullback comparisons.
Source: the coefficient-change paragraph of the node
(blueprint: lem-pod-isomorphism-field-transport). -/
def isomorphismTransportScalarComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ.X f).leftDerivedFunctor ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ (upperStar Λ'.X f).leftDerivedFunctor :=
  Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom
      (scalarSixChange a X) ≫
    scalarSixPullHom a f ≫
      Functor.whiskerLeft (scalarSixChange a Y)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).inv

/-- The geometric-composition equation for the specified coefficient comparison.
Source: det-prop-scalar-six-pullback clause (1), as used in the node's last paragraph
(blueprint: lem-pod-isomorphism-field-transport). -/
def isomorphismTransportScalarComposition {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) : Prop :=
  ∀ K,
    (isomorphismTransportScalarComparison a (f ≫ h)).app K ≫
        (leftDerivedUpperStarComp Λ'.X f h).hom.app ((scalarSixChange a Z).obj K) =
      (scalarSixChange a X).map ((leftDerivedUpperStarComp Λ.X f h).hom.app K) ≫
        (isomorphismTransportScalarComparison a f).app
          (((upperStar Λ.X h).leftDerivedFunctor).obj K) ≫
        ((upperStar Λ'.X f).leftDerivedFunctor).map
          ((isomorphismTransportScalarComparison a h).app K)

/-- Scalar compatibility includes the specified maps for g, its inverse and both composites.
The comparison maps are natural transformations on all ordinary derived complexes.
Source: the last paragraph of the node
(blueprint: lem-pod-isomorphism-field-transport). -/
def IsomorphismTransportScalarCompatible {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (g : X ≅ Y) : Prop :=
  IsIso (isomorphismTransportScalarComparison a g.hom) ∧
    IsIso (isomorphismTransportScalarComparison a g.inv) ∧
    isomorphismTransportScalarComposition a g.inv g.hom ∧
    isomorphismTransportScalarComposition a g.hom g.inv

/-- Naturality in coefficient maps: the two canonical scalar mates paste through the
canonical derived scalar associator, with no coefficient-flatness hypothesis.
Source: det-prop-scalar-six-pullback clause (3) and the last paragraph of the node
(blueprint: lem-pod-isomorphism-field-transport). -/
def IsomorphismTransportScalarTower {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ K,
    (scalarSixTower a b X).hom.app (((upperStar Λ.X f).leftDerivedFunctor).obj K) ≫
        (isomorphismTransportScalarComparison (a ≫ b) f).app K =
      (scalarSixChange b X).map ((isomorphismTransportScalarComparison a f).app K) ≫
        (isomorphismTransportScalarComparison b f).app ((scalarSixChange a Y).obj K) ≫
        ((upperStar Λ''.X f).leftDerivedFunctor).map ((scalarSixTower a b Y).hom.app K)

/-- Bundle the existing continuous finite-field coefficient as a commutative ring object.
Source: the first paragraph of the node; det-def-sfb-condensed-ring
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportFieldRing (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : ScalarSixRing.{u} :=
  CommMon.mk (Profinite.continuousMapRingObj E)

/-- Bundle the existing finite-subextension-valued algebraic-closure coefficient.
Source: the first paragraph of the node; sk-def-sfb-qlbar-condensed
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportClosureRing (l : ℕ) [Fact l.Prime] : ScalarSixRing.{u} :=
  CommMon.mk (Profinite.padicAlgClRingObj l)

/-- Bundle the existing continuous integer coefficient, with no completion operation.
Source: the first and last paragraphs of the node; det-def-sfb-condensed-ring
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportIntegerRing (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : ScalarSixRing.{u} :=
  CommMon.mk (Profinite.padicIntegersRingObj l E)

/-- Bundle the existing positive quotient coefficient; n denotes exponent n + 1.
Source: the coefficient-map list in the node; def-pod-positive-quotient-coefficients
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportQuotientRing (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    ScalarSixRing.{u} :=
  CommMon.mk (Profinite.continuousMapRingObj (completedResidue l E π n))

/-- The existing finite-field inclusion, retaining its ring-homomorphism structure.
Source: the coefficient-map list in the node; sk-def-sfb-coefficient-change
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportFieldMap (l : ℕ) [Fact l.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    isomorphismTransportFieldRing.{u} l E ⟶ isomorphismTransportFieldRing l F :=
  CommMon.homMk (Mon.ofHom (Profinite.padicSubfieldRingObjMap l h))

/-- The existing finite-field-to-algebraic-closure inclusion, bundled without changing it.
Source: the coefficient-map list in the node; sk-def-sfb-coefficient-change
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportClosureMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    isomorphismTransportFieldRing.{u} l E ⟶ isomorphismTransportClosureRing l :=
  CommMon.homMk (Mon.ofHom (Profinite.padicSubfieldRingObjToPadicAlgCl l E))

/-- The existing integer-to-field inclusion, bundled as a commutative coefficient map.
Source: the coefficient-map list in the node; det-def-sfb-condensed-ring
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportIntegerMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    isomorphismTransportIntegerRing.{u} l E ⟶ isomorphismTransportFieldRing l E :=
  CommMon.homMk (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)))

/-- The existing positive quotient projection, bundled as a commutative coefficient map.
Source: the coefficient-map list in the node; def-pod-positive-quotient-coefficients
(blueprint: lem-pod-isomorphism-field-transport). -/
abbrev isomorphismTransportReductionMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    isomorphismTransportIntegerRing.{u} l E ⟶ isomorphismTransportQuotientRing l E π n :=
  CommMon.homMk (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (completedReduction l E π n)))

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] isomorphismTransportCounit leftDerivedUpperStarComp
  leftDerivedUpperStarId leftDerivedUpperStarIsoMapDerivedCategory

private theorem mapNatIsoInvHomId
    {C D E : Type*} [Category C] [Category D] [Category E]
    {G H : C ⥤ D} (e : G ≅ H) (F : D ⥤ E) (K : C) :
    F.map (e.inv.app K) ≫ F.map (e.hom.app K) = 𝟙 _ := by
  rw [← F.map_comp, e.inv_hom_id_app K, F.map_id]

private theorem mapNatIsoInvCompOfHomEq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {G H : C ⥤ D} (e : G ≅ H) (F : D ⥤ E) (K : C)
    {f : F.obj (G.obj K) ⟶ F.obj (H.obj K)} (h : f = F.map (e.hom.app K)) :
    F.map (e.inv.app K) ≫ f = 𝟙 _ := by
  rw [h]
  exact mapNatIsoInvHomId e F K

private theorem secondTriangleOfFirst
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (c : F ⋙ G ≅ 𝟭 C) (d : G ⋙ F ≅ 𝟭 D)
    (h : ∀ K, F.map (c.inv.app K) ≫ d.hom.app (F.obj K) = 𝟙 _) (K : D) :
    c.inv.app (G.obj K) ≫ G.map (d.hom.app K) = 𝟙 _ := by
  have : F.IsEquivalence := (CategoryTheory.Equivalence.mk F G c.symm d).isEquivalence_functor
  apply F.map_injective
  rw [F.map_comp, F.map_id]
  have hd : F.map (G.map (d.hom.app K)) = d.hom.app (F.obj (G.obj K)) := by
    apply (cancel_mono (d.hom.app K)).mp
    simpa only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] using
      d.hom.naturality (d.hom.app K)
  rw [hd]
  exact h (G.obj K)

private def conjugateSquare
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F D : A ⥤ B} {F' D' : A' ⥤ B'} (e : F ≅ D) (e' : F' ≅ D')
    (S : A ⥤ A') (T : B ⥤ B') (θ : D ⋙ T ⟶ S ⋙ D') : F ⋙ T ⟶ S ⋙ F' :=
  Functor.whiskerRight e.hom T ≫ θ ≫ Functor.whiskerLeft S e'.inv

private theorem conjugateSquare_comp
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {F D : B ⥤ C} {H E : A ⥤ B} {P Q : A ⥤ C}
    {F' D' : B' ⥤ C'} {H' E' : A' ⥤ B'} {P' Q' : A' ⥤ C'}
    (eF : F ≅ D) (eH : H ≅ E) (eP : P ≅ Q)
    (eF' : F' ≅ D') (eH' : H' ≅ E') (eP' : P' ≅ Q')
    (S : A ⥤ A') (T : B ⥤ B') (U : C ⥤ C')
    (tF : D ⋙ U ⟶ T ⋙ D') (tH : E ⋙ T ⟶ S ⋙ E') (tP : Q ⋙ U ⟶ S ⋙ Q')
    (c : P ≅ H ⋙ F) (d : Q ≅ E ⋙ D)
    (c' : P' ≅ H' ⋙ F') (d' : Q' ≅ E' ⋙ D') (K : A)
    (hc : c.hom.app K = eP.hom.app K ≫ d.hom.app K ≫
      D.map (eH.inv.app K) ≫ eF.inv.app (H.obj K))
    (hc' : c'.hom.app (S.obj K) = eP'.hom.app (S.obj K) ≫
      d'.hom.app (S.obj K) ≫ D'.map (eH'.inv.app (S.obj K)) ≫
        eF'.inv.app (H'.obj (S.obj K)))
    (ht : tP.app K ≫ d'.hom.app (S.obj K) =
      U.map (d.hom.app K) ≫ tF.app (E.obj K) ≫ D'.map (tH.app K)) :
    (conjugateSquare eP eP' S U tP).app K ≫ c'.hom.app (S.obj K) =
      U.map (c.hom.app K) ≫ (conjugateSquare eF eF' T U tF).app (H.obj K) ≫
        F'.map ((conjugateSquare eH eH' S T tH).app K) := by
  simp only [conjugateSquare, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, hc, hc', Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have cancelF : U.map (eF.inv.app (H.obj K)) ≫ U.map (eF.hom.app (H.obj K)) = 𝟙 _ := by
    rw [← U.map_comp, eF.inv_hom_id_app, U.map_id]
  rw [reassoc_of% cancelF, reassoc_of% ht]
  rw [reassoc_of% (tF.naturality (eH.inv.app K))]
  rw [← reassoc_of% (eF'.inv.naturality (T.map (eH.hom.app K)))]
  have cancelH : T.map (eH.inv.app K) ≫ T.map (eH.hom.app K) = 𝟙 _ := by
    rw [← T.map_comp, eH.inv_hom_id_app, T.map_id]
  rw [← D'.map_comp_assoc (T.map (eH.inv.app K)) (T.map (eH.hom.app K)),
    cancelH, D'.map_id, Category.id_comp]
  rw [← reassoc_of% (eF'.inv.naturality (tH.app K))]
  rw [← eF'.inv.naturality (eH'.inv.app (S.obj K))]

private def transportEquivalence (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y) :
    BoundedConstructible (condensedRingObj Λ.X Y) ≌
      BoundedConstructible (condensedRingObj Λ.X X) := by
  let P := boundedConstructible (condensedRingObj Λ.X Y)
  let Q := boundedConstructible (condensedRingObj Λ.X X)
  let F := Q.lift (P.ι ⋙ (upperStar Λ.X g.hom).leftDerivedFunctor)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ.X g.hom K.obj K.property)
  let G := P.lift (Q.ι ⋙ (upperStar Λ.X g.inv).leftDerivedFunctor)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ.X g.inv K.obj K.property)
  refine CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun K ↦ P.isoMk ((isomorphismTransportCounit Λ g).symm.app K.obj))
      (fun f ↦ ?_))
    (NatIso.ofComponents (fun K ↦ Q.isoMk ((isomorphismTransportCounit Λ g.symm).app K.obj))
      (fun f ↦ ?_))
  · apply P.hom_ext
    exact (isomorphismTransportCounit Λ g).inv.naturality f.hom
  · apply Q.hom_ext
    exact (isomorphismTransportCounit Λ g.symm).hom.naturality f.hom

set_option maxHeartbeats 2000000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
private theorem transportCounitMap (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y) (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))) :
    (isomorphismTransportCounit Λ g.symm).hom.app
        ((upperStar Λ.X g.hom).leftDerivedFunctor.obj K) =
      (upperStar Λ.X g.hom).leftDerivedFunctor.map
        ((isomorphismTransportCounit Λ g).hom.app K) := by
  have leftUnit {r : X ⟶ X} (e : r = 𝟙 X) :
      (leftDerivedUpperStarComp Λ.X r g.hom).hom.app K ≫
        eqToHom (congrArg
          (fun r : X ⟶ X ↦ (upperStar Λ.X r).leftDerivedFunctor.obj
            ((upperStar Λ.X g.hom).leftDerivedFunctor.obj K)) e) ≫
        (leftDerivedUpperStarId Λ.X X).hom.app
          ((upperStar Λ.X g.hom).leftDerivedFunctor.obj K) =
      eqToHom (by rw [e, Category.id_comp]; rfl) := by
    subst e
    simpa using leftDerivedUpperStarComp_id_left_app Λ.X g.hom K
  have rightUnit {r : Y ⟶ Y} (e : r = 𝟙 Y) :
      (leftDerivedUpperStarComp Λ.X g.hom r).hom.app K ≫
        (upperStar Λ.X g.hom).leftDerivedFunctor.map
          (eqToHom (congrArg
            (fun r : Y ⟶ Y ↦ (upperStar Λ.X r).leftDerivedFunctor.obj K) e) ≫
            (leftDerivedUpperStarId Λ.X Y).hom.app K) =
      eqToHom (by rw [e, Category.comp_id]; rfl) := by
    subst e
    simpa using leftDerivedUpperStarComp_id_right_app Λ.X g.hom K
  have h := leftDerivedUpperStarComp_assoc_app Λ.X g.hom g.inv g.hom K
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ.X g.hom g.inv).hom.app
    ((upperStar Λ.X g.hom).leftDerivedFunctor.obj K)),
    ← cancel_epi ((leftDerivedUpperStarComp Λ.X (g.hom ≫ g.inv) g.hom).hom.app K)]
  simp only [isomorphismTransportCounit, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Iso.hom_inv_id_app_assoc]
  rw [leftUnit g.hom_inv_id, reassoc_of% h]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [rightUnit g.inv_hom_id]
  simp only [eqToHom_trans]

private theorem transportFirstTriangle (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))) :
    (upperStar Λ.X g.hom).leftDerivedFunctor.map
        ((isomorphismTransportCounit Λ g).inv.app K) ≫
      (isomorphismTransportCounit Λ g.symm).hom.app
        ((upperStar Λ.X g.hom).leftDerivedFunctor.obj K) = 𝟙 _ := by
  exact mapNatIsoInvCompOfHomEq (isomorphismTransportCounit Λ g)
    (upperStar Λ.X g.hom).leftDerivedFunctor K (transportCounitMap Λ g K)

private theorem transportSecondTriangle (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    (isomorphismTransportCounit Λ g).inv.app
        ((upperStar Λ.X g.inv).leftDerivedFunctor.obj K) ≫
      (upperStar Λ.X g.inv).leftDerivedFunctor.map
        ((isomorphismTransportCounit Λ g.symm).hom.app K) = 𝟙 _ := by
  exact secondTriangleOfFirst (isomorphismTransportCounit Λ g)
    (isomorphismTransportCounit Λ g.symm) (transportFirstTriangle Λ g) K

set_option maxHeartbeats 2000000 in
-- Keep the equivalence construction behind a theorem when synthesizing closed comparisons.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportIsEquivalence (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y) :
    (upperStar Λ.X g.hom).leftDerivedFunctor.IsEquivalence := by
  let e := CategoryTheory.Equivalence.mk
    (upperStar Λ.X g.hom).leftDerivedFunctor
    (upperStar Λ.X g.inv).leftDerivedFunctor
    (isomorphismTransportCounit Λ g).symm (isomorphismTransportCounit Λ g.symm)
  exact e.isEquivalence_functor

set_option maxHeartbeats 2000000 in
-- Isolate the equivalence instance from the fields that only use native functoriality.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportHomComparison (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (g : X ≅ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))) :
    IsIso (Functor.LaxMonoidal.ihomComparison
      (upperStar Λ.X g.hom).leftDerivedFunctor K).natTrans := by
  have : (upperStar Λ.X g.hom).leftDerivedFunctor.IsEquivalence :=
    transportIsEquivalence Λ g
  infer_instance

set_option maxHeartbeats 200000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
private theorem transportData (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (g : X ≅ Y) :
    Nonempty (CondensedIsomorphismTransport Λ g) := by
  exact ⟨{
    preserves := boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ.X g.hom
    inverse_preserves := boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ.X g.inv
    equivalence := transportEquivalence Λ g
    forward := Iso.refl _
    inverse := Iso.refl _
    first_triangle := transportFirstTriangle Λ g
    second_triangle := transportSecondTriangle Λ g
    triangulated := inferInstance
    inverse_triangulated := inferInstance
    tensor_comparison := fun _ _ ↦ inferInstance
    inverse_tensor_comparison := fun _ _ ↦ inferInstance
    hom_comparison := transportHomComparison Λ g
    inverse_hom_comparison := transportHomComparison Λ g.symm
    hom_natural_first := fun f M ↦
      Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app _ f M }⟩

set_option maxHeartbeats 2000000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportCompositor (Λ : ScalarSixRing.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z))) :
    (leftDerivedUpperStarComp Λ.X f h).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (f ≫ h)).hom.app K ≫
        (scalarSixPullComp Λ f h).hom.app K ≫
        (scalarSixPull Λ f).map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X h).inv.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv.app
          ((upperStar Λ.X h).leftDerivedFunctor.obj K) := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    scalarSixPullComp, scalarSixPull, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]

set_option maxHeartbeats 2000000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportScalarComposition (C : ScalarSixPullbackData.{u})
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) : isomorphismTransportScalarComposition a f h := by
  intro K
  have hc := C.composition a f h K
  simp only [C.thetaNormalization] at hc
  exact conjugateSquare_comp
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X h)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (f ≫ h))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X h)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X (f ≫ h))
    (scalarSixChange a Z) (scalarSixChange a Y) (scalarSixChange a X)
    (scalarSixPullHom a f) (scalarSixPullHom a h) (scalarSixPullHom a (f ≫ h))
    (leftDerivedUpperStarComp Λ.X f h) (scalarSixPullComp Λ f h)
    (leftDerivedUpperStarComp Λ'.X f h) (scalarSixPullComp Λ' f h) K
    (transportCompositor Λ f h K)
    (transportCompositor Λ' f h ((scalarSixChange a Z).obj K)) hc

set_option maxHeartbeats 2000000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportScalarIsIso (C : ScalarSixPullbackData.{u})
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (isomorphismTransportScalarComparison a f) := by
  have : IsIso (scalarSixPullHom a f) := by
    rw [← C.thetaNormalization a f]
    infer_instance
  dsimp only [isomorphismTransportScalarComparison]
  infer_instance

set_option maxHeartbeats 2000000 in
-- Native derived-functor expressions carry large exactness and monoidal instances.
set_option synthInstance.maxHeartbeats 200000 in
private theorem transportScalarTower (C : ScalarSixPullbackData.{u})
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsomorphismTransportScalarTower a b f := by
  intro K
  have h := C.tower a b f K
  simp only [C.thetaNormalization] at h
  dsimp only [isomorphismTransportScalarComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  erw [← reassoc_of% ((scalarSixTower a b X).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app K)), reassoc_of% h]
  erw [((leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).app
    ((scalarSixChange a Y).obj K)).map_inv_hom_id_assoc (scalarSixChange b X)]
  erw [← (leftDerivedUpperStarIsoMapDerivedCategory Λ''.X f).inv.naturality
    ((scalarSixTower a b Y).hom.app K)]
  simp only [scalarSixPull]

/-- Exact transport for direct condensed coefficients under any scheme isomorphism.
The fixed algebraic closure is represented by the native PadicAlgCl model. Finite fields
are its finite intermediate fields, so no finite field or embedding is excluded.

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.md, operations paragraph and first proof sentence; coefficient
compatibility uses det-prop-scalar-six-pullback clauses (1) and (3)
(blueprint: lem-pod-isomorphism-field-transport).

Proof:
1. Construct the ambient equivalence from the native derived compositors and identity
comparisons, using the two inverse equations of the scheme isomorphism.
2. The native bounded-constructible pullback theorem applies to every scheme morphism
and every commutative condensed coefficient ring. Its proof uses termwise exactness,
homology compatibility and preservation of module constructibility. Thus pullback
preserves bounded constructibility in both directions without separatedness or
k-linearity. Lift the functors and comparison isomorphisms to the native full subcategories.
3. Compose the native derived-pullback compositors with the inverse equations and identity
comparisons. Associativity and unitality give both triangle identities. Exact termwise
pullback preserves shifts and distinguished triangles. The native strong monoidal
structure identifies derived tensor products; its evaluation transpose gives the
internal-Hom comparison, invertible because the underlying functor is an equivalence.
Both variable naturality equations are those of the canonical closed comparison.
4. Apply the canonical scalar-adjunction mate to every listed coefficient map, including
non-flat finite reduction. Conjugate by the exact termwise comparisons. The geometric
composition equation gives compatibility with the inverse and both identity composites.
Scalar-tower pasting gives naturality in the coefficient maps, including the finite-field
and algebraic-closure inclusions and the composites through the integer coefficient.
-/
theorem isomorphismFieldTransportCondensed
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E))
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g : X ≅ Y) :
    Nonempty (CondensedIsomorphismTransport (isomorphismTransportFieldRing l E) g) ∧
      Nonempty (CondensedIsomorphismTransport (isomorphismTransportClosureRing l) g) ∧
      Nonempty (CondensedIsomorphismTransport (isomorphismTransportIntegerRing l E) g) ∧
      (∀ n : ℕ,
        Nonempty (CondensedIsomorphismTransport (isomorphismTransportQuotientRing l E π n) g) ∧
        IsomorphismTransportScalarCompatible (isomorphismTransportReductionMap l E π n) g) ∧
      IsomorphismTransportScalarCompatible (isomorphismTransportIntegerMap l E) g ∧
      IsomorphismTransportScalarCompatible (isomorphismTransportClosureMap l E) g ∧
      IsomorphismTransportScalarTower
        (isomorphismTransportIntegerMap l E) (isomorphismTransportClosureMap l E) g.hom ∧
      IsomorphismTransportScalarTower
        (isomorphismTransportIntegerMap l E) (isomorphismTransportClosureMap l E) g.inv ∧
      (∀ (F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
        Nonempty (CondensedIsomorphismTransport (isomorphismTransportFieldRing l F) g) ∧
        IsomorphismTransportScalarCompatible (isomorphismTransportFieldMap l h) g ∧
        IsomorphismTransportScalarTower
          (isomorphismTransportIntegerMap l E) (isomorphismTransportFieldMap l h) g.hom ∧
        IsomorphismTransportScalarTower
          (isomorphismTransportIntegerMap l E) (isomorphismTransportFieldMap l h) g.inv ∧
        IsomorphismTransportScalarTower
          (isomorphismTransportFieldMap l h) (isomorphismTransportClosureMap l F) g.hom ∧
        IsomorphismTransportScalarTower
          (isomorphismTransportFieldMap l h) (isomorphismTransportClosureMap l F) g.inv ∧
        (∀ (H : PadicAlgCl.FiniteIntermediateField l) (h' : F ≤ H),
          IsomorphismTransportScalarTower
            (isomorphismTransportFieldMap l h) (isomorphismTransportFieldMap l h') g.hom ∧
          IsomorphismTransportScalarTower
            (isomorphismTransportFieldMap l h) (isomorphismTransportFieldMap l h') g.inv)) := by
  obtain ⟨C⟩ := scalarSixPullbackData_exists
  have transport (Λ : ScalarSixRing.{u}) : Nonempty (CondensedIsomorphismTransport Λ g) :=
    transportData Λ g
  have compatible {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
      IsomorphismTransportScalarCompatible a g :=
    ⟨transportScalarIsIso C a g.hom, transportScalarIsIso C a g.inv,
      transportScalarComposition C a g.inv g.hom,
      transportScalarComposition C a g.hom g.inv⟩
  refine ⟨transport _, transport _, transport _, ?_, compatible _, compatible _,
    transportScalarTower C _ _ _, transportScalarTower C _ _ _, ?_⟩
  · intro n
    exact ⟨transport _, compatible _⟩
  · intro F h
    exact ⟨transport _, compatible _, transportScalarTower C _ _ _,
      transportScalarTower C _ _ _, transportScalarTower C _ _ _,
      transportScalarTower C _ _ _, fun H h' ↦
        ⟨transportScalarTower C _ _ _, transportScalarTower C _ _ _⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
