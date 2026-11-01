/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import all WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap

import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Canonical pullback comparisons for coordinate intersections -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] PurityFiniteSetting.Coefficient PurityFiniteSetting.Ring
  PurityFiniteSetting.coefficientCommRing PurityFiniteSetting.ringCommRing
  AffineLinePurity.Ring Scheme.finiteTateCoefficient
set_option allowUnsafeReducibility true in
attribute [local reducible] cupSingle PurityFiniteSetting.functorialCupCategory
  PurityFiniteSetting.functorialCupAbelian PurityFiniteSetting.functorialCupMonoidal
  PurityFiniteSetting.functorialCupHasDerived PurityFiniteSetting.functorialCupSource
  PurityFiniteSetting.functorialCupInverseImage PurityFiniteSetting.functorialCupConstant
  PurityFiniteSetting.functorialCupFullSupportIso

set_option allowUnsafeReducibility true in
attribute [local reducible] classSource PurityFiniteSetting.constant
  PurityFiniteSetting.constantEtale supportData

private theorem intersection_pullback_exists
    {S D X S' D' X' : Scheme.{u}} (i : S ⟶ X) (j : D ⟶ X)
    (i' : S' ⟶ X') (j' : D' ⟶ X') (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsClosedImmersion i'] [IsClosedImmersion j']
    (p : S' ⟶ S) (q : D' ⟶ D)
    (hi : IsPullback p i' i v) (hj : IsPullback q j' j v) :
    ∃ r : pullback i' j' ⟶ pullback i j,
      IsPullback r (cupIntersection i' j') (cupIntersection i j) v := by
  let r := pullback.map i' j' i j p q v hi.w.symm hj.w.symm
  have hr : r ≫ cupIntersection i j = cupIntersection i' j' ≫ v := by
    simp only [r, pullback.map, cupIntersection, ← Category.assoc, pullback.lift_fst]
    rw [Category.assoc, hi.w, ← Category.assoc]
  refine ⟨r, IsPullback.of_isLimit
    (c := PullbackCone.mk r (cupIntersection i' j') hr) ?_⟩
  let lift (s : PullbackCone (cupIntersection i j) v) : s.pt ⟶ pullback i' j' :=
    pullback.lift
      (hi.lift (s.fst ≫ pullback.fst i j) s.snd
        (by simpa only [cupIntersection, Category.assoc] using s.condition))
      (hj.lift (s.fst ≫ pullback.snd i j) s.snd (by
        rw [Category.assoc, ← pullback.condition]
        exact s.condition))
      (by simp only [IsPullback.lift_snd])
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · simp only [lift, r, pullback.map, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
    · simp only [lift, r, pullback.map, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, IsPullback.lift_fst]
  · intro s
    simp only [lift, cupIntersection, ← Category.assoc, pullback.lift_fst,
      IsPullback.lift_snd]
  · intro s m hm hn
    apply (cancel_mono (cupIntersection i' j')).mp
    exact hn.trans (by
      simp only [lift, cupIntersection, ← Category.assoc, pullback.lift_fst,
        IsPullback.lift_snd])

/-- Each individual coordinate divisor square is Cartesian.
Source: the coordinate zero-locus universal property
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: pullback sends the coordinate function to its namesake; apply the
Cartesian zero-locus theorem. -/
theorem divisor_pullback_exists {B' B : Scheme.{u}} (g : B' ⟶ B)
    (c : ℕ) (i : Fin c) :
    ∃ p : divisor B' c i ⟶ divisor B c i,
      IsPullback p (inclusion B' c i) (inclusion B c i) (spaceMap g c) := by
  have h : (spaceMap g c).appTop '' {iteratedAffineLine.coord B c i} =
      {iteratedAffineLine.coord B' c i} := by
    rw [Set.image_singleton]
    congr 1
    exact Scheme.Hom.toIteratedAffineLine_appTop_coord _ _ _
  exact ⟨_, Scheme.isPullback_zeroLocusSubschemeι (spaceMap g c) _ _ h⟩

/-- Partial intersections are preserved by base change.
Source: coordinate zero loci and the universal property of intersections
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: a variable pulls back to the corresponding variable, so each divisor square
is Cartesian. The empty intersection is the identity, and the universal property
of the intersection pullback gives the induction step. -/
theorem support_pullback_exists {B' B : Scheme.{u}} (g : B' ⟶ B)
    (c : ℕ) (is : List (Fin c)) :
    ∃ p : support B' c is ⟶ support B c is,
      IsPullback p (supportMap B' c is) (supportMap B c is) (spaceMap g c) := by
  induction is with
  | nil => exact ⟨spaceMap g c, IsPullback.id_vert _⟩
  | cons i is ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := divisor_pullback_exists g c i
    exact intersection_pullback_exists (supportMap B c is) (inclusion B c i)
      (supportMap B' c is) (inclusion B' c i) (spaceMap g c) p q hp hq

private theorem normalized_source_map_square
    {C D : Type*} [Category C] [Category D] (U : C ⥤ D)
    {A S T : C} {A' S' T' : D} (ρS : A ⟶ S) (ρT : A ⟶ T)
    (ρS' : A' ⟶ S') (ρT' : A' ⟶ T') (f : S ⟶ T) (f' : S' ⟶ T')
    (eS : U.obj S ≅ S') (eT : U.obj T ≅ T') (eA : U.obj A ≅ A')
    (hf : ρS ≫ f = ρT) (_hf' : ρS' ≫ f' = ρT')
    (hS : U.map ρS ≫ eS.hom = eA.hom ≫ ρS')
    (hT : U.map ρT ≫ eT.hom = eA.hom ≫ ρT')
    (unique : ∀ b : S' ⟶ T', ρS' ≫ b = ρT' → b = f') :
    U.map f ≫ eT.hom = eS.hom ≫ f' := by
  have h : eS.inv ≫ U.map f ≫ eT.hom = f' := by
    apply unique
    apply (cancel_epi eA.hom).mp
    rw [← Category.assoc eA.hom ρS', ← hS]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← U.map_comp_assoc, hf, hT]
  rw [← h, Iso.hom_inv_id_assoc]

private theorem source_map_square (Q : PurityFiniteSetting.{u})
    {Z S X Z' S' X' : Scheme.{u}}
    (i : Z ⟶ X) (j : S ⟶ X) (i' : Z' ⟶ X') (j' : S' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsClosedImmersion i'] [IsClosedImmersion j']
    (v : X' ⟶ X) (p : Z' ⟶ Z) (q : S' ⟶ S)
    (si : ChosenCartesianSquare p i' i v) (sj : ChosenCartesianSquare q j' j v)
    (h : S ⟶ Z) (hh : h ≫ i = j) (h' : S' ⟶ Z') (hh' : h' ≫ i' = j') :
    (Q.functorialCupInverseImage true v).map
        (Q.functorialCupSupportMap true i j h hh) ≫
        (Q.functorialCupExchange true j j' v q sj).hom =
      (Q.functorialCupExchange true i i' v p si).hom ≫
        Q.functorialCupSupportMap true i' j' h' hh' := by
  apply normalized_source_map_square
    (Q.functorialCupInverseImage true v)
    (Q.functorialCupRestriction true i) (Q.functorialCupRestriction true j)
    (Q.functorialCupRestriction true i') (Q.functorialCupRestriction true j')
    (Q.functorialCupSupportMap true i j h hh)
    (Q.functorialCupSupportMap true i' j' h' hh')
    (Q.functorialCupExchange true i i' v p si)
    (Q.functorialCupExchange true j j' v q sj)
    (Q.functorialCupConstantPullback true v)
  · exact (Q.functorialCupSupportMap_existsUnique true i j h hh).choose_spec.1
  · exact (Q.functorialCupSupportMap_existsUnique true i' j' h' hh').choose_spec.1
  · exact (Q.functorialCupExchange_existsUnique true i i' v p si).choose_spec.1
  · exact (Q.functorialCupExchange_existsUnique true j j' v q sj).choose_spec.1
  · intro b hb
    exact (Q.functorialCupSupportMap_existsUnique true i' j' h' hh').unique hb
      (Q.functorialCupSupportMap_existsUnique true i' j' h' hh').choose_spec.1

private theorem pullbackSingle_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X : Scheme.{u}} (v : X' ⟶ X)
    {S T : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)}
    {S' T' : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} A)}
    (f : S ⟶ T) (f' : S' ⟶ T')
    (eS : (upperStar (ModuleCat.{u + 1} A) v).obj S ≅ S')
    (eT : (upperStar (ModuleCat.{u + 1} A) v).obj T ≅ T')
    (hf : (upperStar (ModuleCat.{u + 1} A) v).map f ≫ eT.hom = eS.hom ≫ f') :
    (inverseImage A v).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
        (pullbackSingle A v T T' eT).hom =
      (pullbackSingle A v S S' eS).hom ≫
        (DerivedCategory.singleFunctor _ 0).map f' := by
  let V := upperStar (ModuleCat.{u + 1} A) v
  let a := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v
  let b := V.mapDerivedCategorySingleFunctor 0
  have ha := a.hom.naturality ((DerivedCategory.singleFunctor _ 0).map f)
  have hb := b.hom.naturality f
  dsimp only [a] at ha
  dsimp only [b, V, Functor.comp_map] at hb
  simp only [pullbackSingle, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  unfold inverseImage
  rw [reassoc_of% ha, reassoc_of% hb, ← Functor.map_comp, hf, Functor.map_comp]

/-- The map of literal partial intersections induced by base change.
Source: coordinate equations and finite intersections, blueprint proof Step 1
(blueprint: def-pur-coordinate-product-pullback-data). -/
def coordinateSupportMap {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ)
    (is : List (Fin c)) : support B' c is ⟶ support B c is :=
  (support_pullback_exists g c is).choose

/-- Every partial coordinate intersection has its canonical Cartesian square.
Source: coordinate equations and finite intersections, blueprint proof Step 1
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: each coordinate equation pulls back to the same coordinate. Its zero locus
is therefore Cartesian. Pullback preserves intersections by their universal
property. Induct on the list, starting from the identity support. -/
theorem coordinateSupport_isPullback {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ)
    (is : List (Fin c)) :
    IsPullback (coordinateSupportMap g c is) (supportMap B' c is)
      (supportMap B c is) (spaceMap g c) :=
  (support_pullback_exists g c is).choose_spec

/-- The specified square for pulling back a literal partial intersection.
Source: coordinate support universal property, blueprint proof Step 1
(blueprint: def-pur-coordinate-product-pullback-data). -/
def coordinateSupportSquare {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ)
    (is : List (Fin c)) :
    ChosenCartesianSquare (coordinateSupportMap g c is) (supportMap B' c is)
      (supportMap B c is) (spaceMap g c) where
  toCommSq := (coordinateSupport_isPullback g c is).toCommSq
  isoPullback := (coordinateSupport_isPullback g c is).isoPullback
  hom_fst := (coordinateSupport_isPullback g c is).isoPullback_hom_fst
  hom_snd := (coordinateSupport_isPullback g c is).isoPullback_hom_snd

/-- The normalized derived source comparison on a partial coordinate intersection.
Source: exact inverse image and the unit-normalized closed exchange
(blueprint: def-pur-coordinate-product-pullback-data). -/
def coordinateListSourcePullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) (is : List (Fin c)) :
    (inverseImage (setting P n).Coefficient (spaceMap g c)).obj
      (classSource P n B c is) ≅ classSource P n B' c is :=
  (inverseImage (setting P n).Coefficient (spaceMap g c)).mapIso
      (eqToIso (classSource_eq P n B c is)) ≪≫
    pullbackSingle (setting P n).Coefficient (spaceMap g c) _ _
      ((setting P n).functorialCupExchange true (supportMap B c is)
        (supportMap B' c is) (spaceMap g c) (coordinateSupportMap g c is)
        (coordinateSupportSquare g c is)) ≪≫
    (eqToIso (classSource_eq P n B' c is)).symm

/-- Restriction from the zero support to the literal full coordinate intersection.
Source: the definition of supportedClass
(blueprint: def-pur-coordinate-product-pullback-data). -/
def coordinateSupportTransport (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ classSource P n B c (List.finRange c) :=
  (cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec) ≫
    eqToHom (classSource_eq P n B c (List.finRange c)).symm

private theorem postcast_naturality {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A T W : C} {A' T' W' : D}
    (f : A ⟶ T) (f' : A' ⟶ T') (t : W ≅ T) (t' : W' ≅ T')
    (a : F.obj A ≅ A') (b : F.obj T ≅ T')
    (h : F.map f ≫ b.hom = a.hom ≫ f') :
    F.map (f ≫ t.inv) ≫ (F.mapIso t ≪≫ b ≪≫ t'.symm).hom =
      a.hom ≫ f' ≫ t'.inv := by
  simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.map_inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ t'.inv) h

set_option maxHeartbeats 8000000 in
-- Normalize concrete sheaf comparisons at the prescribed coefficient level.
/-- The full-support identification commutes with the normalized closed exchange.
Source: full-coordinate intersection and unit-normalized coefficient restriction
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: the two ordinary composites preserve the same restricted coefficient unit.
Uniqueness of the normalized support restriction identifies them. Naturality of
the exact derived single comparison then gives the displayed equation. -/
theorem coordinateSupportTransport_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    (inverseImage (setting P n).Coefficient (spaceMap g c)).map
        (coordinateSupportTransport P n B c) ≫
        (coordinateListSourcePullback P n g c (List.finRange c)).hom =
      (coordinateSourcePullback P n g c).hom ≫
        coordinateSupportTransport P n B' c := by
  have hs := source_map_square (setting P n) (zero B c)
    (supportMap B c (List.finRange c)) (zero B' c)
    (supportMap B' c (List.finRange c)) (spaceMap g c) g
    (coordinateSupportMap g c (List.finRange c)) (zeroSquare g c)
    (coordinateSupportSquare g c (List.finRange c))
    (supportIso B c).hom (supportIso_existsUnique B c).exists.choose_spec
    (supportIso B' c).hom (supportIso_existsUnique B' c).exists.choose_spec
  have h := pullbackSingle_naturality (setting P n).Coefficient (spaceMap g c)
    _ _ ((setting P n).functorialCupExchange true (zero B c) (zero B' c)
      (spaceMap g c) g (zeroSquare g c))
    ((setting P n).functorialCupExchange true (supportMap B c (List.finRange c))
      (supportMap B' c (List.finRange c)) (spaceMap g c)
      (coordinateSupportMap g c (List.finRange c))
      (coordinateSupportSquare g c (List.finRange c))) hs
  have h' := postcast_naturality
    (inverseImage (setting P n).Coefficient (spaceMap g c)) _ _
    (eqToIso (classSource_eq P n B c (List.finRange c)))
    (eqToIso (classSource_eq P n B' c (List.finRange c))) _ _ h
  with_unfolding_all exact h'

set_option maxHeartbeats 8000000 in
-- Normalize concrete sheaf comparisons at the prescribed coefficient level.
/-- Pullback preserves the empty coordinate product and its normalized unit.
Source: the identity support and exact single comparison
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: the closed restriction for the identity immersion is inverse to the direct
image identity comparison. Substitute this normalization into the exchange
normalization and cancel these isomorphisms. Naturality of the exact single
comparison yields the derived equation. -/
theorem coordinateProduct_nil_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (inverseImage (setting P n).Coefficient (spaceMap g c)).map
        (product P n B aB c []) ≫
        (unitPullback P n (spaceMap g c)).hom =
      (coordinateListSourcePullback P n g c []).hom ≫
        product P n B' (g ≫ aB) c [] := by
  let Q := setting P n
  let X := iteratedAffineLine B c
  let X' := iteratedAffineLine B' c
  let v := spaceMap g c
  let U := Q.functorialCupInverseImage true v
  let e := Q.functorialCupExchange true (𝟙 X) (𝟙 X') v
    (coordinateSupportMap g c []) (coordinateSupportSquare g c [])
  let f := Q.functorialCupFullSupportIso true X
  let f' := Q.functorialCupFullSupportIso true X'
  have he := (Q.functorialCupExchange_existsUnique true (𝟙 X) (𝟙 X') v
    (coordinateSupportMap g c []) (coordinateSupportSquare g c [])).choose_spec.1
  change U.map (Q.functorialCupRestriction true (𝟙 X)) ≫ e.hom =
    (Q.functorialCupConstantPullback true v).hom ≫
      Q.functorialCupRestriction true (𝟙 X') at he
  rw [PurityFiniteSetting.restriction_full, PurityFiniteSetting.restriction_full] at he
  have hs : U.map f.hom ≫ (Q.functorialCupConstantPullback true v).hom =
      e.hom ≫ f'.hom := by
    apply (cancel_epi (U.map f.inv)).mp
    rw [← U.map_comp_assoc, f.inv_hom_id, U.map_id, Category.id_comp]
    exact (by simpa only [U, e, f, f', Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun t ↦ t ≫ f'.hom) he.symm)
  have h := pullbackSingle_naturality Q.Coefficient v f.hom f'.hom e
    (Q.frameConstantPullback v) hs
  have hprod : product P n B aB c [] = (cupSingle Q X).map f.hom := by
    with_unfolding_all change (𝟙 _ ≫ _) = _
    exact Category.id_comp _
  have hprod' : product P n B' (g ≫ aB) c [] = (cupSingle Q X').map f'.hom := by
    with_unfolding_all change (𝟙 _ ≫ _) = _
    exact Category.id_comp _
  have hsource : (coordinateListSourcePullback P n g c []).hom =
      (pullbackSingle Q.Coefficient v _ _ e).hom := by
    with_unfolding_all change
      (inverseImage Q.Coefficient v).map (𝟙 _) ≫
        (pullbackSingle Q.Coefficient v _ _ e).hom ≫ 𝟙 _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hunit : (unitPullback P n v).hom =
      (pullbackSingle Q.Coefficient v _ _ (Q.frameConstantPullback v)).hom := by
    with_unfolding_all change
      (inverseImage Q.Coefficient v).map (𝟙 _) ≫
        (pullbackSingle Q.Coefficient v _ _ (Q.frameConstantPullback v)).hom ≫ 𝟙 _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [hprod, hprod', hsource, hunit]
  with_unfolding_all exact h

/-- The specified supported class is the full list product with its support transport.
Source: definition of supportedClass
(blueprint: def-pur-coordinate-product-pullback-data).
Proof: expand the cached generic composite and the support transport. -/
theorem supportedClass_transport (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    supportedClass P n B aB c =
      coordinateSupportTransport P n B c ≫ product P n B aB c (List.finRange c) ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c))
          (@List.length_finRange c)) := by
  unfold supportedClass coordinateSupportedCompose coordinateSupportTransport
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.ProEtale.AffineZeroPurity
