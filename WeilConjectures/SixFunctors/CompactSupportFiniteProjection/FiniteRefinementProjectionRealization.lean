/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRefinementAmbientNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-! # Realization of the two endpoints of a finite refinement square

Source: the refinement calculation in fix-prop-projection-formula.proof.md,
steps 4 and 7 of lem-sf-projection-refinement-descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000

attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open RefinementProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local implicit_reducible] realization sixFunctorFiniteRealization tensor fixedTensor
attribute [local irreducible] ProEtale.derivedTensor derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp Functor.mapDerivedCategory Functor.rightDerivedFunctor
  properOpenMate

private theorem witness_support_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (V : C ⥤ D) (U : B ⥤ D) (F : A ⥤ C)
    (α : R.functor ⋙ U ≅ F ⋙ V) {K : B} {H : A}
    (e : H ≅ R.inverse.obj K) {a : D} (b : a ≅ U.obj K) :
    (b ≪≫ U.mapIso (R.functor.mapIso e ≪≫ R.counitIso.app K).symm ≪≫ α.app H).hom ≫
        V.map (F.map e.hom) =
      (b ≪≫ U.mapIso (R.counitIso.app K).symm ≪≫ α.app (R.inverse.obj K)).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  congr 1
  have hn : U.map (R.functor.map e.hom) ≫ α.hom.app (R.inverse.obj K) =
      α.hom.app H ≫ V.map (F.map e.hom) := α.hom.naturality e.hom
  rw [← hn]
  simp only [← U.map_comp_assoc, ← R.functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem inverse_unit_square
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {a b : B} {c d : A} (s : a ≅ R.functor.obj c) (t : b ≅ R.functor.obj d)
    (q : b ⟶ a) (k : d ⟶ c) (h : q ≫ s.hom = t.hom ≫ R.functor.map k) :
    R.inverse.map q ≫
        (R.inverse.map s.hom ≫ R.unitIso.inv.app c) =
      (R.inverse.map t.hom ≫ R.unitIso.inv.app d) ≫ k := by
  rw [← Category.assoc, ← R.inverse.map_comp, h, R.inverse.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.id_map] using
    congrArg (R.inverse.map t.hom ≫ ·) (R.unitIso.inv.naturality k)

private theorem retained_origin
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X) :
    ∃ O : ProEtale.RefinementFiniteLevelOrigin C.l E n hn X.obj.left,
      Nonempty (ProEtale.refinementFiniteLevelFixedObject C.l E n hn X.obj.left O ≅
        (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) := by
  classical
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left
  obtain ⟨a, ha⟩ := K.property.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X.obj.left A).2.2.1
    K.obj).mpr ⟨K.property.2, min a b, b, min_le_right _ _, hv⟩
  obtain ⟨c, d, _, hvan⟩ := L.property.2
  let LP : DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    ⟨L.obj, ⟨c, (DerivedCategory.isGE_iff L.obj c).2
      (fun i hi ↦ hvan i (Or.inl hi))⟩⟩
  let : TopologicalSpace (ULift.{u + 1} A) := ⊥
  let := discreteTopology_bot (ULift.{u + 1} A)
  let O : ProEtale.RefinementFiniteLevelOrigin C.l E n hn X.obj.left :=
    ⟨(ProEtale.finiteCoefficientComparison X.obj.left
      (ULift.{u + 1} A)).mapDerivedCategoryPlus.obj LP, ⟨LP, Iso.refl _⟩⟩
  have e : U.mapDerivedCategory.obj L.obj ≅ R.inverse.obj K.obj := by
    apply R.functor.preimageIso
    exact ((Functor.mapDerivedCategoryCompIso U
      (sfIntrinsicModuleEquivalence X.obj.left A).functor).app L.obj).symm ≪≫
        eL ≪≫ (R.counitIso.app K.obj).symm
  exact ⟨O, ⟨(ProEtale.refinementFixedWitnessIso X.obj.left
    (ULift.{u + 1} A) O).symm ≪≫ e⟩⟩

private theorem coefficient_prime_isUnit
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) : IsUnit (C.l : D.k) := by
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
    (fun h ↦ C.different ((Nat.prime_dvd_prime_iff_eq D.prime C.prime.out).1 h).symm)

private theorem finiteComparison_naturality
    (D : FiniteFieldDatum.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : SixFunctorSpace D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    {c d : Compactification f.hom.left} (r : c.Refinement d)
    {K L : ProEtale.ProperOpenDerived A X.obj.left} (a : K ⟶ L) :
    (ProEtale.ProperOpenPush A d.g).map ((ProEtale.ProperOpenShriek A d.i).map a) ≫
        RefinementProjection.finiteComparison D A r L =
      RefinementProjection.finiteComparison D A r K ≫
        (ProEtale.ProperOpenPush A c.g).map ((ProEtale.ProperOpenShriek A c.i).map a) := by
  let := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let Jc := ProEtale.ProperOpenShriek A c.i
  let Jd := ProEtale.ProperOpenShriek A d.i
  let Sr := ProEtale.ProperOpenPush A r.hom
  let Sd := ProEtale.ProperOpenPush A d.g
  let β := identityNormalize Jc Jd ((ordinary D A).S (𝟙 X)) Sr
    ((ordinary D A).sId X).inv
    (ProEtale.properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
      (r.i_hom.trans (Category.id_comp _).symm))
  let κ := Functor.whiskerRight β Sd ≫
    Functor.whiskerLeft Jc
      ((conjugateIsoEquiv
        ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) d.g).comp
          (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom))
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (r.hom ≫ d.g))
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom d.g)).hom) ≫
    Functor.whiskerLeft Jc (indexIso (ProEtale.ProperOpenPush A) r.hom_g).hom
  have h := κ.naturality a
  dsimp only [κ, β, identityNormalize, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map] at h
  simp only [Category.assoc] at h
  simpa only [RefinementProjection.finiteComparison, Category.assoc] using h

private theorem reverse_iso_square
    {A : Type*} [Category A] {a b c d : A}
    (ρ : a ≅ b) (s : a ≅ c) (t : b ≅ d) (m : c ≅ d)
    (h : ρ ≪≫ t = s ≪≫ m) : ρ.inv ≫ s.hom = t.hom ≫ m.inv := by
  apply (cancel_epi ρ.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hh := congrArg (fun e ↦ e.hom ≫ m.inv) h
  simpa only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

private theorem mapped_square_transport
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {a b : B} {c d c' d' : A}
    (q : b ⟶ a) (s : a ⟶ R.obj c) (t : b ⟶ R.obj d)
    (k : d ⟶ c) (u : c ⟶ c') (v : d ⟶ d') (k' : d' ⟶ c')
    (h : q ≫ s = t ≫ R.map k) (hn : k ≫ u = v ≫ k') :
    q ≫ (s ≫ R.map u) = (t ≫ R.map v) ≫ R.map k' := by
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← R.map_comp]
  rw [hn]

private theorem support_refinement
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        ((S.finite.comparison f c d).inv.app K) ≫ (supportRealization S f c K).hom =
      (supportRealization S f d K).hom ≫
        RY.functor.map (RefinementProjection.finiteComparison D A r (RX.inverse.obj K.obj)) := by
  classical
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) d
  obtain ⟨O, ⟨e⟩⟩ := retained_origin X K
  let w := RX.functor.mapIso e ≪≫ RX.counitIso.app K.obj
  let Wc := sixFunctorFiniteWitnessSupport C E n hn f c (S.finite.support f c)
    (S.finiteSupport f c) K O w
  let Wd := sixFunctorFiniteWitnessSupport C E n hn f d (S.finite.support f d)
    (S.finiteSupport f d) K O w
  have hc : Wc.hom ≫ RY.functor.map (F.map e.hom) =
      (supportRealization S f c K).hom := by
    exact witness_support_transport RX RY.functor (sixFunctorFiniteSupport D C E n hn f c)
      F (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c)
      e ((S.finiteSupport f c).app K)
  have hd : Wd.hom ≫ RY.functor.map (G.map e.hom) =
      (supportRealization S f d K).hom := by
    exact witness_support_transport RX RY.functor (sixFunctorFiniteSupport D C E n hn f d)
      G (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) d)
      e ((S.finiteSupport f d).app K)
  have h := reverse_iso_square (I.mapIso ((S.finite.comparison f c d).app K)) Wc Wd
    (RY.functor.mapIso (sixFunctorFiniteRefinementComparison C E n hn f
      (coefficient_prime_isUnit D C) r O))
    (S.finiteRefinementNormalization f (coefficient_prime_isUnit D C) c d r K O w)
  have hm : (sixFunctorFiniteRefinementComparison C E n hn f
      (coefficient_prime_isUnit D C) r O).inv =
      RefinementProjection.finiteComparison D A r
        (ProEtale.refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) := by
    let : TopologicalSpace A := ⊥
    let := discreteTopology_bot A
    exact refinementComparisonAtWitness_inv_eq D A r O
  dsimp only [Functor.mapIso_inv, Iso.app_inv] at h
  rw [hm] at h
  rw [← hc, ← hd]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← RY.functor.map_comp]
  simpa only [F, G, sfFixedCompactSupport, Functor.map_comp, Functor.comp_map,
    Category.assoc] using
    congrArg (Wd.hom ≫ ·) (congrArg RY.functor.map
      (finiteComparison_naturality D A r e.hom).symm)

/-- The recorded reverse refinement comparison realizes the same ambient proper/open
arrow at both endpoints of the projection square. This statement compares only
coefficient realizations, support comparisons and tensor functor actions; it makes
no assertion about a projection morphism.

Source: current blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, refinement sentence; steps 4 and 7 of
lem-sf-projection-refinement-descent, Stacks Tags 0F7B and 0F7G.
(blueprint: lem-sf-finite-refinement-projection-realization).

Proof: choose bounded constructible etale origins for K and for
K tensor f*L using finiteRing_constructibleDerived_origin and domains. These provide
actual origin witnesses in the canonical fixed-scalar presentation. The finite
refinement normalization, at each of those witnesses, expresses the forward
comparison as the proper compositor followed by the proper image of the inverse
proper/open comparison. Invert this equation. The site-normalization equation and
the refinement clause of proper/open interchange identify its proper/open factor
with the etale comparison transported to the pro-etale site. Constant-tower
evaluation in StrictTowerProperOpenCalculus identifies this transport with the
clopen-normalized ambient mate, inserting the normalized identity direct image.
The inverse proper compositor is the conjugate of pullback composition by the two
adjunctions.
Thus the reverse arrow is precisely RefinementProjection.finiteComparison, including
the transport along r.hom_g. Naturality removes the two chosen origin presentations.
Apply inverse coefficient realization and its unit naturality to the comparison at
K, tensor with the fixed presentation of L, and realize back; expanding
sourceComparison gives the first equation. At the tensor input, expand
targetComparison and use naturality of the ambient reverse comparison along the
canonical unit cancellation and fixedPullRealization. This gives the second equation.
No projection component is used or inverted. Bounded constructibility of the tensor
uses finite Tor only for L. Identity refinements, zero inputs and empty schemes obey
the same unit cancellations, so require no exclusions. -/
theorem refinement_realization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let TY := fixedTensor (C := C) (E := E) (n := n) Y
    let P := fixedDerivedPull (C := C) (E := E) (n := n) f
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let T := ((TX.obj (RX.inverse.obj K.obj)).obj (P.obj (RY.inverse.obj L.obj)))
    let rho := S.finite.comparison f c d
    ((intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        (((partialTensor S Y).map (rho.inv.app K)).app L) ≫
      (sourceComparison S f c K L).hom =
      (sourceComparison S f d K L).hom ≫ RY.functor.map
        ((TY.map (RefinementProjection.finiteComparison D A r
          (RX.inverse.obj K.obj))).app (RY.inverse.obj L.obj))) ∧
    ((intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        (rho.inv.app (((partialTensor S X).obj K).obj ((torPull S f).obj L))) ≫
      (targetComparison S f c K L).hom =
      (targetComparison S f d K L).hom ≫ RY.functor.map
        (RefinementProjection.finiteComparison D A r T)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let q := I.map ((S.finite.comparison f c d).inv.app K)
  let k := RefinementProjection.finiteComparison D A r (RX.inverse.obj K.obj)
  constructor
  · have h := inverse_unit_square RY (supportRealization S f c K)
      (supportRealization S f d K) q k (support_refinement S f c d r K)
    have ht := congrArg (fun a ↦ RY.functor.map
      ((TY.map a).app (RY.inverse.obj L.obj))) h
    simp only [Functor.map_comp, NatTrans.comp_app] at ht
    have hq : I.map (((partialTensor S Y).map
        ((S.finite.comparison f c d).inv.app K)).app L) =
        RY.functor.map ((TY.map (RY.inverse.map q)).app (RY.inverse.obj L.obj)) := by
      change ((tensor (C := C) (E := E) (n := n) (hn := hn) Y).map q).app L.obj ≫
        ((tensor (C := C) (E := E) (n := n) (hn := hn) Y).obj
          ((S.finite.support f c).obj K).obj).map (𝟙 L.obj) = _
      rw [CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
      rfl
    rw [hq]
    change RY.functor.map ((TY.map (RY.inverse.map q)).app (RY.inverse.obj L.obj)) ≫
        RY.functor.map ((TY.map (fixedSupportRealization S f c K).hom).app
          (RY.inverse.obj L.obj)) =
      RY.functor.map ((TY.map (fixedSupportRealization S f d K).hom).app
        (RY.inverse.obj L.obj)) ≫
        RY.functor.map ((TY.map k).app (RY.inverse.obj L.obj))
    simpa only [fixedSupportRealization, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, NatTrans.comp_app,
      Functor.id_obj, Functor.comp_obj, Category.assoc] using ht
  · let U := ((partialTensor S X).obj K).obj ((torPull S f).obj L)
    let H := (TX.obj (RX.inverse.obj K.obj)).obj
      (RX.inverse.obj ((S.finite.pull f).obj ⟨L.obj, L.property.1⟩).obj)
    let e := (RX.unitIso.app H).symm ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S f ⟨L.obj, L.property.1⟩)
    have h := support_refinement S f c d r U
    have hn := finiteComparison_naturality D A r e.hom
    dsimp only [targetComparison, projectionTensorTargetRealization,
      Iso.trans_hom, Functor.mapIso_hom]
    change I.map ((S.finite.comparison f c d).inv.app U) ≫
        ((supportRealization S f c U).hom ≫
          RY.functor.map ((sfFixedCompactSupport
            (Padic.coefficientExtensionRing C.l E n) c).map e.hom)) =
      ((supportRealization S f d U).hom ≫
          RY.functor.map ((sfFixedCompactSupport
            (Padic.coefficientExtensionRing C.l E n) d).map e.hom)) ≫
        RY.functor.map (RefinementProjection.finiteComparison D A r
          ((TX.obj (RX.inverse.obj K.obj)).obj
            ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
              (RY.inverse.obj L.obj))))
    refine mapped_square_transport RY.functor _ _ _ _ _ _ _ h ?_
    change RefinementProjection.finiteComparison D A r
        (RX.inverse.obj (RX.functor.obj H)) ≫
        (ProEtale.ProperOpenPush A c.g).map ((ProEtale.ProperOpenShriek A c.i).map e.hom) =
      (ProEtale.ProperOpenPush A d.g).map ((ProEtale.ProperOpenShriek A d.i).map e.hom) ≫
        RefinementProjection.finiteComparison D A r
          ((TX.obj (RX.inverse.obj K.obj)).obj
            ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
              (RY.inverse.obj L.obj)))
    exact hn.symm

end WeilConjectures.CompactSupportFiniteProjection
