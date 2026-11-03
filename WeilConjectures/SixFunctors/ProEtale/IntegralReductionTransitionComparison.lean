/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.SixFunctors.ProEtale.IntegralPresentationEncoding
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalConeTower
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
public import WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

set_option linter.privateModule false

/-! # Transition compatibility for normalized integral comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension scalarReductionExtension scalarReductionCounit
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Lift the finite square by cancelling fully faithful ordinary restriction. -/
private theorem liftRestrictionSquare
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (U : D ⥤ C) (V : E ⥤ D) (W : E ⥤ C)
    (U' : D' ⥤ C') (V' : E' ⥤ D') (W' : E' ⥤ C')
    [U'.Full] [U'.Faithful]
    (F : C ⥤ C') (G : D ⥤ D') (H : E ⥤ E')
    (a : U ⋙ F ≅ G ⋙ U') (b : W ⋙ F ≅ H ⋙ W')
    (c : V ⋙ U ≅ W) (d : V' ⋙ U' ≅ W') :
    ∃ e : V ⋙ G ≅ H ⋙ V', ∀ N,
      F.map (c.hom.app N) ≫ b.hom.app N =
        a.hom.app (V.obj N) ≫ U'.map (e.hom.app N) ≫ d.hom.app (H.obj N) := by
  let z : (V ⋙ G) ⋙ U' ≅ (H ⋙ V') ⋙ U' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft V a.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c F ≪≫ b ≪≫
      Functor.isoWhiskerLeft H d.symm ≪≫ (Functor.associator _ _ _).symm
  let e : V ⋙ G ≅ H ⋙ V' :=
    Functor.fullyFaithfulCancelRight U' z
  refine ⟨e, ?_⟩
  intro N
  have he : U'.map (e.hom.app N) = z.hom.app N := by
    exact U'.map_preimage _
  rw [he]
  simp only [z, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]

/-- Exact localization preserves the lifted restriction compositor square. -/
private theorem liftDerivedRestrictionSquare
    {C D E C' D' E' : Type*}
    [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    [Category C'] [Abelian C'] [HasDerivedCategory C']
    [Category D'] [Abelian D'] [HasDerivedCategory D']
    [Category E'] [Abelian E'] [HasDerivedCategory E']
    (U : D ⥤ C) (V : E ⥤ D) (W : E ⥤ C)
    (U' : D' ⥤ C') (V' : E' ⥤ D') (W' : E' ⥤ C')
    [U'.Full] [U'.Faithful]
    (F : C ⥤ C') (G : D ⥤ D') (H : E ⥤ E')
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [U'.Additive] [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [V'.Additive] [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [W'.Additive] [PreservesFiniteLimits W'] [PreservesFiniteColimits W']
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits (V ⋙ U)] [PreservesFiniteColimits (V ⋙ U)]
    [PreservesFiniteLimits (V' ⋙ U')] [PreservesFiniteColimits (V' ⋙ U')]
    (a : U ⋙ F ≅ G ⋙ U') (b : W ⋙ F ≅ H ⋙ W')
    (c : V ⋙ U ≅ W) (d : V' ⋙ U' ≅ W') :
    ∃ e : V.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
        H.mapDerivedCategory ⋙ V'.mapDerivedCategory, ∀ K,
      F.mapDerivedCategory.map
          (((Functor.mapDerivedCategoryCompIso V U).symm ≪≫
            Functor.mapDerivedCategoryNatIso c).hom.app K) ≫
          ((Functor.mapDerivedCategoryCompIso W F).symm ≪≫
            Functor.mapDerivedCategoryNatIso b ≪≫
              Functor.mapDerivedCategoryCompIso H W').hom.app K =
        ((Functor.mapDerivedCategoryCompIso U F).symm ≪≫
          Functor.mapDerivedCategoryNatIso a ≪≫
            Functor.mapDerivedCategoryCompIso G U').hom.app (V.mapDerivedCategory.obj K) ≫
          U'.mapDerivedCategory.map (e.hom.app K) ≫
          ((Functor.mapDerivedCategoryCompIso V' U').symm ≪≫
            Functor.mapDerivedCategoryNatIso d).hom.app (H.mapDerivedCategory.obj K) := by
  obtain ⟨e, he⟩ := liftRestrictionSquare U V W U' V' W' F G H a b c d
  refine ⟨Functor.mapDerivedCategorySquareIso e, ?_⟩
  intro K
  have hq (Z : E) :
      F.map (c.inv.app Z) ≫ a.hom.app (V.obj Z) ≫ U'.map (e.hom.app Z) =
        b.hom.app Z ≫ d.inv.app (H.obj Z) := by
    have h := congrArg (fun k ↦ F.map (c.inv.app Z) ≫ k ≫ d.inv.app (H.obj Z)) (he Z)
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id,
      Category.id_comp, Iso.hom_inv_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h.symm
  have h := Functor.exactSquare_comp_forward V U W V' U' W' H G F
    e a b c.symm d.symm hq K
  let cd := (Functor.mapDerivedCategoryCompIso V U).symm ≪≫
    Functor.mapDerivedCategoryNatIso c
  let dd := (Functor.mapDerivedCategoryCompIso V' U').symm ≪≫
    Functor.mapDerivedCategoryNatIso d
  have h' : F.mapDerivedCategory.map (cd.inv.app K) ≫
      (Functor.mapDerivedCategorySquareIso a).hom.app (V.mapDerivedCategory.obj K) ≫
      U'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e).hom.app K) =
      (Functor.mapDerivedCategorySquareIso b).hom.app K ≫
        dd.inv.app (H.mapDerivedCategory.obj K) := by
    simpa only [cd, dd, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm] using h
  have h'' := congrArg (fun k ↦ F.mapDerivedCategory.map (cd.hom.app K) ≫ k ≫
    dd.hom.app (H.mapDerivedCategory.obj K)) h'
  simp only [Category.assoc, ← F.mapDerivedCategory.map_comp_assoc,
    Iso.hom_inv_id_app, F.mapDerivedCategory.map_id, Category.id_comp,
    Iso.inv_hom_id_app] at h''
  dsimp only [Functor.comp_obj] at h''
  simpa only [Category.comp_id] using h''.symm

/-- Unit-normalized comparisons preserve adjoint quotient transitions. -/
private theorem adjointTransitionComparison
    {C A B C' A' B' : Type*}
    [Category C] [Category A] [Category B]
    [Category C'] [Category A'] [Category B']
    {L : C ⥤ A} {U : A ⥤ C} {N : C ⥤ B} {W : B ⥤ C}
    {L' : C' ⥤ A'} {R : A' ⥤ C'} {N' : C' ⥤ B'} {S : B' ⥤ C'}
    (al : L ⊣ U) (an : N ⊣ W) (ar : L' ⊣ R) (as' : N' ⊣ S)
    (V : B ⥤ A) (T : B' ⥤ A') (F : C ⥤ C') (G : A ⥤ A') (H : B ⥤ B')
    (a : U ⋙ F ≅ G ⋙ R) (b : W ⋙ F ≅ H ⋙ S)
    (e : V ⋙ G ≅ H ⋙ T) (c : V ⋙ U ≅ W) (d : T ⋙ R ≅ S)
    (hsq : ∀ Z, F.map (c.hom.app Z) ≫ b.hom.app Z =
      a.hom.app (V.obj Z) ≫ R.map (e.hom.app Z) ≫ d.hom.app (H.obj Z))
    (K : C) (bm : L'.obj (F.obj K) ≅ G.obj (L.obj K))
    (bn : N'.obj (F.obj K) ≅ H.obj (N.obj K))
    (hm : ar.unit.app (F.obj K) ≫ R.map bm.hom ≫ a.inv.app (L.obj K) =
      F.map (al.unit.app K))
    (hn : as'.unit.app (F.obj K) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      F.map (an.unit.app K))
    (v : L.obj K ⟶ V.obj (N.obj K))
    (hv : al.unit.app K ≫ U.map v ≫ c.hom.app (N.obj K) = an.unit.app K) :
    R.map ((ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
        (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))) ≫
        d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      R.map bm.hom ≫ a.inv.app (L.obj K) ≫
        F.map (U.map v ≫ c.hom.app (N.obj K)) := by
  have hm' : ar.unit.app (F.obj K) ≫ R.map bm.hom =
      F.map (al.unit.app K) ≫ a.hom.app (L.obj K) := by
    have h := congrArg (fun k ↦ k ≫ a.hom.app (L.obj K)) hm
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have hn' : as'.unit.app (F.obj K) ≫ S.map bn.hom =
      F.map (an.unit.app K) ≫ b.hom.app (N.obj K) := by
    have h := congrArg (fun k ↦ k ≫ b.hom.app (N.obj K)) hn
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  let t := (ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
    (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))
  have ht : bm.hom ≫ G.map v ≫ e.hom.app (N.obj K) = t ≫ T.map bn.hom := by
    apply (ar.homEquiv _ _).injective
    simp only [ar.homEquiv_unit, R.map_comp]
    have htu : ar.unit.app (F.obj K) ≫ R.map t =
        as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)) :=
      (ar.homEquiv_unit _ _ t).symm.trans ((ar.homEquiv _ _).apply_symm_apply _)
    rw [reassoc_of% htu]
    apply (cancel_mono (d.hom.app (H.obj (N.obj K)))).1
    rw [reassoc_of% hm']
    have ha := a.hom.naturality v
    dsimp only [Functor.comp_map] at ha
    simp only [Category.assoc]
    rw [← reassoc_of% ha, ← hsq]
    have hd := d.hom.naturality bn.hom
    dsimp only [Functor.comp_map] at hd
    rw [hd]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [hn', ← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hv]
  have hc : a.inv.app (V.obj (N.obj K)) ≫ F.map (c.hom.app (N.obj K)) =
      R.map (e.hom.app (N.obj K)) ≫ d.hom.app (H.obj (N.obj K)) ≫
        b.inv.app (N.obj K) := by
    have h := congrArg
      (fun k ↦ a.inv.app (V.obj (N.obj K)) ≫ k ≫ b.inv.app (N.obj K))
      (hsq (N.obj K))
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have ha := a.inv.naturality v
  dsimp only [Functor.comp_map] at ha
  change R.map t ≫ d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫
      b.inv.app (N.obj K) = _
  rw [F.map_comp]
  rw [← reassoc_of% ha]
  rw [hc, ← R.map_comp_assoc, ← R.map_comp_assoc]
  simp only [Category.assoc]
  rw [ht, R.map_comp]
  have hd := d.hom.naturality bn.hom
  dsimp only [Functor.comp_map] at hd
  rw [Category.assoc, reassoc_of% hd]

/-- Locally surjective scalar restriction is full on sheaf modules. -/
private theorem restrictionFull
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    [Presheaf.IsLocallySurjective J f.hom] :
    (SheafOfModules.restrictScalars f).Full where
  map_surjective {M N} g := by
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := J) (M₁ := M.val) f.hom N.isSheaf
    refine ⟨⟨e.symm g.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply g.val

/-- The completed coefficient projections have full ordinary restriction. -/
private theorem scalarRestrictionFull (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E X n).Full := by
  let f := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  let : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) f.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (projection_surjective l E X _ (uniformizer_normalized l E X n))
  exact restrictionFull f

private def testDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem existsTestDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  by_cases h : l = 2
  · exact ⟨testDatum 3 (by decide), by simp [testDatum, h]⟩
  · exact ⟨testDatum 2 (by decide), h⟩

/-- The restricted adjoint of the smaller reduction unit. -/
private def adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn) :
    Lm ⋙ Rm ⟶ Ln ⋙ Rn where
  app M := Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
      (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ d.hom.app (Ln.obj M)
  naturality {M N} f := by
    have h : Lm.map f ≫
        (am.homEquiv N (T.obj (Ln.obj N))).symm
          (an.unit.app N ≫ d.inv.app (Ln.obj N)) =
        (am.homEquiv M (T.obj (Ln.obj M))).symm
          (an.unit.app M ≫ d.inv.app (Ln.obj M)) ≫ T.map (Ln.map f) := by
      apply (am.homEquiv _ _).injective
      rw [am.homEquiv_naturality_left, Equiv.apply_symm_apply,
        am.homEquiv_naturality_right, Equiv.apply_symm_apply]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      have hu := an.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      rw [reassoc_of% hu]
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ an.unit.app M ≫ k) (d.inv.naturality (Ln.map f))
    dsimp only [Functor.comp_map]
    rw [← Rm.map_comp_assoc, h, Rm.map_comp, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun k ↦ Rm.map ((am.homEquiv M (T.obj (Ln.obj M))).symm
        (an.unit.app M ≫ d.inv.app (Ln.obj M))) ≫ k)
      (d.hom.naturality (Ln.map f))

private theorem normalizeRepresentativeTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (T : B ⥤ A) (d : T ⋙ Rm ≅ Rn)
    (P V W : C) (cm : Rm.obj (Lm.obj P) ⟶ V) (cn : Rn.obj (Ln.obj P) ⟶ W)
    (f : V ⟶ W)
    (h : Rm.map ((am.homEquiv P (T.obj (Ln.obj P))).symm
        (an.unit.app P ≫ d.inv.app (Ln.obj P))) ≫ d.hom.app (Ln.obj P) ≫
        Rn.map (Ln.map (Iso.refl P).inv) ≫ cn =
      Rm.map (Lm.map (Iso.refl P).inv) ≫ cm ≫ f) :
    (adjointTransition am an T d).app P ≫ cn = cm ≫ f := by
  simpa [adjointTransition] using h
private theorem encodingDerivedFunctor (A : Encoding l E X) :
    A.derived.functor = A.modules.functor.mapDerivedCategory := rfl

/-- Normalized finite derived comparison maps commute with the actual quotient transitions.
Source: blueprint integral-criterion-reductions, comparison proof step 4;
Stacks 06YY, compatibility of derived base change with quotient maps
(blueprint: lem-pe-integral-reduction-transition-comparison).

Proof: the inverse mate of each restriction square is the unique comparison of left
adjoints normalized by the displayed unit equation. On an internal K-flat representative,
the normalized section reconstruction and coefficient relabelling identify the tensor
balancing relations. The comparison takes s tensor x to s tensor x. Consecutive coefficient
quotients on each side take this tensor to rho(s) tensor x. These formulas agree, including
on zero modules, and tensor generation followed by sheafification gives equality of the
ordinary chain maps. The section equivalence preserves K-flatness, by the internal/section
tensor comparison and relabelling along a ring isomorphism. The universal derived counits
are invertible on these representatives. Their unit normalization identifies the inverse
mate with the localized tensor comparison. The defining representative normalization of
sfDerivedReductionTransition and the internal derived scalar adjunction identify both
localized quotient maps with the transitions in the conclusion. Naturality of all comparisons
transports the equation from the K-flat representative to every derived object. This result
concerns the transitions alone; it asserts neither existence of normalized squares nor any
completeness triangle. -/
theorem integral_completion_transition_comparison (A : Encoding l E X) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (e : ∀ n : ℕ,
      FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X)
      (a : ∀ n : ℕ,
      Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
        (e n).ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n),
    let r (n : ℕ) :
        AdicCompletion.restrict l E X n ⋙ A.derived.functor ≅
          (e n).ordinaryDerived.functor ⋙ scalarReductionDerivedRestriction.{u, u} l E X n :=
      letI := HasDerivedCategory.standard
        (FiniteDiscreteOrdinary.Ordinary (Padic.coefficientExtensionRing l E (n + 1)) X)
      letI := scalarReductionRestrictionLimits.{u, u} l E X n
      letI := scalarReductionRestrictionColimits.{u, u} l E X n
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (AdicCompletion.quotient l E X n)) A.modules.functor).symm ≪≫
        Functor.mapDerivedCategoryNatIso (a n) ≪≫
        Functor.mapDerivedCategoryCompIso (e n).ordinary.functor
          (scalarReductionRestriction.{u, u} l E X n)
    let c (b : ∀ n : ℕ,
      A.derived.functor ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
        AdicCompletion.derivedReduction l E X n ⋙ (e n).ordinaryDerived.functor)
        (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)) :
        (sfDerivedReductionRestricted l E X n).obj (A.derived.functor.obj K) ≅
          A.derived.functor.obj (AdicCompletion.integralLevel l E X K n) :=
      (scalarReductionDerivedRestriction.{u, u} l E X n).mapIso ((b n).app K) ≪≫
        ((r n).app ((AdicCompletion.derivedReduction l E X n).obj K)).symm
    (∀ (n : ℕ) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)),
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          ((a n).hom.app M) =
        (SheafOfModules.toSheaf
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
            (eqToIso (congrArg (fun F ↦ F.obj
              ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
          (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
            (eqToIso (congrArg (fun F ↦ F.obj M) (e n).ordinary_functor)).inv) →
    ∀ (b : ∀ n : ℕ,
      A.derived.functor ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
        AdicCompletion.derivedReduction l E X n ⋙ (e n).ordinaryDerived.functor),
      (∀ (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)),
        (sfDerivedReductionUnit l E X n).app (A.derived.functor.obj K) ≫
          (c b n K).hom = A.derived.functor.map
            ((Mod.derivedExtendMapDerivedCategoryAdjunction
              (AdicCompletion.quotient l E X n)).unit.app K)) →
      ∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ),
        (sfDerivedReductionTransition l E X n).app (A.derived.functor.obj K) ≫
            (c b n K).hom = (c b (n + 1) K).hom ≫
          A.derived.functor.map (AdicCompletion.integralStep l E X K n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  intro e a r c _ha b hb K n
  obtain ⟨D, hl⟩ := existsTestDatum l
  let (i : ℕ) := HasDerivedCategory.standard
    (FiniteDiscreteOrdinary.Ordinary (Padic.coefficientExtensionRing l E (i + 1)) X)
  let (i : ℕ) : (e i).ordinary.functor.Additive := (e i).ordinaryAdditive
  let (i : ℕ) := scalarReductionRestrictionLimits.{u, u} l E X i
  let (i : ℕ) := scalarReductionRestrictionColimits.{u, u} l E X i
  let := scalarRestrictionFull l E X (n + 1)
  let : (scalarReductionRestriction.{u, u} l E X (n + 1)).Faithful := by
    constructor
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.restrictScalars _).map_injective
    exact congrArg SheafOfModules.Hom.val h
  let c₀ := (Mod.comapComp (AdicCompletion.quotient l E X (n + 1))
    (AdicCompletion.transition l E X n)).symm ≪≫
      Mod.comapCongr (AdicCompletion.quotient_transition l E X n)
  let d₀ := normalizedDVRTransitionRestriction l E X D hl n
  have hd₀ := normalizedDVRTransitionRestriction_comp l E X D hl n
  have hSquare := liftDerivedRestrictionSquare
    (Mod.comap (AdicCompletion.quotient l E X (n + 1)))
    (Mod.comap (AdicCompletion.transition l E X n))
    (Mod.comap (AdicCompletion.quotient l E X n))
    (scalarReductionRestriction.{u, u} l E X (n + 1))
    (normalizedDVRModuleRes l E X n.le_succ)
    (scalarReductionRestriction.{u, u} l E X n)
    A.modules.functor (e (n + 1)).ordinary.functor (e n).ordinary.functor
    (a (n + 1)) (a n) c₀ d₀
  obtain ⟨q, hq⟩ := hSquare
  have hs := adjointTransitionComparison
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X (n + 1)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (AdicCompletion.finiteRestrict l E X n) (normalizedDVRRes l E X n.le_succ)
    A.modules.functor.mapDerivedCategory
    (e (n + 1)).ordinary.functor.mapDerivedCategory
    (e n).ordinary.functor.mapDerivedCategory
    (r (n + 1)) (r n) q
    (AdicCompletion.restrictComp l E X n)
    (normalizedDVRResCompletedComp l E X D hl n.le_succ)
    (by
      simpa only [r, AdicCompletion.restrictComp, AdicCompletion.finiteRestrict,
        scalarReductionDerivedRestriction, c₀, d₀, hd₀] using hq)
    K ((b (n + 1)).app K) ((b n).app K)
    (hb (n + 1) K) (hb n K) (AdicCompletion.derivedStep l E X K n)
    (AdicCompletion.reductionUnit_compatible l E X K n)
  rw [sectionTransitionAdjoint l E X D hl n]
  simpa only [adjointTransition, AdicCompletion.integralStep, c, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc, encodingDerivedFunctor, Iso.app_inv,
    AdicCompletion.derivedReduction, AdicCompletion.restrict, AdicCompletion.integralLevel,
    sfDerivedReductionRestricted, Functor.comp_obj] using hs

attribute [local irreducible] Functor.mapDerivedCategory

private theorem sectionTransitionAdjoint
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    sfDerivedReductionTransition l E X n =
      adjointTransition
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
        (normalizedDVRRes.{u, u} l E X n.le_succ)
        (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ) := by
  apply (sfDerivedReductionTransition_existsUnique l E X n).unique
    (sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec
  intro P hP
  have h := normalizedDVR_kflat_transition.{0, u, u} l E X D hl P hP
    (DerivedCategory.Q.obj P) (Iso.refl _) n
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl (n + 1) P hP)
    (normalizedDVRKFlatUnit.{0, u, u} l E X D hl n P hP)
  have h' := normalizeRepresentativeTransition
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X (n + 1)).choose
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
    (normalizedDVRRes.{u, u} l E X n.le_succ)
    (normalizedDVRResCompletedComp.{0, u, u} l E X D hl n.le_succ)
    (DerivedCategory.Q.obj P) _ _
    (normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P)
    (normalizedDVRKFlatComparison.{u, u} l E X n P)
    (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) h
  have hf := congrArg (fun f ↦ DerivedCategory.Q.map f)
    (transition_eq l E X D hl P n)
  simpa only [normalizedDVRKFlatComparison, sfReductionRepresentativeComparison] using
    h'.trans (congrArg
      (fun f ↦ normalizedDVRKFlatComparison.{u, u} l E X (n + 1) P ≫ f) hf)

section RestrictionCompositor
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

/-- Ordinary restriction compositor coming from the limit projection equation. -/
private noncomputable def normalizedDVRTransitionRestriction
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    normalizedDVRModuleRes l E X n.le_succ ⋙
      scalarReductionRestriction.{u, u} l E X (n + 1) ≅
        scalarReductionRestriction.{u, u} l E X n := by
  let e₀ := normalizedDVRRestrictionCompIso
    (completedIntegralCoefficientProjection l E X D hl (n + 1))
    (normalizedDVRQuotient l E X n.le_succ)
  let he : completedIntegralCoefficientProjection l E X D hl (n + 1) ≫
      normalizedDVRQuotient l E X n.le_succ =
        completedIntegralCoefficientProjection l E X D hl n := by
    exact limit.w (integralCoefficientSheafSystem l E X) (homOfLE n.le_succ).op
  exact e₀ ≪≫ eqToIso (congrArg
    (fun f : completedIntegralCoefficientSheaf l E X D hl ⟶
        integralCoefficientSheaf l E X n ↦ SheafOfModules.restrictScalars.{u + 1} f) he)

/-- Localization of the ordinary compositor is the specified tower compositor. -/
private theorem normalizedDVRTransitionRestriction_comp
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (n : ℕ) :
    (Functor.mapDerivedCategoryCompIso
      (normalizedDVRModuleRes l E X n.le_succ)
      (scalarReductionRestriction.{u, u} l E X (n + 1))).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (normalizedDVRTransitionRestriction l E X D hl n) =
      normalizedDVRResCompletedComp l E X D hl n.le_succ := by
  unfold normalizedDVRResCompletedComp
  rfl
end RestrictionCompositor

end AlgebraicGeometry.ProEtale.IntegralPresentation
