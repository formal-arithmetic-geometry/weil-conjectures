/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # Reconstruction of constructible morphisms from compatible finite reductions

Source: the mapping-limit argument in lem-coef-integral-finite-extension,
second and third paragraphs, and Bhatt--Scholze, Lemma 3.5.7.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [local instance] normalizedDVREffectivityLocal2 normalizedDVREffectivityLocal3
attribute [local irreducible] HasDerivedCategory.standard
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted
  normalizedDVRResCompletedComp

private theorem roos_isHomotopyLimit
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {F : ℕᵒᵖ ⥤ C} (c : Cone F) [HasProduct (fun n ↦ F.obj (op n))]
    (δ : (∏ᶜ fun n ↦ F.obj (op n)) ⟶ c.pt⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op)
      c.pt (Pi.lift (fun n ↦ c.π.app (op n))) δ) : IsHomotopyLimit c := by
  refine ⟨_, productIsProduct _, δ, ?_⟩
  have h₁ : Fan.IsLimit.lift (productIsProduct (fun n ↦ F.obj (op n)))
      (fun n ↦ c.π.app (op n)) = Pi.lift (fun n ↦ c.π.app (op n)) := by
    apply Pi.hom_ext
    intro n
    exact (Fan.IsLimit.fac _ _ n).trans
      (Pi.lift_π (fun n ↦ c.π.app (op n)) n).symm
  have h₂ : towerShift (F := F) (productIsProduct (fun n ↦ F.obj (op n))) =
      towerProductShift (fun n ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    simp only [towerShift, towerProductShift, Pi.lift_π]
    exact Fan.IsLimit.fac _ _ n
  rw [h₁, h₂]
  exact h

private theorem adjoint_compatible
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {K M : C} (fm : Lm.obj K ⟶ Lm.obj M) (fn : Ln.obj K ⟶ Ln.obj M)
    (hf : fm ≫ (am.homEquiv M _).symm
        (an.unit.app M ≫ e.inv.app (Ln.obj M)) =
      (am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)) ≫ S.map fn) :
    am.homEquiv K _ fm ≫
        Rm.map ((am.homEquiv M _).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M))) ≫ e.hom.app _ =
      an.homEquiv K _ fn := by
  have hu : am.unit.app K ≫
      Rm.map ((am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K))) =
      an.unit.app K ≫ e.inv.app (Ln.obj K) :=
    (am.homEquiv_unit _ _ _).symm.trans ((am.homEquiv _ _).apply_symm_apply _)
  have he := e.hom.naturality fn
  dsimp only [Functor.comp_map] at he
  rw [am.homEquiv_unit, Category.assoc, ← Functor.map_comp_assoc, hf,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc]
  rw [he, Iso.inv_hom_id_app_assoc, ← an.homEquiv_unit]

private theorem intrinsic_transition_eq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (M : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    (sfDerivedReductionTransition l E X n).app M =
      (scalarReductionDerivedRestriction.{u, u} l E X (n + 1)).map
          (normalizedDVRReductionTransition.{u, u, u} l E X D hl n.le_succ M) ≫
        (normalizedDVRResCompletedComp.{u, u, u} l E X D hl n.le_succ).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj M) := by
  let G : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ :=
    (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).objPreimage M
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X) G
  have : QuasiIso q := hq
  let e : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map q) ≪≫
      (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).objObjPreimageIso M
  have hi (j : ℕ) : IsIso (sfReductionRepresentativeComparison l E X j P) :=
    representative_isIso l E X j P hP
  let a (j : ℕ) := (sfDerivedReductionRestricted l E X j).mapIso e.symm ≪≫
    @asIso _ _ _ _ (sfReductionRepresentativeComparison l E X j P) (hi j)
  apply (cancel_mono (a n).hom).1
  have ht := normalizedDVR_kflat_transition.{u, u, u} l E X D hl P hP M e n
    (normalizedDVRIntegralAdjunction l E X (n + 1))
    (normalizedDVRIntegralAdjunction l E X n)
    (normalizedDVRKFlatUnit.{u, u, u} l E X D hl (n + 1) P hP)
    (normalizedDVRKFlatUnit.{u, u, u} l E X D hl n P hP)
  dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
  erw [Category.assoc]
  erw [← (sfDerivedReductionTransition l E X n).naturality_assoc e.inv]
  erw [(sfDerivedReductionTransition_existsUnique l E X n).exists.choose_spec P
    hP]
  erw [← transition_eq l E X D hl P n]
  exact ht.symm

private theorem reduction_hom_finite
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (K M : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    Finite (K.obj⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E X n).obj M.obj) := by
  classical
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦ by
    let φ : D.k →+* X.residueField x :=
      (X.evaluation ⊤ x (by trivial)).hom.comp
        ((X ↘ Spec (.of D.k)).appTop.hom.comp (Scheme.ΓSpecIso (.of D.k)).inv.hom)
    exact (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        (PurCompactSupport.coefficientPrimeUnit l D hl).map φ).invertible
  let K' : sfIntegralConstructibleCategory l E X :=
    ⟨K.obj⟦(1 : ℤ)⟧, (sfIntegralConstructible l E X).le_shift (1 : ℤ) _ K.property⟩
  obtain ⟨a, b, hab, hK⟩ := K'.property.2
  obtain ⟨c, d, hcd, hM⟩ := M.property.2
  have htK := (integral_residue_tor D l hl E X).1
    K'.obj K'.property a b hab (hK 0).2 n
  have htM := (integral_residue_tor D l hl E X).1
    M.obj M.property c d hcd (hM 0).2 n
  have : Finite ((scalarReductionDerivedExtension.{u, u} l E X n).obj K'.obj ⟶
      (scalarReductionDerivedExtension.{u, u} l E X n).obj M.obj) :=
    intrinsic_hom_finite D l hl E (n + 1) (by omega) X _ _
      (hK n).1 (hM n).1 a b c d htK htM
  exact Finite.of_equiv _ ((normalizedDVRIntegralAdjunction l E X n).homEquiv _ _)

/-- Compatible finite reductions reconstruct a unique constructible integral morphism.
Source: lem-coef-integral-finite-extension, second and third paragraphs;
Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-sf-integral-constructible-reduction-hom).

Proof: the defining augmented Roos triangle of M makes its intrinsic reduction
cone a homotopy limit. The source library's Milnor Hom theorem identifies maps
into M with compatible maps into its restricted reductions: the required shifted
Hom groups are finite, by integral residue Tor, finite-level constructible Hom
finiteness, and scalar adjunction. On K-flat representatives the normalized
adjunction transitions agree with the intrinsic quotient transitions. Adjunction
therefore transposes the given family to an element of this Hom limit. The Milnor
bijection supplies its unique lift; unit naturality identifies the reductions of
the lift with the given maps. Level n is exponent n+1; the argument also applies
to zero objects and the empty scheme. -/
theorem integralConstructibleReductionHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (K M : sfIntegralConstructibleCategory l E X)
    (f : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj K.obj ⟶
      (scalarReductionDerivedExtension l E X n).obj M.obj)
    (hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ normalizedDVRReductionTransition l E X D hl h M.obj =
        normalizedDVRReductionTransition l E X D hl h K.obj ≫
          (normalizedDVRRes l E X h).map (f n)) :
    ∃! g : K.obj ⟶ M.obj,
      ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).map g = f n := by
  obtain ⟨hp, δ, hδ⟩ := M.property.1
  let := hp
  have hc : IsHomotopyLimit (sfIntegralReductionCone l E X M.obj) := by
    apply roos_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun n ↦ (sfDerivedReductionRestricted l E X n).obj M.obj)
      (fun n ↦ (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op)
      M.obj (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app M.obj)) δ
    simpa only [sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  have (n : ℕ) : Finite
      (K.obj⟦(1 : ℤ)⟧ ⟶ (sfIntegralReductionTower l E X M.obj).obj (op n)) :=
    reduction_hom_finite D l hl E X K M n
  have hb := hc.bijective_milnorMap K.obj
  let a (n : ℕ) := (normalizedDVRIntegralAdjunction l E X n).homEquiv K.obj _ (f n)
  have ha (n : ℕ) : a (n + 1) ≫
      (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op = a n := by
    have ht : (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op =
        (sfDerivedReductionTransition l E X n).app M.obj :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [ht, intrinsic_transition_eq D l hl E X M.obj n]
    exact adjoint_compatible
      (normalizedDVRIntegralAdjunction l E X (n + 1))
      (normalizedDVRIntegralAdjunction l E X n)
      (normalizedDVRRes l E X n.le_succ)
      (normalizedDVRResCompletedComp.{u, u, u} l E X D hl n.le_succ)
      (f (n + 1)) (f n) (hf n.le_succ)
  obtain ⟨g, hg⟩ := hb.surjective ⟨a, ha⟩
  change K.obj ⟶ M.obj at g
  have hgn (n : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X n).map g = f n := by
    apply ((normalizedDVRIntegralAdjunction l E X n).homEquiv _ _).injective
    have hn := congrArg (fun z ↦ z.val n) hg
    change g ≫ (sfDerivedReductionUnit l E X n).app M.obj = a n at hn
    rw [Adjunction.homEquiv_unit]
    have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
    exact hu.symm.trans hn
  refine ⟨g, hgn, ?_⟩
  intro g' hg'
  apply hb.injective
  apply Subtype.ext
  funext n
  change g' ≫ (sfDerivedReductionUnit l E X n).app M.obj =
    g ≫ (sfDerivedReductionUnit l E X n).app M.obj
  change g' ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj =
    g ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj
  have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
  have hu' := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g'
  dsimp only [Functor.id_map, Functor.comp_map] at hu hu'
  rw [hu', hu, hg' n, hgn n]

end WeilConjectures
