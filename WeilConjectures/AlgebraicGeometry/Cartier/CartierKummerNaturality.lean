/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerArbitraryScalarMaps
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerScalarOfSource
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionPullback
import WeilConjectures.AlgebraicGeometry.Cartier.CartierSourceComparisonGenerator
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierExchangeUnitCompatibility
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateEtaleLineNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateTransportedPullbackNormalization
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionScalar
import WeilConjectures.AlgebraicGeometry.Cartier.CartierDerivedUnitConjugation
import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability

/-! # Functoriality of the normalized Cartier realization

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md,
final paragraph, and the expanded proof steps 7, 12 and 13.
(blueprint: lem-route-cartier-kummer-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Normalized ordinary Cartier Kummer families satisfy coefficient reduction:
the first conjunct of `cartier_kummer_naturality`.

Source: blueprint lem-route-cartier-kummer-naturality, proof step 1
(blueprint: lem-route-cartier-kummer-naturality).

Proof: for a ≤ b and an exponent N = l^(r+1) killing both quotient rings, the
arbitrary-ring scalar maps give the constant maps η_D, η_T with their generator
formulas; the ordinary derived-unit lemma gives their unbounded universal
properties, including that of i_*η_D; the two normalized boundary classes and
these data are the hypotheses of the scalar-of-source lemma, which yields
SupportedKummerScalar. -/
private theorem cartier_etale_kummer_reduction
    (κ : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ) :
    CartierEtaleKummerReduction l E κ := by
  unfold CartierEtaleKummerReduction
  intro a b hab r hb ha D T i hi hI hT
  let _ : Finite (finiteTateCoefficient l E a) := by
    let := Padic.finite_coefficientExtensionRing l E (a + 1)
      (Nat.le_add_left 1 a)
    infer_instance
  let _ : Finite (finiteTateCoefficient l E b) := by
    let := Padic.finite_coefficientExtensionRing l E (b + 1)
      (Nat.le_add_left 1 b)
    infer_instance
  have hN : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  obtain ⟨ηD, ηT, hηD, hηT, _⟩ :=
    exists_supported_kummer_arbitrary_scalar_maps
      (cartierCoefficientReduction l E a b hab) i
  obtain ⟨hD, hIu, hTu⟩ := supported_kummer_scalar_derived_units T
    (finiteTateCoefficient l E b) (finiteTateCoefficient l E a)
    (cartierCoefficientReduction l E a b hab) i ηD ηT hηD hηT
  unfold CartierEtaleKummerNormalization at hκ
  exact supported_kummer_scalar_of_source
    (cartierCoefficientReduction l E a b hab) T (l ^ (r + 1)) hN hb ha
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) i hI
    (κ a r ha i hI hT) (κ b r hb i hI hT)
    (hκ a r ha i hI hT) (hκ b r hb i hI hT) ηD hηD hIu

-- Expose the two fixed supported-constant abbreviations only in this proof module.
set_option allowUnsafeReducibility true in
attribute [local reducible] cartierSupported cartierSupportedUnit

-- The proof uses the Ext API, never its localization implementation.
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor

/-- The two scalar-unit predicates differ only by associativity of composition. -/
private theorem scalar_unit_of_geo
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj G)
    (hη : ProEtale.GeoCartierScalarUnit φ T F G η) :
    IsCartierDerivedScalarUnit φ T F G η := by
  unfold IsCartierDerivedScalarUnit ProEtale.GeoCartierScalarUnit
    Sheaf.IsDerivedBaseChange Sheaf.derivedRestrictScalars at *
  intro K
  simpa only [Category.assoc] using hη K

private instance coefficientFinite (n : ℕ) : Finite (finiteTateCoefficient l E n) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  infer_instance

/-- The quotient map in the open-closed short exact sequence is epic. -/
private theorem supported_unit_epi (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    Epi (supportedConstantUnit A i) := by
  have h := shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
    i.openComplement.ι i (ordinaryFiniteConstant A T) i.range_eq_compl_range_openComplement_ι
  have hu : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (ordinaryFiniteConstant A T)) := h.epi_g
  unfold supportedConstantUnit
  rw [Adjunction.homEquiv_unit]
  infer_instance

set_option maxHeartbeats 800000 in
-- Identifying the concrete supported-source presentations needs extra elaboration heartbeats.
/-- The supported-unit normalization determines the source comparison by epi cancellation;
ordinary boundary uniqueness then identifies the realized Ext class. -/
private theorem realized_class_eq
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤)))
    (α : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
            (ordinaryFiniteConstant (finiteTateCoefficient l E n) D)) ≅ cartierSupported l E n i)
    (q : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) ≅
            finiteTateProSheaf l E n T 1)
    (hα : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).map
          (supportedConstantUnit (finiteTateCoefficient l E n) i) ≫ α.hom =
        cartierConstantComparison (finiteTateCoefficient l E n) T ≫
          cartierSupportedUnit l E n i)
    (he : (Ext.mk₀ α.hom).comp (c n i hI hT) (zero_add 2) =
        ((κ n r hA i hI hT).mapExactFunctor
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
          (Ext.mk₀ q.hom) (add_zero 2)) :
    c n i hI hT =
      (ProEtale.geoCartierCanonicalClass (finiteTateCoefficient l E n)
        (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA i hI
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).comp
          (Ext.mk₀ q.hom) (add_zero 2) := by
  let _ : Finite (finiteTateCoefficient l E n) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    infer_instance
  let A := finiteTateCoefficient l E n
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let e := ProEtale.geoCartierSourceComparison A i
  let _ := supported_unit_epi A i
  let _ := Functor.preservesEpimorphisms_of_adjunction
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
  have hαe : α.hom = e := by
    apply (cancel_epi (V.map (supportedConstantUnit A i))).1
    exact hα.trans (ProEtale.cartierSourceComparison_supportedConstantUnit A i).symm
  have hk : κ n r hA i hI hT =
      geoCartierEtaleClass A (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _)
        hA i hI (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) := by
    apply (geoCartierEtaleClass_spec A (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA i hI _).2
    unfold CartierEtaleKummerNormalization at hκ
    exact hκ n r hA i hI hT
  have hh := congrArg
    (fun z ↦ (Ext.mk₀ (asIso e).inv).comp z (zero_add 2)) he
  rw [hαe, hk] at hh
  have hei : (asIso e).inv ≫ e = 𝟙 _ := (asIso e).inv_hom_id
  rw [Ext.mk₀_comp_mk₀_assoc, hei, Ext.mk₀_id_comp] at hh
  simpa only [Ext.comp_assoc_of_third_deg_zero, ProEtale.geoCartierCanonicalClass] using hh

universe uC uB vC vB wC wB

/-- Transport the targets in a scalar Yoneda square. -/
private theorem ext_target_transport
    {C : Type uC} {B : Type uB} [Category.{vC} C] [Category.{vB} B]
    [Abelian C] [Abelian B] [HasExt.{wC} C] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {P Q R : C} {P' Q' R' : B}
    (p : P' ⟶ U.obj P) (t : Q' ⟶ U.obj Q)
    (g : Ext P Q 2) (g' : Ext P' Q' 2)
    (h : (Ext.mk₀ p).comp (g.mapExactFunctor U) (zero_add 2) =
      g'.comp (Ext.mk₀ t) (add_zero 2))
    (q : Q ≅ R) (q' : Q' ≅ R') :
    (Ext.mk₀ p).comp
        ((g.comp (Ext.mk₀ q.hom) (add_zero 2)).mapExactFunctor U) (zero_add 2) =
      (g'.comp (Ext.mk₀ q'.hom) (add_zero 2)).comp
        (Ext.mk₀ (q'.inv ≫ t ≫ U.map q.hom)) (add_zero 2) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, h]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_assoc]

/-- Transport the targets in a pullback Yoneda square. -/
private theorem ext_pullback_target_transport
    {C : Type uC} {B : Type uB} [Category.{vC} C] [Category.{vB} B]
    [Abelian C] [Abelian B] [HasExt.{wC} C] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {P Q R : C} {P' Q' R' : B}
    (p : U.obj P ⟶ P') (t : U.obj Q ⟶ Q')
    (g : Ext P Q 2) (g' : Ext P' Q' 2)
    (h : (Ext.mk₀ p).comp g' (zero_add 2) =
      (g.mapExactFunctor U).comp (Ext.mk₀ t) (add_zero 2))
    (q : Q ≅ R) (q' : Q' ≅ R') :
    (Ext.mk₀ p).comp (g'.comp (Ext.mk₀ q'.hom) (add_zero 2)) (zero_add 2) =
      ((g.comp (Ext.mk₀ q.hom) (add_zero 2)).mapExactFunctor U).comp
        (Ext.mk₀ (U.map q.inv ≫ t ≫ q'.hom)) (add_zero 2) := by
  rw [← Ext.comp_assoc_of_third_deg_zero, h, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [← U.map_comp_assoc, q.hom_inv_id, U.map_id, Category.id_comp]

set_option maxHeartbeats 800000 in
-- The explicit Tate transports require extra elaboration heartbeats.
private theorem cartier_kummer_baseChange
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hc : CartierKummerRealization l E κ c) : CartierKummerBaseChange l E c := by
  unfold CartierKummerBaseChange
  intro n D D' T T' i i' hi hi' h w sq hI hI' hT hT'
  obtain ⟨r, hA⟩ := hkill n
  let _ : Finite (finiteTateCoefficient l E n) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    infer_instance
  have hN : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hTN : IsUnit (((l ^ (r + 1) : ℕ)) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (r + 1)
  have hTN' : IsUnit (((l ^ (r + 1) : ℕ)) : Γ(T', ⊤)) := by
    simpa only [Nat.cast_pow] using hT'.pow (r + 1)
  unfold CartierKummerRealization at hc
  obtain ⟨α, q, hq, hα, he⟩ := hc n r hA i hI hT
  obtain ⟨α', q', hq', hα', he'⟩ := hc n r hA i' hI' hT'
  have hc₀ := realized_class_eq l E κ c hκ n r hA i hI hT α q hα he
  have hc₁ := realized_class_eq l E κ c hκ n r hA i' hI' hT' α' q' hα' he'
  obtain ⟨t, ht⟩ := ProEtale.geoCartierCanonicalClass_pullback
    (finiteTateCoefficient l E n) (l ^ (r + 1)) hN hA
  obtain ⟨hex, hg⟩ := ht i i' h w sq hI hI' hTN hTN'
  let U := ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h
  let p : U.obj (cartierSupported l E n i) ≅ cartierSupported l E n i' := by
    unfold cartierSupported
    exact asIso (ProEtale.geoCartierExchange (finiteTateCoefficient l E n)
      i i' h w sq.toCommSq)
  let tq := U.mapIso q.symm ≪≫
    (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).app _ ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso (t.line h hTN) ≪≫ q'
  refine ⟨p, tq, ?_, ?_, ?_⟩
  · exact finite_tate_transported_pullback_normalized l E n T T' h hT hT' r hA 1
      q q' hq hq' (t.line h hTN)
      (ordinaryFiniteLineNormalization_finiteTateEtalePullback l E n r hA t h hT)
  · dsimp [p]
    exact ProEtale.geoCartierExchange_unit_compatibility
      (finiteTateCoefficient l E n) i i' h w sq.toCommSq
  · rw [hc₀, hc₁]
    simpa only [tq, ProEtale.geoCartierLinePullback, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Category.assoc] using
      ext_pullback_target_transport U p.hom
      (ProEtale.geoCartierLinePullback (finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA t h hTN).hom _ _ hg q q'

/-- Evaluation preserves the kernel defining the etale roots sheaf.
This is the kernel calculation also used in FiniteTateTransportedPullbackNormalization. -/
private theorem etale_roots_sections (T : Scheme.{u}) (m : ℕ) (U : T.Etaleᵒᵖ) :
    ∃ e : (T.rootsOfUnitySheaf m).obj.obj U ≃
        {z : Γ(U.unop.left, ⊤)ˣ // z ^ m = 1},
      ∀ z, (e z).val = finiteTateEtaleRootValue T m U z := by
  let ev := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let φ := ev.map (m • 𝟙 T.gmSheaf)
  let e := PreservesKernel.iso ev (m • 𝟙 T.gmSheaf) ≪≫ AddCommGrpCat.kernelIsoKer φ
  let g : φ.hom.ker ≃ {z : Γ(U.unop.left, ⊤)ˣ // z ^ m = 1} :=
    { toFun := fun y ↦ ⟨y.1.down.toMul, by
        have hy : m • y.1 = 0 := y.2
        exact congrArg (fun z ↦ z.down.toMul) hy⟩
      invFun := fun z ↦ ⟨ULift.up (Additive.ofMul z.val), by
        change m • (ULift.up (Additive.ofMul z.val)) = 0
        apply ULift.ext
        apply Additive.toMul.injective
        exact z.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨e.addCommGroupIsoToAddEquiv.toEquiv.trans g, ?_⟩
  intro z
  have he : e.hom ≫ AddCommGrpCat.ofHom φ.hom.ker.subtype =
      ev.map (kernel.ι (m • 𝟙 T.gmSheaf)) := by
    rw [Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact congrArg (fun q ↦ q.down.toMul) (ConcreteCategory.congr_hom he z)

/-- An N-th root on a pro-etale object is pulled back from the tautological root on μ_N.
Construct the latter by affineRoots_representability; invertibility of N makes it etale. -/
private theorem root_test_object (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    ∃ (V : T.Etale) (z : (T.rootsOfUnitySheaf m).obj.obj (op V)),
      ∀ (W : T.ProEt) (y : Γ(W.left, ⊤)ˣ), y ^ m = 1 →
        ∃ f : W ⟶ (toProEt T).obj V,
          Units.map f.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T m (op V) z) = y := by
  let B := Γ(T, ⊤)
  have : Etale (affineRootsOver B m).hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap B
      (AdjoinRoot ((Polynomial.X : Polynomial B) ^ m - 1)))))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      (AdjoinRoot.etale_X_pow_sub_C (Nat.ne_of_gt hm) hT isUnit_one)
  let P := (Over.pullback T.toSpecΓ).obj (affineRootsOver B m)
  have : Etale P.hom := by
    change Etale (pullback.snd (affineRootsOver B m).hom T.toSpecΓ)
    infer_instance
  let V := Scheme.Etale.mk P.hom
  obtain ⟨_, _, _, _, _, _, _, hbase⟩ := affineRoots_representability B m hm
  obtain ⟨e, _, hnat, _⟩ := hbase T T.toSpecΓ
  obtain ⟨s, hs⟩ := etale_roots_sections T m (op V)
  let z := s.symm (e P (𝟙 P))
  refine ⟨V, z, ?_⟩
  intro W y hy
  let q := (e (Over.mk W.hom)).symm ⟨y, hy⟩
  let f : W ⟶ (toProEt T).obj V := MorphismProperty.Over.homMk q.left q.w
  refine ⟨f, ?_⟩
  have hz : finiteTateEtaleRootValue T m (op V) z = (e P (𝟙 P)).val :=
    (hs z).symm.trans (congrArg Subtype.val (s.apply_symm_apply _))
  rw [hz]
  exact (hnat (Over.mk W.hom) P q (𝟙 P)).symm.trans
    (congrArg Subtype.val (by
      simpa only [Category.comp_id] using (e (Over.mk W.hom)).apply_symm_apply ⟨y, hy⟩))

set_option maxHeartbeats 800000 in
-- Comparing the two concrete scalar-unit predicates requires extra heartbeats.
private theorem cartier_kummer_reduction
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hc : CartierKummerRealization l E κ c) : CartierKummerReduction l E c := by
  unfold CartierKummerReduction
  intro a b hab D T i hi hI hT
  obtain ⟨r, hb⟩ := hkill b
  let φ := cartierCoefficientReduction l E a b hab
  have ha : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E a) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ hb
  have hN : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hTN : IsUnit (((l ^ (r + 1) : ℕ)) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (r + 1)
  unfold CartierKummerRealization at hc
  obtain ⟨α, q, hq, hα, he⟩ := hc b r hb i hI hT
  obtain ⟨α', q', hq', hα', he'⟩ := hc a r ha i hI hT
  have hc₀ := realized_class_eq l E κ c hκ b r hb i hI hT α q hα he
  have hc₁ := realized_class_eq l E κ c hκ a r ha i hI hT α' q' hα' he'
  have hs := ProEtale.geoCartierCanonicalClass_scalar
    (finiteTateCoefficient l E b) (finiteTateCoefficient l E a)
    (l ^ (r + 1)) hN hb ha φ i hI hTN
  unfold ProEtale.GeoCartierScalarCompatibility at hs
  obtain ⟨η₀, θ₀, hη₀, hθ₀, huη, huθ, hsq⟩ := hs
  let Res := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
  let η : cartierSupported l E b i ⟶ Res.obj (cartierSupported l E a i) := by
    unfold cartierSupported
    exact (ProEtale.lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E b)) i).map η₀
  let θ := q.inv ≫ θ₀ ≫ Res.map q'.hom
  refine ⟨η, θ, ?_, ?_, ?_, ?_, ?_⟩
  · intro W z
    exact hη₀ ((Scheme.proEtaleBaseChange i).op.obj W) z
  · intro W z x
    obtain ⟨V, y, hV⟩ := root_test_object T (l ^ (r + 1)) hN hTN
    have hx : finiteTateLimitRootValue l T r W x ^ (l ^ (r + 1)) = 1 := by
      have hh := congrArg (fun q ↦ q.hom.app W
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W x))
        (kernel.condition (proEtaleUnitsPower T (l ^ (r + 1))))
      exact congrArg (fun q ↦ q.down.toMul) hh
    obtain ⟨f, hf⟩ := hV W.unop (finiteTateLimitRootValue l T r W x) hx
    let FR := ProEtale.geoCartierLine (finiteTateCoefficient l E b) (l ^ (r + 1)) hb T
    let FS := ProEtale.geoCartierLine (finiteTateCoefficient l E a) (l ^ (r + 1)) ha T
    let zR := ((ProEtale.comparisonAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E b)) T).unit.app
        (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E b) hb)).hom.app
          (op V) (finiteEtaleTateOneGenerator _ _ T hb (op V) z y)
    let zS := ((ProEtale.comparisonAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E a)) T).unit.app
        (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E a) ha)).hom.app
          (op V) (finiteEtaleTateOneGenerator _ _ T ha (op V) (φ z) y)
    have hqb : q.hom.hom.app W (FR.obj.map f.op zR) =
        finiteTateProGenerator l E b T W z x :=
      hq (op V) W f z (fun _ ↦ y) (fun _ ↦ x) (fun _ ↦ hf.symm)
    have hqa : q'.hom.hom.app W (FS.obj.map f.op zS) =
        finiteTateProGenerator l E a T W (φ z) x :=
      hq' (op V) W f (φ z) (fun _ ↦ y) (fun _ ↦ x) (fun _ ↦ hf.symm)
    have hqi : q.inv.hom.app W (finiteTateProGenerator l E b T W z x) =
        FR.obj.map f.op zR := by
      rw [← hqb]
      exact ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.hom.app W) q.hom_inv_id) _
    have hn := ConcreteCategory.congr_hom (θ₀.hom.naturality f.op) zR
    change θ₀.hom.app W (FR.obj.map f.op zR) =
      FS.obj.map f.op (θ₀.hom.app (op ((toProEt T).obj V)) zR) at hn
    have hθz : θ₀.hom.app (op ((toProEt T).obj V)) zR = zS := hθ₀ (op V) z y
    change q'.hom.hom.app W (θ₀.hom.app W
      (q.inv.hom.app W (finiteTateProGenerator l E b T W z x))) = _
    rw [hqi, hn, hθz]
    exact hqa
  · exact scalar_unit_of_geo φ T _ _ η huη
  · have huθ' := scalar_unit_of_geo φ T _ _ θ₀ huθ
    exact isCartierDerivedScalarUnit_of_iso_conj φ T _ _ _ _ θ₀ huθ' q.symm q'
  · rw [hc₀, hc₁]
    exact ext_target_transport Res η θ₀ _ _ hsq q' q

/-- Realization of the ordinary relative boundaries preserves arbitrary finite
coefficient reduction and every Cartier-preserving scheme pullback.

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md, final paragraph
(blueprint: lem-route-cartier-kummer-naturality).

Proof: the ordinary clause is `cartier_etale_kummer_reduction` (arbitrary scalar maps,
their derived units, and the scalar-of-source lemma at a common annihilating exponent).
For the two pro-etale clauses, `realized_class_eq` identifies each realized class with
the canonical class geoCartierCanonicalClass followed by its normalized Tate comparison:
the ordinary supported constant unit is epic (open-closed short exact sequence), the
comparison inverse image preserves epimorphisms, so the realization source comparison
equals the canonical one by cartierSourceComparison_supportedConstantUnit, and ordinary
boundary uniqueness identifies the etale class. Pullback (`cartier_kummer_baseChange`)
then follows from geoCartierCanonicalClass_pullback, exchange-unit compatibility and the
transported Tate pullback normalization; coefficient reduction (`cartier_kummer_reduction`)
from geoCartierCanonicalClass_scalar, derived-unit conjugation by the Tate comparisons, and
the pure-root formula checked on the etale root scheme of `root_test_object`. The Ext
squares are transported by the Yoneda identities `ext_pullback_target_transport` and
`ext_target_transport`. No flatness of either the coefficient or scheme map occurs. -/
theorem cartier_kummer_naturality
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hc : CartierKummerRealization l E κ c) :
    CartierEtaleKummerReduction l E κ ∧
      CartierKummerBaseChange l E c ∧ CartierKummerReduction l E c := by
  refine ⟨cartier_etale_kummer_reduction l E κ hκ,
    cartier_kummer_baseChange l E hkill κ c hκ hc,
    cartier_kummer_reduction l E hkill κ c hκ hc⟩

end AlgebraicGeometry.Etale
