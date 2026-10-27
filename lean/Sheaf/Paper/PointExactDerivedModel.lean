/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-!
# Exact point models and the normalized derived compositor

Source: Stacks Project, Tags 0D6D, 015F and 04VG; the point-fibre clause of
blueprint `def-weil-finite-coefficient-point`
(blueprint: lem-trf-point-exact-derived-model).

The abbreviations specialize existing module pullbacks, exact derived factorizations,
and point sections. The ordinary compositor is determined by fibre-product pasting
and adjunction conjugation. The derived compositor is the prescribed K-flat-normalized
comparison, specialized to the actual constant-section coefficient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointExactDerivedModel

/-- Spec of geometric field Frobenius on the fixed closure.
Source: Deligne, Weil II (1.1.7); Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
def frobenius (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ⟶ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Spec.map (CommRingCat.ofHom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom)

/-- Iterated geometric Frobenius, with the positive recursion exposing composition.
Source: Stacks Tag 0D6D, applied to powers of geometric Frobenius
(blueprint: lem-trf-point-exact-derived-model). -/
def power (D : FiniteFieldDatum.{u}) : ℕ → (Spec (.of D.k) ⟶ Spec (.of D.k))
  | 0 => 𝟙 _
  | 1 => frobenius D
  | r + 2 => frobenius D ≫ power D (r + 1)

/-- The actual constant-ring module category on the original small pro-etale point.
Source: Stacks, Modules on Sites, Tag 03CW
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev modules (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  proEtaleRingModules (Spec (.of D.k)) (proEtaleConstantRing (Spec (.of D.k)) A)

/-- Ordinary tensor module pullback with the canonical constant-section coefficient map.
Source: Stacks Tags 03D2 and 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev pullback (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  proEtaleConstantRingPullback A (power D r)

/-- The ambient derived pullback in the recorded canonical ring-sheaf presentation.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev derivedPullback (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  proEtaleConstantRingDerivedPullback A (power D r)

/-- Canonical exact-functor comparison on every complex, without flatness conditions.
Source: Stacks Tag 015F and Mathlib `Functor.mapDerivedCategoryFactors`
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev pullbackFactors (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (r : ℕ) :=
  (pullback D A r).mapDerivedCategoryFactors

/-- Derived final-object sections using the recorded constant scalar action.
Source: blueprint `def-weil-finite-coefficient-point`, clause 1; Stacks Tag 015F
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev evaluation (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  (pointFiniteSections D.k A).mapDerivedCategory

/-- The canonical comparison with termwise final-object sections on every representative.
Source: Stacks Tag 015F and Mathlib `Functor.mapDerivedCategoryFactors`
(blueprint: lem-trf-point-exact-derived-model). -/
abbrev evaluationFactors (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] :=
  (pointFiniteSections D.k A).mapDerivedCategoryFactors

/-- The ordinary compositor T_(m+1), in the iterated-to-composite direction.
The defining theorem determines its direct-image conjugate on every section by the
fibre-product associator. That fixes the conjugate and hence this isomorphism uniquely.
Source: Stacks Tag 03D8
(blueprint: lem-trf-point-exact-derived-model). -/
def ordinaryComposition (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (m : ℕ) :
    pullback D A (m + 1) ⋙ pullback D A 1 ≅ pullback D A (m + 2) :=
  (Classical.choose (proEtaleConstantRingModulePullbackComposition
    (frobenius D) (power D (m + 1)) A)).symm

/-- The inverse of the prescribed K-flat-normalized comparison, with the composite
coefficient identification transported by the published constant-section equality.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model). -/
def derivedComposition (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] (m : ℕ) :
    derivedPullback D A (m + 1) ⋙ derivedPullback D A 1 ≅
      derivedPullback D A (m + 2) :=
  proEtaleConstantRingPullbackComposition (frobenius D) (power D (m + 1)) A

/-- Exactness and preservation of quasi-isomorphisms for all positive powers and sections.
Source: Stacks Tags 0982, 098H and 015F
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 1--2): constant-coefficient module inverse image is exact. Final-object
sections over the algebraically closed point are exact. Restrict scalars by the actual
constant-section map; this preserves kernels and cokernels. Exact additive functors
preserve cohomology and hence quasi-isomorphisms. Their canonical factorization maps
are precisely `pullbackFactors` and `evaluationFactors`, on arbitrary complexes. -/
theorem exactness (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ r : ℕ,
      PreservesFiniteLimits (pullback D (Padic.coefficientExtensionRing l E n) (r + 1)) ∧
      PreservesFiniteColimits (pullback D (Padic.coefficientExtensionRing l E n) (r + 1)) ∧
      ∀ (K L : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ)
        (f : K ⟶ L), QuasiIso f →
        QuasiIso (((pullback D (Padic.coefficientExtensionRing l E n) (r + 1)).mapHomologicalComplex
          (.up ℤ)).map f)) ∧
    PreservesFiniteLimits (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) ∧
    PreservesFiniteColimits (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) ∧
    ∀ (K L : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ)
      (f : K ⟶ L), QuasiIso f →
      QuasiIso (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (.up ℤ)).map f) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n _hn
  refine ⟨?_, inferInstance, inferInstance, ?_⟩
  · intro r
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro K L f hf
    have : QuasiIso f := hf
    infer_instance
  · intro K L f hf
    have : QuasiIso f := hf
    infer_instance

private theorem exactCompositionFormula
    {C B M : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category M] [Abelian M] [HasDerivedCategory M]
    (F : C ⥤ B) (G : B ⥤ M) (J : C ⥤ M)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (T : F ⋙ G ≅ J)
    (t : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ J.mapDerivedCategory)
    (ht : t.symm = Functor.mapDerivedCategoryNatIso T.symm ≪≫
      Functor.mapDerivedCategoryCompIso F G)
    (K : CochainComplex C ℤ) :
    t.hom.app (DerivedCategory.Q.obj K) ≫ J.mapDerivedCategoryFactors.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K) := by
  let c := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)
  have hcomp := Functor.mapDerivedCategoryCompIso_fac F G K
  have hcomp' : (Functor.mapDerivedCategoryCompIso F G).hom.app
        (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (c.inv.app K) := by
    apply (cancel_mono (DerivedCategory.Q.map (c.hom.app K))).mp
    simpa [c, ← CategoryTheory.Functor.map_comp] using hcomp
  apply (cancel_epi (t.inv.app (DerivedCategory.Q.obj K))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [show t.inv = (Functor.mapDerivedCategoryNatIso T.symm ≪≫
    Functor.mapDerivedCategoryCompIso F G).hom from congrArg Iso.hom ht]
  simp only [Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Category.assoc]
  have hn := Functor.mapDerivedCategoryNatIso_fac T.symm K
  change (Functor.mapDerivedCategoryNatIso T.symm).hom.app (DerivedCategory.Q.obj K) ≫
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
    J.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((T.inv.mapHomologicalComplex (.up ℤ)).app K) at hn
  symm
  calc
    _ = (Functor.mapDerivedCategoryNatIso T.symm).hom.app (DerivedCategory.Q.obj K) ≫
        (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (c.inv.app K) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K) := by
      simpa only [CategoryTheory.Category.assoc] using congrArg
        (fun f ↦ (Functor.mapDerivedCategoryNatIso T.symm).hom.app
          (DerivedCategory.Q.obj K) ≫ f ≫ DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K)) hcomp'
    _ = J.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((T.inv.mapHomologicalComplex (.up ℤ)).app K) ≫
          DerivedCategory.Q.map (c.inv.app K) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K) := by
      simpa only [CategoryTheory.Category.assoc] using congrArg
        (fun f ↦ f ≫ DerivedCategory.Q.map (c.inv.app K) ≫ DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K)) hn
    _ = _ := by
      have h : (T.inv.mapHomologicalComplex (.up ℤ)).app K ≫ c.inv.app K ≫
          (Functor.mapHomologicalComplexCompIso T (.up ℤ)).hom.app K = 𝟙 _ := by
        apply HomologicalComplex.hom_ext
        intro i
        change T.inv.app (K.X i) ≫ 𝟙 _ ≫ T.hom.app (K.X i) = 𝟙 _
        simp
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h,
        CategoryTheory.Functor.map_id]
      exact CategoryTheory.Category.comp_id _

/-- The prescribed derived compositor equals localization of the ordinary compositor
on every complex, with all iterated exact-functor identifications displayed.
Source: Stacks Tag 0D6D
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 3--5): constant-section coefficient maps compose by
lem-trf-constant-coefficient-composition. Resolve an arbitrary K by a K-flat complex P
with flat terms. On P the normalization of the recorded derived comparison gives the
ordinary termwise compositor. Its first pullback remains K-flat with flat terms.
Naturality of both compositors and of the factorization maps gives two squares along
P -> K. Exactness makes the localized iterated pullback of this quasi-isomorphism
invertible. Cancel it to get the same equation on K, without a flatness hypothesis. -/
theorem composition (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) (m : ℕ)
    (K : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ) :
    (derivedComposition D (Padic.coefficientExtensionRing l E n) m).hom.app
        (DerivedCategory.Q.obj K) ≫
      (pullbackFactors D (Padic.coefficientExtensionRing l E n) (m + 2)).hom.app K =
    (derivedPullback D (Padic.coefficientExtensionRing l E n) 1).map
        ((pullbackFactors D (Padic.coefficientExtensionRing l E n) (m + 1)).hom.app K) ≫
      (pullbackFactors D (Padic.coefficientExtensionRing l E n) 1).hom.app
        (((pullback D (Padic.coefficientExtensionRing l E n) (m + 1)).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((ordinaryComposition D (Padic.coefficientExtensionRing l E n) m).hom.mapHomologicalComplex
          (.up ℤ)).app K) := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n _hn
  exact exactCompositionFormula (pullback D A (m + 1)) (pullback D A 1)
    (pullback D A (m + 2)) (ordinaryComposition D A m) (derivedComposition D A m)
    (proEtaleConstantRingPullbackComposition_eq_mapModuleComparison
      (frobenius D) (power D (m + 1)) A) K

/-- Positive Frobenius pullbacks preserve the full bounded constructible subcategory.
Source: blueprint `lem-weil-isomorphism-derived-pullback`, finite-level clause
(blueprint: lem-trf-point-exact-derived-model).
Proof (node step 6): geometric Frobenius and every positive power are scheme
isomorphisms. The prime l is invertible on Spec k because l differs from p. Apply the
isomorphism-pullback theorem at the positive finite level n. Its termwise inverse image
is the same constant-coefficient pullback, so it preserves the recorded predicate. -/
theorem preserves_constructible (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (K : proEtaleDerivedCategory (Spec (.of D.k)) (Padic.coefficientExtensionRing l E n)) :
    intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) K →
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))
        ((derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1)).obj K) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have hF : IsIso (frobenius D) := by
    change IsIso (frobeniusPointIso D).hom
    infer_instance
  have hp : ∀ j, IsIso (power D j) := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => change IsIso (𝟙 _); infer_instance
    | one => exact hF
    | more j _ ih =>
      change IsIso (frobenius D ≫ power D (j + 1))
      have := ih
      infer_instance
  have := hp (r + 1)
  let : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    fun x ↦ (frobeniusPointPrimeResidueUnit D l _hl x).invertible
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  subst n
  obtain ⟨h, _⟩ := isomorphismFiniteDerivedPullback_termwise l E (power D (r + 1)) j
  intro hK
  let e := (openSquareDerivedPullbackModel
    (Padic.coefficientExtensionRing l E (j + 1)) (power D (r + 1))).app K
  have : (intrinsicFiniteTorsionConstructible l E (j + 1) hn
      (Spec (.of D.k))).IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (j + 1))).1
  exact (intrinsicFiniteTorsionConstructible l E (j + 1) hn
    (Spec (.of D.k))).prop_of_iso e.symm (h K hK).1

/-- Restriction of ambient evaluation is precisely the recorded point fibre functor,
with its finite-cohomology target included in the ambient coefficient derived category.
Source: blueprint `def-weil-finite-coefficient-point`, clause 1
(blueprint: lem-trf-point-exact-derived-model).
Proof (node step 6): the point fibre functor is defined by restricting this very
termwise final-object section functor. Point-sections finiteness puts its cohomology in
the finite bounded target. The full-subcategory inclusion forgets only that proof. -/
theorem evaluation_restriction (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) :
    pointFiniteFibre D l hl E n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).ι =
      (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).ι ⋙
        evaluation D (Padic.coefficientExtensionRing l E n) := by
  rfl

-- Descent is purely the universal property of the localization. Keeping the
-- argument abstract avoids unfolding the ringed-site models while cancelling factors.
private theorem descendExactTransformation
    {C B : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : C ⥤ B) (H : C ⥤ C) [F.Additive] [H.Additive]
    (V : DerivedCategory C ⥤ DerivedCategory B)
    (HD : DerivedCategory C ⥤ DerivedCategory C)
    (v : DerivedCategory.Q ⋙ V ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e : DerivedCategory.Q ⋙ HD ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : F ⟶ H ⋙ F) :
    ∃! δ : V ⟶ HD ⋙ V, ∀ K : CochainComplex C ℤ,
      δ.app (DerivedCategory.Q.obj K) ≫ V.map (e.hom.app K) ≫
        v.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      v.hom.app K ≫ DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) := by
  let L := DerivedCategory.Q (C := C)
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let w : L ⋙ (HD ⋙ V) ≅
      (H ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e V ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ)) v ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ F)) (.up ℤ))
        DerivedCategory.Q
  have hw (K : CochainComplex C ℤ) : w.hom.app K =
      V.map (e.hom.app K) ≫ v.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
    have hid : DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ F)) (.up ℤ)).hom.app K) =
          𝟙 _ := by
      change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
    simp only [w, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, hid,
      CategoryTheory.Category.id_comp]
    change V.map (e.hom.app K) ≫
      v.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫ 𝟙 _ = _
    rw [CategoryTheory.Category.comp_id]
  let : Localization.Lifting L W
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) V := ⟨v⟩
  let : Localization.Lifting L W
      ((H ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (HD ⋙ V) := ⟨w⟩
  let δ : V ⟶ HD ⋙ V := Localization.liftNatTrans L W _ _ V (HD ⋙ V)
    (Functor.whiskerRight (α.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q)
  have hδ (K : CochainComplex C ℤ) :
      δ.app (L.obj K) ≫ V.map (e.hom.app K) ≫
        v.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      v.hom.app K ≫ DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) := by
    rw [← hw]
    change δ.app (L.obj K) ≫ w.hom.app K = _
    dsimp only [δ]
    rw [Localization.liftNatTrans_app]
    change (v.hom.app K ≫
      DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) ≫
      w.inv.app K) ≫ w.hom.app K = _
    simp
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  apply Localization.natTrans_ext L W
  intro K
  apply (cancel_mono (w.hom.app K)).mp
  simpa only [hw, CategoryTheory.Category.assoc] using (hδ' K).trans (hδ K).symm

/-- Every ordinary natural transformation of section functors descends uniquely on
all ambient derived objects, with its degreewise chain-map formula on every complex.
Source: Stacks Tag 04VG; Mathlib `Localization.liftNatTrans` and `natTrans_ext`
(blueprint: lem-trf-point-exact-derived-model).
Proof (node steps 7--9): naturality of alpha at differentials makes its components a
chain map, and naturality at module maps makes these chain maps a natural transformation.
Both exact termwise functors invert quasi-isomorphisms. Use the localization universal
property with the displayed evaluation and pullback factorizations. Full faithfulness
of precomposition gives existence and uniqueness of the derived transformation. Its
type enforces naturality at every derived morphism, including inverses of localized
quasi-isomorphisms. No component of alpha is required to be invertible. -/
theorem descent (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (_hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :
    ∃! αD : evaluation D (Padic.coefficientExtensionRing l E n) ⟶
        derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
          evaluation D (Padic.coefficientExtensionRing l E n),
      ∀ K : CochainComplex (modules D (Padic.coefficientExtensionRing l E n)) ℤ,
        αD.app (DerivedCategory.Q.obj K) ≫
          (evaluation D (Padic.coefficientExtensionRing l E n)).map
            ((pullbackFactors D (Padic.coefficientExtensionRing l E n) (r + 1)).hom.app K) ≫
          (evaluationFactors D (Padic.coefficientExtensionRing l E n)).hom.app
            (((pullback D (Padic.coefficientExtensionRing l E n) (r + 1)).mapHomologicalComplex
              (.up ℤ)).obj K) =
        (evaluationFactors D (Padic.coefficientExtensionRing l E n)).hom.app K ≫
          DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) := by
  exact descendExactTransformation
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n))
    (pullback D (Padic.coefficientExtensionRing l E n) (r + 1))
    (evaluation D (Padic.coefficientExtensionRing l E n))
    (derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1))
    (evaluationFactors D (Padic.coefficientExtensionRing l E n))
    (pullbackFactors D (Padic.coefficientExtensionRing l E n) (r + 1)) α

/-- The unique ambient descent characterized by `descent`, with no choice of its maps.
Source: Stacks Tag 04VG, localization of natural transformations
(blueprint: lem-trf-point-exact-derived-model). -/
def descendedTransformation (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :
    evaluation D (Padic.coefficientExtensionRing l E n) ⟶
      derivedPullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        evaluation D (Padic.coefficientExtensionRing l E n) :=
  Classical.choose (descent D l hl E Ω _ι n hn r α).exists

/-- Restrict the same derived transformation to the full bounded constructible source.
No maps are chosen anew: whiskering retains every component and every naturality square.
The target is viewed in the ambient D(A), as in `evaluation_restriction`.
Source: Stacks Tag 04VG and blueprint `def-weil-finite-coefficient-point`, clause 1
(blueprint: lem-trf-point-exact-derived-model). -/
def restrictedTransformation (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (α : pointFiniteSections D.k (Padic.coefficientExtensionRing l E n) ⟶
      pullback D (Padic.coefficientExtensionRing l E n) (r + 1) ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
  Functor.whiskerLeft
    (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).ι
    (descendedTransformation D l hl E Ω _ι n hn r α)

end WeilConjectures.PointExactDerivedModel
