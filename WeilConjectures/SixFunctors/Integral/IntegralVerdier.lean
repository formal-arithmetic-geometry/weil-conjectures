/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomComparisonIsIso
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomRoosTransport
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBounds
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBiduality
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierReductionPairing
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Integral Verdier biduality

Source: blueprint thm-coef-integral-verdier.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

namespace WeilConjectures

private theorem comparison_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)} {n : ℕ}
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (K : IntegralVerdier.Ambient l E X) :
    IntegralVerdier.comparison l E X D hl m ω r K =
      IntegralHom.comparison l E X D hl m K ω.obj ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K)))
            (r n).hom) := by
  rfl

private theorem dual_equivalence {C : Type u} [Category.{v} C]
    (D : Cᵒᵖ ⥤ C) (e : 𝟭 C ≅ D.rightOp ⋙ D) : D.IsEquivalence := by
  let : (D.rightOp ⋙ D).IsEquivalence := Functor.isEquivalence_of_iso e
  let : D.rightOp.Faithful := Functor.Faithful.of_comp D.rightOp D
  have : D.Faithful := by
    constructor
    intro X Y f g h
    apply Quiver.Hom.unop_inj
    apply D.rightOp.map_injective
    exact congrArg Quiver.Hom.op h
  have : D.rightOp.Full := Functor.Full.of_comp_faithful D.rightOp D
  have : D.Full := by
    constructor
    intro X Y f
    refine ⟨(D.rightOp.preimage f.op).op, ?_⟩
    exact Quiver.Hom.op_inj (D.rightOp.map_preimage f.op)
  have : D.EssSurj := by
    constructor
    intro X
    exact ⟨D.rightOp.obj X, ⟨(e.app X).symm⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

private theorem adjunction_transpose_post
    {C : Type u} {D : Type v} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {A : C} {B B' : D} (q : L.obj A ⟶ B) (r : B ⟶ B') :
    L.map (a.homEquiv A B q ≫ R.map r) ≫ a.counit.app B' = q ≫ r := by
  rw [← Adjunction.homEquiv_naturality_right]
  exact (a.homEquiv A B').symm_apply_apply (q ≫ r)

private theorem adjunction_baseChange_transpose
    {C : Type u} {D : Type v} [Category C] [Category D]
    {L R : C ⥤ C} {L' R' : D ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (F : C ⥤ D) (mu : L ⋙ F ≅ F ⋙ L')
    {V M : C} (f : L.obj V ⟶ M) :
    F.map (a.homEquiv V M f) ≫
        b.homEquiv (F.obj (R.obj M)) (F.obj M)
          (mu.inv.app (R.obj M) ≫ F.map (a.counit.app M)) =
      b.homEquiv (F.obj V) (F.obj M) (mu.inv.app V ≫ F.map f) := by
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  have hn := mu.inv.naturality (a.homEquiv V M f)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp]
  congr 2
  exact (a.homEquiv V M).symm_apply_apply f

private theorem adjunction_baseChange_transpose_post
    {C : Type u} {D : Type v} [Category C] [Category D]
    {L R : C ⥤ C} {L' R' : D ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (F : C ⥤ D) (mu : L ⋙ F ≅ F ⋙ L')
    {V M : C} {N : D} (f : V ⟶ R.obj M) (r : F.obj M ⟶ N) :
    b.homEquiv (F.obj V) N
        (mu.inv.app V ≫ F.map ((a.homEquiv V M).symm f) ≫ r) =
      F.map f ≫ b.homEquiv (F.obj (R.obj M)) (F.obj M)
        (mu.inv.app (R.obj M) ≫ F.map (a.counit.app M)) ≫ R'.map r := by
  have h := adjunction_baseChange_transpose a b F mu ((a.homEquiv V M).symm f)
  simp only [Equiv.apply_symm_apply] at h
  calc
    _ = b.homEquiv (F.obj V) (F.obj M)
        (mu.inv.app V ≫ F.map ((a.homEquiv V M).symm f)) ≫ R'.map r := by
      rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    _ = _ := by rw [← h, Category.assoc]

private theorem adjunction_tensor_baseChange_transpose_post
    {C : Type u} {D : Type v} [Category C] [Category D]
    (T : C × C ⥤ C) (T' : D × D ⥤ D) (F : C ⥤ D)
    (mu : T ⋙ F ≅ F.prod F ⋙ T') (K : C)
    {R : C ⥤ C} {R' : D ⥤ D}
    (a : (Functor.curry.obj T).obj K ⊣ R)
    (b : (Functor.curry.obj T').obj (F.obj K) ⊣ R')
    {V M : C} {N : D} (f : V ⟶ R.obj M) (r : F.obj M ⟶ N) :
    b.homEquiv (F.obj V) N
        (mu.inv.app (K, V) ≫ F.map ((a.homEquiv V M).symm f) ≫ r) =
      F.map f ≫ b.homEquiv (F.obj (R.obj M)) (F.obj M)
        (mu.inv.app (K, R.obj M) ≫ F.map (a.counit.app M)) ≫ R'.map r := by
  let μ : (Functor.curry.obj T).obj K ⋙ F ≅
      F ⋙ (Functor.curry.obj T').obj (F.obj K) :=
    NatIso.ofComponents (fun V ↦ mu.app (K, V)) (by
      intro V W f
      simpa using mu.hom.naturality (Prod.mkHom (𝟙 K) f))
  simpa only [μ, NatIso.ofComponents_inv_app, Iso.app_inv] using
    adjunction_baseChange_transpose_post a b F μ f r

private theorem sfComplete_zero (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K)
    (hz : ∀ n : ℕ, IsZero ((scalarReductionDerivedExtension l E X n).obj K)) :
    IsZero K := by
  obtain ⟨hp, δ, hδ⟩ := hK
  let := hp
  have hzero (n : ℕ) : IsZero ((sfDerivedReductionRestricted l E X n).obj K) := by
    let : PreservesFiniteLimits (scalarReductionRestriction l E X n) :=
      (scalarReductionRestriction_exact l E X n).1
    let : PreservesFiniteColimits (scalarReductionRestriction l E X n) :=
      (scalarReductionRestriction_exact l E X n).2
    let : (scalarReductionDerivedRestriction l E X n).Additive :=
      inferInstanceAs (scalarReductionRestriction l E X n).mapDerivedCategory.Additive
    exact (scalarReductionDerivedRestriction l E X n).map_isZero (hz n)
  have hprod : IsZero (∏ᶜ fun n ↦ (sfDerivedReductionRestricted l E X n).obj K) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro n
    exact (hzero n).eq_of_tgt _ _
  exact Triangle.isZero₁_of_isIso₂ _ hδ (hprod.isIso hprod _)

set_option linter.style.haveILetI false in
private theorem sfComplete_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {K L : IntegralVerdier.Ambient l E X} (f : K ⟶ L)
    (hK : IsSfDerivedComplete l E X K) (hL : IsSfDerivedComplete l E X L)
    (hf : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E X n).map f)) :
    IsIso f := by
  let P : ObjectProperty (IntegralVerdier.Ambient l E X) := IsSfDerivedComplete l E X
  have : P.IsTriangulated := sf_complete_tri l E X
  have : P.IsClosedUnderIsomorphisms := sf_complete_iso l E X
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hC : IsSfDerivedComplete l E X C :=
    P.ext_of_isTriangulatedClosed₃ _ hT hK hL
  apply (Triangle.isZero₃_iff_isIso₁ _ hT).mp
  apply sfComplete_zero l E X C hC
  intro n
  obtain ⟨hshift, htri⟩ :=
    (scalarReductionDerivedExistence.{u, u} l E X n).choose_spec.choose_spec.2.1
  let F := scalarReductionDerivedExtension l E X n
  letI : F.CommShift ℤ := hshift
  have : F.IsTriangulated := htri
  exact Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ hT) (hf n)

private theorem tensorTranspose_source (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (he : ∀ (K K' W : IntegralHom.Derived.{u, u} X R) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
          (a.adjunction K').counit.app W =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (T P P' Q : IntegralHom.Derived.{u, u} X R) (f : P' ⟶ P)
    (g : a.tensor.obj (P, T) ⟶ Q) :
    (a.adjunction P').homEquiv T Q (a.tensor.map (Prod.mkHom f (𝟙 T)) ≫ g) =
      (a.adjunction P).homEquiv T Q g ≫
        (IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 Q)) := by
  apply (a.adjunction P').homEquiv T Q |>.symm.injective
  rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change _ = a.tensor.map (Prod.mkHom (𝟙 P') ((a.adjunction P).homEquiv T Q g)) ≫
    a.tensor.map (Prod.mkHom (𝟙 P')
      ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 Q)))) ≫
    (a.adjunction P').counit.app Q
  rw [he, ← Category.assoc]
  have hc : a.tensor.map (Prod.mkHom (𝟙 P') ((a.adjunction P).homEquiv T Q g)) ≫
      a.tensor.map (Prod.mkHom f (𝟙 _)) =
      a.tensor.map (Prod.mkHom f (𝟙 T)) ≫
        a.tensor.map (Prod.mkHom (𝟙 P) ((a.adjunction P).homEquiv T Q g)) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [hc, Category.assoc]
  congr 1
  exact ((a.adjunction P).homEquiv T Q |>.symm_apply_apply g).symm

private theorem signed_delta_natural (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (s : IntegralVerdier.SignedSymmetry X R a)
    (hnat : ∀ (K L K' L' : IntegralHom.Derived.{u, u} X R)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : IntegralHom.Derived.{u, u} X R) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
          (a.adjunction K').counit.app W =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (ω K L : IntegralHom.Derived.{u, u} X R) (f : K ⟶ L) :
    f ≫ IntegralVerdier.delta X a s ω L = IntegralVerdier.delta X a s ω K ≫
      (IntegralHom.hom.{u, u} X R).map (Prod.mkHom
        ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 ω))).op (𝟙 ω)) := by
  unfold IntegralVerdier.delta restrictionDualDelta restrictionDualEvaluation
  rw [← Adjunction.homEquiv_naturality_left, ← tensorTranspose_source X a he]
  congr 1
  change a.tensor.map (Prod.mkHom (𝟙 _) f) ≫
      (s.swap _ _).hom ≫ (a.adjunction L).counit.app ω =
    a.tensor.map (Prod.mkHom
      ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 ω))) (𝟙 K)) ≫
      (s.swap _ _).hom ≫ (a.adjunction K).counit.app ω
  rw [← Category.assoc, hnat, Category.assoc, ← he L K ω f]
  symm
  rw [← Category.assoc, hnat, Category.assoc]
  rfl

/-- Integral Verdier biduality for the dualizing object with its reductions
supplied by prop-coef-integral-dualizing. The finite terms and their
transition adjuncts are the exceptional inverse images of the coefficient units.
The conclusion states equality of the constructible and finite-Tor categories,
exact anti-equivalence, canonical reduction and Roos reconstruction, the uniform
Tor bound, and invertibility and naturality of the evaluation-defined double dual.

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2146
(blueprint: thm-coef-integral-verdier).

Proof plan, following all eight steps of the node:
1. Choose a cohomological interval containing the residue reduction of K.
   lem-coef-integral-residue-tor gives this same Tor interval at every positive
   level. This proves equality with the uniform finite-Tor subcategory. Choose
   a nonnegative dimension bound by lem-kun-dimension-finite-type; for the empty
   scheme take zero.
2. prop-coef-integral-dualizing makes omega complete with its specified coherent
   finite reductions. Apply lem-coef-integral-hom-reduction to K and omega.
   Ambient RHom is complete, and the evaluation-defined comparisons are invertible.
   Their defining transpose equations give evaluation and transpose compatibility.
3. lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude give
   finite etale origins with the input Tor interval. Apply
   lem-weil-verdier-preservation-strata and then
   lem-weil-finite-duality-site-comparison. The output reductions are constructible
   with Tor interval [-b-2d,-a], hence have cohomology in that same interval.
   Completeness and these bounds are precisely sfIntegralConstructible.
4. Take the actual Roos triangle of the complete ambient Hom. The comparisons
   identify each restricted reduction with the finite dual. Their evaluation and
   transpose equations identify finite evaluation's transition with conjugation
   by these comparisons. The product of the comparisons intertwines 1-s, checked
   on each projection. Transport the Roos triangle, including its specified first
   legs; this is def-weil-derived-limit, without choosing a second limit model.
5. Ringed-site internal-Hom exactness, lem-pur-rhom-global-sections and the
   inherited triangulation of lem-weil-integral-constructible-triangulated give
   exactness. The sheaf tensor symmetry with sign (-1)^(ij) descends on K-flats.
   Transpose evaluation after this symmetry to obtain delta. Evaluation naturality
   makes both sides of delta's naturality square have the same transpose.
6. Apply the Hom reduction comparison twice, using preservation for DK. Its
   evaluation and transpose equations carry the actual reduced delta to the
   finite delta of lem-weil-duality-pairing. This map is invertible by
   thm-fix-general-biduality, since the reductions are finite-Tor constructible.
7. The cone of delta is constructible and complete by triangulated closure.
   Exact derived reduction (lem-pur-derived-change-of-rings) makes every reduction
   of the cone zero. Its Roos triangle then has two zero product vertices, so
   lem-kun-distinguished-cone-zero kills the cone and makes delta invertible.
8. Uncurrying D(delta_K) composed with delta_DK gives evaluation itself, by
   evaluation naturality and the two inverse signed symmetries. Thus that
   composite is the identity. Naturality and invertibility of delta give full
   faithfulness: a map v:DL to DK has preimage delta_K followed by Dv and the
   inverse of delta_L. Every L is isomorphic to D(DL), proving essential
   surjectivity. Together with step 5 this is the exact anti-equivalence.
-/
theorem integral_verdier_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) :
    IntegralVerdier.Conclusion l E X D hl ω r := by
  classical
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  have categories := (integral_residue_tor D l hl E X).2
  obtain ⟨tensor, signed, reduction, finiteSigned, signed_swap_natural,
    evaluation_natural, finiteSigned_swap_natural, finite_evaluation_natural⟩ :=
    IntegralVerdier.signedCalculus D l hl E X
  have complete := IntegralHom.hom_roosTransport l E X D hl tensor
  have reduction_iso (n : ℕ) (K L : IntegralVerdier.Ambient l E X) :=
    IntegralHom.comparison_isIso l E X D hl tensor n (reduction n) K L
  unfold IntegralVerdier.Conclusion
  have dual_complete (K : IntegralVerdier.Ambient l E X) :
      IsSfDerivedComplete l E X ((IntegralVerdier.dual l E X ω.obj).obj (op K)) :=
    (sfDerivedComplete_iff_legacy l E X D hl _).mpr
      (complete K ω.obj ((sfDerivedComplete_iff_legacy l E X D hl _).mp ω.property.1))
  have comparison_iso (K : IntegralVerdier.Ambient l E X) (n : ℕ) :
      IsIso (IntegralVerdier.comparison l E X D hl (reduction n) ω r K) := by
    have : IsIso (IntegralHom.comparison l E X D hl (reduction n) K ω.obj) :=
      reduction_iso n K ω.obj
    rw [comparison_eq]
    have : IsIso (Prod.mkHom
        (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K))) (r n).hom) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    infer_instance
  have preserves (K : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E X ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj)) := by
    have torK : finiteTorConstructibleIntegral l E X K.obj := categories ▸ K.property
    obtain ⟨a, b, hab, htor⟩ := torK.2
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
    refine ⟨dual_complete K.obj, -b - 2 * (d : ℤ), -a, by omega, fun n ↦ ?_⟩
    have hf := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X n _
      (K.property.2.choose_spec.choose_spec.2 n).1 d hd a b (htor n)
    let e := @asIso _ _ _ _
      (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj)
      (comparison_iso K.obj n)
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
      (proEtale_bounded_constructible_isTriangulated X
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨ObjectProperty.prop_of_iso _ e.symm hf.1, ?_⟩
    intro i hi
    apply hf.2.2
    intro hz
    exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mpr hz)
  have signed_natural := signed_delta_natural X tensor signed
    signed_swap_natural evaluation_natural
  have pairing := IntegralVerdier.reductionPairing D l hl E X tensor signed
    signed_swap_natural reduction finiteSigned finiteSigned_swap_natural evaluation_natural
    finite_evaluation_natural ω r comparison_iso
  have delta_iso (K : sfIntegralConstructibleCategory l E X) :
      IsIso (IntegralVerdier.delta X tensor signed ω.obj K.obj) := by
    apply sfComplete_iso l E X _ K.property.1
      (dual_complete ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj)))
    intro n
    have torK : finiteTorConstructibleIntegral l E X K.obj := categories ▸ K.property
    obtain ⟨a, b, hab, htor⟩ := torK.2
    have := IntegralVerdier.finiteIntrinsicVerdier_biduality D l hl E X n
      (reduction n).target (finiteSigned n) (finiteSigned_swap_natural n)
      (finite_evaluation_natural n) _
      (K.property.2.choose_spec.choose_spec.2 n).1 a b (htor n)
    have hc : IsIso (IntegralVerdier.comparison l E X D hl (reduction n) ω r
        ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj))) := comparison_iso _ n
    have hcK := comparison_iso K.obj n
    have hi : IsIso (Prod.mkHom
        (@asIso _ _ _ _
          (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj) hcK).inv.op
        (𝟙 (integralDualizingFiniteTerm l E D X n))) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    have hm := (IntegralHom.hom.{u, u} X
      (integralCoefficientCommRingSheaf l E X n)).map_isIso
        (Prod.mkHom (@asIso _ _ _ _
          (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj) hcK).inv.op
          (𝟙 (integralDualizingFiniteTerm l E D X n)))
    have hcomp : IsIso ((scalarReductionDerivedExtension l E X n).map
        (IntegralVerdier.delta X tensor signed ω.obj K.obj) ≫
        IntegralVerdier.comparison l E X D hl (reduction n) ω r
          ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj)) ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (@asIso _ _ _ _
            (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj) hcK).inv.op
            (𝟙 (integralDualizingFiniteTerm l E D X n)))) := (pairing.2 K.obj n) ▸ this
    exact IsIso.of_isIso_comp_right _
      (IntegralVerdier.comparison l E X D hl (reduction n) ω r
        ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj)) ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (@asIso _ _ _ _
            (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj) hcK).inv.op
            (𝟙 (integralDualizingFiniteTerm l E D X n))))
  refine ⟨tensor, signed, reduction, finiteSigned, categories, preserves, ?_, ?_,
    (fun K n ↦ comparison_iso K.obj n), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let Dv := IntegralVerdier.restrictedDual l E X ω.obj preserves
    have hδ (K : sfIntegralConstructibleCategory l E X) :
        IsIso (ObjectProperty.homMk
          (IntegralVerdier.delta X tensor signed ω.obj K.obj) :
          K ⟶ (Dv.rightOp ⋙ Dv).obj K) := by
      apply (ObjectProperty.isIso_hom_iff _).mp
      exact delta_iso K
    let e : 𝟭 (sfIntegralConstructibleCategory l E X) ≅ Dv.rightOp ⋙ Dv :=
      NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (ObjectProperty.homMk
        (IntegralVerdier.delta X tensor signed ω.obj K.obj)) (hδ K)) (by
          intro K L f
          apply ObjectProperty.hom_ext
          exact signed_natural ω.obj K.obj L.obj f.hom)
    exact dual_equivalence Dv e
  · obtain ⟨s, hs⟩ :=
      (@CategoryTheory.RingedHomUniverses.ringedInternalHom_exact.{u + 1, u, u, u + 2}
        X.ProEt inferInstance (ProEt.topology X) inferInstance inferInstance
        (completedIntegralCommRingSheaf l E X D hl) (HasDerivedCategory.standard _)).1 ω.obj
    let : (IntegralVerdier.dual l E X ω.obj).CommShift ℤ := s
    have : (IntegralVerdier.dual l E X ω.obj).IsTriangulated := hs
    refine ⟨s, ?_⟩
    intro T _ _ _ hT
    exact (IntegralVerdier.dual l E X ω.obj).map_distinguished T hT
  · intro K n
    simpa only [IntegralVerdier.comparison, IntegralVerdier.dual,
      Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
      Functor.id_obj, Category.assoc] using
      adjunction_transpose_post
        (A := (scalarReductionDerivedExtension l E X n).obj
          ((IntegralVerdier.dual l E X ω.obj).obj (op K.obj)))
        ((reduction n).target.adjunction
          ((scalarReductionDerivedExtension l E X n).obj K.obj))
        ((reduction n).mu.inv.app (K.obj, (IntegralVerdier.dual l E X ω.obj).obj (op K.obj)) ≫
          (scalarReductionDerivedExtension l E X n).map
            ((tensor.adjunction K.obj).counit.app ω.obj))
        (r n).hom
  · intro K n V f
    with_unfolding_all
      simpa only [completedIntegralCommRingSheaf,
        IntegralVerdier.comparison, IntegralVerdier.dual,
        Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
        Functor.id_obj] using
        adjunction_tensor_baseChange_transpose_post tensor.tensor (reduction n).target.tensor
          (scalarReductionDerivedExtension l E X n) (reduction n).mu K.obj
          (tensor.adjunction K.obj)
          ((reduction n).target.adjunction
            ((scalarReductionDerivedExtension l E X n).obj K.obj)) f (r n).hom
  · exact fun K n ↦ pairing.1 K.obj n
  · intro K
    let W := (IntegralVerdier.dual l E X ω.obj).obj (op K.obj)
    let e := IntegralVerdier.restrictedComparison l E X D hl reduction ω r K.obj
      (comparison_iso K.obj)
    apply roos_transport
      (fun n ↦ (sfDerivedReductionTransition l E X n).app W)
      (IntegralVerdier.finiteTransition l E X D hl reduction ω r K.obj
        (comparison_iso K.obj))
      (Iso.refl W) e
      (fun n ↦ (sfDerivedReductionUnit l E X n).app W)
      (IntegralVerdier.finiteLeg l E X D hl reduction ω r K.obj (comparison_iso K.obj))
    · intro n
      simp [IntegralVerdier.finiteTransition, e, W]
    · intro n
      simp [IntegralVerdier.finiteLeg, e, W]
    · exact dual_complete K.obj
  · intro K d hd a b hab htor n
    have hf := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E X n _
      (K.property.2.choose_spec.choose_spec.2 n).1 d hd a b (htor n)
    let e := @asIso _ _ _ _
      (IntegralVerdier.comparison l E X D hl (reduction n) ω r K.obj)
      (comparison_iso K.obj n)
    refine ⟨hf.2.1.1, ?_⟩
    intro L P hL f hf' hP M i hi
    exact hf.2.1.2 L P (hL.map (fun eL ↦ eL ≪≫ e)) f hf' hP M i hi
  · exact fun K n ↦ pairing.2 K.obj n
  · exact delta_iso
  · exact fun K L f ↦ signed_natural ω.obj K.obj L.obj f.hom

end WeilConjectures
