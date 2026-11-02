/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.Algebra.Homology.PoincareDuality.TensorTrilinearUniversal
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Ordinary signed-line scalar evaluation

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3), evaluation compatibility.
(blueprint: lem-pur-completed-line-ordinary-evaluation)

The normalized ordinary comparisons preserve evaluation before completion. This is
the ordinary square used to prove the completed evaluation square by conjugation.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

section SheafSquare

/-- Ordinary completed scalar extension is left adjoint to restriction, with unit `1 ⊗ x`.
Source: Stacks 03D7 (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem scalarAdjunction :
    ∃ a : completedOrdinaryScalarExtension l E F ι X ⊣
        SheafOfModules.restrictScalars
          ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
            (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E F ι X)),
      ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = completedScalarTensorSection l E F ι X M U 1 x := by
  obtain ⟨a, ha⟩ :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
      (completedCoefficientMap l E F ι X)).choose_spec.choose_spec
        (completedOrdinaryScalarExtension l E F ι X)
        (completedOrdinaryScalarExtension_obj l E F ι X)
        (fun f ↦ completedOrdinaryScalarExtension_map l E F ι X f)
  refine ⟨a, ?_⟩
  intro M U x
  let e := eqToIso (completedOrdinaryScalarExtension_obj l E F ι X M)
  have h := ha M ((completedOrdinaryScalarExtension l E F ι X).obj M) e.inv U x
  have he : eqToHom (completedOrdinaryScalarExtension_obj l E F ι X M) ≫ e.inv = 𝟙 _ :=
    e.hom_inv_id
  rw [he, Adjunction.homEquiv_id] at h
  dsimp only [completedScalarTensorSection, e, eqToIso.inv,
    completedOrdinaryScalarExtension] at h ⊢
  with_unfolding_all exact h

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] completedScalarTensorSection in
/-- Coefficient scalars pass through the scalar-extension generator `1 ⊗ x`.
Source: Stacks 03EK, balancing (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem scalarTensorSection_smul (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (p : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) (x : M.val.obj U) :
    smul l F X ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        ((completedCoefficientMap l E F ι X).hom.app U p)
        (completedScalarTensorSection l E F ι X M U 1 x) =
      completedScalarTensorSection l E F ι X M U 1 (smul l E X M U p x) := by
  letI : Module ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) (M.val.obj U) :=
    (M.val.obj U).isModule
  let η := ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (R := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (completedIntegralCommRingSheafUnrestricted l F X))
    (𝟙 _)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} (completedCoefficientMap l E F ι X) M)).app U
  have h := η.hom.map_smul ((completedCoefficientMap l E F ι X).hom.app U p)
    ((1 : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) ⊗ₜ[
      (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
      ((completedCoefficientMap l E F ι X).hom.app U).hom] x)
  unfold smul completedScalarTensorSection
  refine (LinearMap.map_smul _ _ _).symm.trans ?_
  refine congrArg _ (h.symm.trans ?_)
  refine congrArg _ ?_
  show ((completedCoefficientMap l E F ι X).hom.app U p * 1) ⊗ₜ[
      (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
      ((completedCoefficientMap l E F ι X).hom.app U).hom] x =
    (1 : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) ⊗ₜ[
      (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
      ((completedCoefficientMap l E F ι X).hom.app U).hom] (p • x)
  rw [TensorProduct.tmul_smul]
  rfl

/-- Normalized line comparisons multiply the signed pairing by the coefficient map.
Source: Stacks 03EO; blueprint Proof (3), pairing clause of `IsPairNormalized`
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: at zero both lines are the unit comparison and pairing is multiplication; for a
positive exponent this is the pairing clause; for a negative exponent apply that clause
with the two factors interchanged. -/
private theorem pairing_line (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (U : X.ProEtᵒᵖ) (p : (power l E X L m).val.obj U)
    (q : (power l E X L (-m)).val.obj U) :
    pairing l F X N m U
        ((d.line m).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 p))
        ((d.line (-m)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 q)) =
      (completedCoefficientMap l E F ι X).hom.app U (pairing l E X L m U p q) := by
  rcases m with (_ | n) | n
  · have h0 : (d.line (Int.ofNat 0)).hom = ((binary l E X F ι).power L 0).hom ≫
        SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
          (completedIntegralCommRingSheafUnrestricted l F X) b.hom 0 := hd.1 0
    have h0' : (d.line (-Int.ofNat 0)).hom = ((binary l E X F ι).power L 0).hom ≫
        SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
          (completedIntegralCommRingSheafUnrestricted l F X) b.hom 0 := hd.1 0
    have hp (r : (power l E X L (Int.ofNat 0)).val.obj U) :
        (d.line (Int.ofNat 0)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 r) =
          (1 * (completedCoefficientMap l E F ι X).hom.app U r :
            (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) := by
      rw [h0]
      exact SheafOfModules.scalarExtensionUnitIso_tmul (completedCoefficientMap l E F ι X) U 1 r
    have hq (r : (power l E X L (-Int.ofNat 0)).val.obj U) :
        (d.line (-Int.ofNat 0)).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) _ U 1 r) =
          (1 * (completedCoefficientMap l E F ι X).hom.app U r :
            (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) := by
      rw [h0']
      exact SheafOfModules.scalarExtensionUnitIso_tmul (completedCoefficientMap l E F ι X) U 1 r
    change (@id ((completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) _) *
        (@id ((completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) _) =
      (completedCoefficientMap l E F ι X).hom.app U
        ((@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) p) *
          (@id ((completedIntegralCommRingSheafUnrestricted l E X).obj.obj U) q))
    rw [hp, hq]
    have hm : ∀ p' q' : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
        (1 * (completedCoefficientMap l E F ι X).hom.app U p') *
          (1 * (completedCoefficientMap l E F ι X).hom.app U q') =
        (completedCoefficientMap l E F ι X).hom.app U (p' * q') := by
      intro p' q'
      rw [one_mul, one_mul, map_mul]
    exact hm p q
  · have h := hd.2.1 n U 1 1 q p
    rw [one_mul, one_mul] at h
    exact h
  · have h := hd.2.1 n U 1 1 p q
    rw [one_mul, one_mul] at h
    exact h

/-- The ordinary sheaf square: the normalized ordinary comparisons preserve evaluation.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: transpose along the scalar-extension adjunction and test on nested pure
tensors `(x ⊗ p) ⊗ q`. The comparisons move the line factors past the scalar, the
evaluation multiplies by the pairing, and `pairing_line` identifies that scalar with
the image of the original pairing. -/
private theorem sheaf_square (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (M : integralTowerModules l E X) :
    (d.ordinarySheaf (-m)).hom.app ((sheaf l E X L m).obj M) ≫
      (sheaf l F X N (-m)).map ((d.ordinarySheaf m).hom.app M) ≫
      (evaluation l F X N m).hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) =
    (completedOrdinaryScalarExtension l E F ι X).map ((evaluation l E X L m).hom.app M) := by
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  obtain ⟨a, ha⟩ := scalarAdjunction l E X F ι
  apply (a.homEquiv _ _).injective
  obtain ⟨_, _, _, hext⟩ := SheafOfModules.tensor_trilinear_universal
    (completedIntegralCommRingSheafUnrestricted l E X)
  apply (hext M (power l E X L m) (power l E X L (-m)) _ _ _).2
  intro U x p q
  let O := completedOrdinaryScalarExtension l E F ι X
  let Z := (sheaf l E X L (-m)).obj ((sheaf l E X L m).obj M)
  let y : Z.val.obj U := tmul l E X L (-m) ((sheaf l E X L m).obj M) U (tmul l E X L m M U x p) q
  have key (T : integralTowerModules l F X) (f : O.obj Z ⟶ T) :
      (a.homEquiv _ _ f).val.app U y = f.val.app U (completedScalarTensorSection l E F ι X Z U 1 y) := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (fun z ↦ f.val.app U z) (ha Z U y)
  change (a.homEquiv _ _ _).val.app U y = (a.homEquiv _ _ _).val.app U y
  rw [key, key]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have ha' := hd.2.2.1 (-m) ((sheaf l E X L m).obj M) U 1 (tmul l E X L m M U x p) q
  have hc := hd.2.2.1 m M U 1 x p
  have hevF := (evaluation_existsUnique l F X N m).exists.choose_spec (O.obj M) U
    (completedScalarTensorSection l E F ι X M U 1 x)
    ((d.line m).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 p))
    ((d.line (-m)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 q))
  have hevE := (evaluation_existsUnique l E X L m).exists.choose_spec M U x p q
  have hb := SheafOfModules.map_tmul_first (completedIntegralCommRingSheafUnrestricted l F X)
    ((d.ordinarySheaf m).hom.app M) U
    (completedScalarTensorSection l E F ι X ((sheaf l E X L m).obj M) U 1
      (tmul l E X L m M U x p))
    ((d.line (-m)).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) _ U 1 q))
  rw [ha']
  erw [hb]
  rw [hc]
  erw [hevF]
  rw [pairing_line l E X F ι L N b d hd m U p q, scalarTensorSection_smul]
  exact (congrArg (completedScalarTensorSection l E F ι X M U 1) hevE.symm).trans
    (completedScalarTensorSection_naturality l E F ι X ((evaluation l E X L m).hom.app M)
      U 1 y).symm

end SheafSquare

section DerivedSquare

/-- Signed evaluation applied termwise to a complex.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private def evaluationComplex (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (complex l E X L (-m)).obj ((complex l E X L m).obj K) ⟶ K where
  f i := (evaluation l E X L m).hom.app (K.X i)
  comm' i j _ := ((evaluation l E X L m).hom.naturality (K.d i j)).symm

/-- The derived evaluation on a representative is the termwise evaluation.
Source: Stacks 06YY, localization of exact functors
(blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem epsilon_app_Q (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (epsilon l E X L m).hom.app (DerivedCategory.Q.obj K) =
      (tensor l E X L (-m)).map ((factors l E X L m).hom.app K) ≫
        (factors l E X L (-m)).hom.app ((complex l E X L m).obj K) ≫
        DerivedCategory.Q.map (evaluationComplex l E X L m K) := by
  have h1 := Functor.mapDerivedCategoryCompIso_fac (sheaf l E X L m) (sheaf l E X L (-m)) K
  have h2 := Functor.mapDerivedCategoryNatIso_fac (evaluation l E X L m) K
  have h3 := Functor.mapDerivedCategoryIdIso_hom_app_Q_obj K
  have h4 : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (sheaf l E X L m ⋙ sheaf l E X L (-m))) (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex (evaluation l E X L m).hom (ComplexShape.up ℤ)).app K =
      evaluationComplex l E X L m K := by
    ext i
    simp [evaluationComplex]
  simp only [epsilon, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [h3, h2, ← h1, ← h4]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

/-- Termwise ordinary comparisons commute with termwise evaluation.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem chain_square (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (K : CochainComplex (integralTowerModules l E X) ℤ) :
    (comparisonComplex l E X F ι L N (-m) (d.ordinarySheaf (-m))).hom.app
        ((complex l E X L m).obj K) ≫
      (complex l F X N (-m)).map
        ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app K) ≫
      evaluationComplex l F X N m ((completedOrdinaryScalarComplex l E F ι X).obj K) =
    (completedOrdinaryScalarComplex l E F ι X).map (evaluationComplex l E X L m K) := by
  ext i
  exact sheaf_square l E X F ι L N b d hd m (K.X i)

attribute [local semireducible] completedScalarCounit completedDerivedScalarExtension
  completedOrdinaryScalarComplex completedOrdinaryScalarExtension completedScalarChangeData in
/-- Naturality of the universal counit for chain maps.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem counit_naturality {K K' : CochainComplex (integralTowerModules l E X) ℤ}
    (g : K ⟶ K') :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l E F ι X K' =
      completedScalarCounit l E F ι X K ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map g) :=
  ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec.choose_spec.2.2
    |>.choose_spec.choose).naturality ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g)

attribute [local semireducible] completedScalarCounit completedDerivedScalarExtension
  completedOrdinaryScalarComplex completedOrdinaryScalarExtension completedScalarChangeData in
/-- The universal counit is invertible on K-flat complexes.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem counit_isIso (K : CochainComplex (integralTowerModules l E X) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) K) :
    IsIso (completedScalarCounit l E F ι X K) :=
  ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec.choose_spec.2.2
    |>.choose_spec.choose_spec).2.2 K hK

/-- Every complex has a good quasi-isomorphic resolution.
Source: Stacks 06YS (blueprint: lem-pur-completed-line-ordinary-evaluation). -/
private theorem good_resolution (c : CochainComplex (integralTowerModules l E X) ℤ) :
    ∃ (P : (integralOperationsGoodComplex l E X).FullSubcategory) (r : P.obj ⟶ c),
      QuasiIso r := by
  obtain ⟨Y, r, hY, hf, hr, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients c
  refine ⟨⟨Y, hY, fun n ↦ ?_⟩, r, hr⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso _ (Y.X n)).symm (hf n)

end DerivedSquare

/-- The ordinary scalar comparison respects the specified signed-line evaluation.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3), inverse-pair compatibility
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: first check the ordinary sheaf square on sections. The two scalar-line
comparisons move the two line factors past the scalar factor. Evaluation then
multiplies by the image of their pairing. For positive exponents this is precisely
IsPairNormalized's negative pairing clause; for negative exponents interchange the
paired factors, and for zero use multiplication. The defining evaluation formula
identifies the other path with scalar extension of evaluation. Sheafified tensor
generators determine these maps. Apply the square termwise to a flat-term K-flat
representative. Exact line tensor preserves these representatives. Substitute the
universal-counit normalizations of the two ordinary comparisons and the exact
localization comparisons of evaluation. Naturality and cancellation of the invertible
K-flat counits give the derived square. Every derived object has such a resolution,
so naturality transports the equality to every unbounded object. This argument uses
ordinary derived extension only, with no completeness assumption. -/
theorem ordinary_evaluation_compatibility (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X)) :
    (d.ordinary (-m)).hom.app ((tensor l E X L m).obj K) ≫
      (tensor l F X N (-m)).map
        ((d.ordinary m).hom.app K) ≫
      (epsilon l F X N m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) =
    (completedDerivedScalarExtension l E F ι X).map
      ((epsilon l E X L m).hom.app K) := by sorry

end CompletedLineTensor
end WeilConjectures
