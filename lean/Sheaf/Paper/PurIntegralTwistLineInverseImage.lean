/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.CompletedCoefficientTensorNormalization
import Sheaf.Paper.PurBaseCompletionPullbackIso
import Sheaf.Paper.PurRootTowerPreservation
import Sheaf.Paper.PurIntegralTensorTransport
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage

/-! # Inverse image of the completed integral Tate line

Source: current blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist
(blueprint: lem-pur-integral-twist-line-inverse-image).

The adjunction expresses local section formulas on the original site: the adjunct of
`rho` sends a root tensor to the pulled-back root tensor and is semilinear over the
adjunct of `alpha`. Thus no section of an inverse image is treated as a section on the
source site. Level `n` always means positive exponent `n + 1`.

## Main definitions and statement

* `IsPurIntegralCoefficientComparison`: the coefficient projection characterization.
* `IsPurRootLimitComparison`: the roots-of-unity projection characterization.
* `IsPurIntegralTwistComparison`: the tensor formula and completed semilinearity.
* `pur_integral_twist_line_inverse_image`: the isomorphisms and both naturality squares.

The coefficient and root comparison predicates below are projection-level
characterizations.  In particular, their quantification over every finite level
keeps the completed objects tied to the canonical inverse-limit constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf of the recorded completed integral twist module.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
abbrev purIntegralTwistAb (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (SheafOfModules.toSheaf _).obj (purTwistIntegralModule S l E)

/-- The underlying abelian map of the existing canonical coefficient inclusion at twist one.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def purIntegralTwistScalarMap (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F) :
    purIntegralTwistAb S l E ⟶ purIntegralTwistAb S l F :=
  ⟨(PresheafOfModules.toPresheaf _).map (twistScalarMaps l E S F ι 1).val⟩

/-- The defining finite-projection equations for the completed coefficient comparison.
The constant comparison is the recorded constant-section adjunct, with commutativity retained.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurIntegralCoefficientComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X) : Prop :=
  ∀ n : ℕ, α ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The root-limit comparison is fixed by every root projection.
Source: Roots of unity paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurRootLimitComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime]
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l) : Prop :=
  ∀ n : ℕ,
    τ ≫ limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) =
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)) ≫
          proEtaleRootsOfUnityInverseImageMap h (l ^ (n + 1))

/-- The local tensor formula and completed semilinearity, expressed under the actual
inverse-image/direct-image adjunction. The formula is stated for all local scalar sections;
for a constant scalar its direct-image comparison is the same scalar on the base change.
Source: Integral twist paragraph of the coefficient-twist blueprint
(blueprint: lem-pur-integral-twist-line-inverse-image). -/
def IsPurIntegralTwistComparison {X Y : Scheme.{u}} (h : X ⟶ Y)
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (α : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X)
    (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (ρ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
      (purIntegralTwistAb Y l E) ⟶ purIntegralTwistAb X l E) : Prop :=
  (∀ (V : Y.ProEtᵒᵖ) (b : (purTwistIntegralConstant Y l E).obj.obj V)
      (t : (purTwistZlModule Y l).val.obj V),
    (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
        (purTwistIntegralTensor Y l E V b t) =
      purTwistIntegralTensor X l E ((proEtaleBaseChange h).op.obj V)
        ((proEtaleConstantDirectImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
            V b)
        ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) τ).hom.app
          V t)) ∧
  ∀ (V : Y.ProEtᵒᵖ)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj V)
      (t : (purTwistIntegralModule Y l E).val.obj V),
    (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V
        (a • t) =
      @id ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _) α).hom.app V a) •
      @id ((purTwistIntegralModule X l E).val.obj ((proEtaleBaseChange h).op.obj V))
        ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρ).hom.app V t)

private theorem normalization_inverse {X Y : Scheme.{u}} (h : X ⟶ Y) :
    CompletedCoefficientNormalization.inverse.{u, u} h =
      proEtaleSheafInverseImage h CommRingCat.{u + 1} := by
  rfl

private theorem normalization_delta {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    CompletedCoefficientNormalization.delta.{u, u} h A =
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1} A := by
  rw [proEtaleConstantInverseImageMap, ← Adjunction.homEquiv_symm_apply]
  rfl

private theorem normalization_alpha_isIso
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : CompletedCoefficientNormalization.BaseData.{u, u} l)
    (p : CompletedCoefficientNormalization.Presentation l E d)
    (a : CompletedCoefficientNormalization.BasePullback l d h)
    (b : CompletedCoefficientNormalization.Pullback l E d p h a) : IsIso b.alpha := by
  let L := CompletedCoefficientNormalization.inverse.{u, u} h
  let δD := CompletedCoefficientNormalization.delta.{u, u} h
    (CommRingCat.of (ULift.{u + 1} (PadicInt l)))
  let δB := CompletedCoefficientNormalization.delta.{u, u} h
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
  have : IsIso a.alpha :=
    CompletedCoefficientNormalization.pur_base_completion_pullback_isIso h l d a
  have : IsIso δD := a.constant_iso _
  have : IsIso δB := a.constant_iso _
  let m := pushout.map (L.map (d.epsilon Y))
    (L.map (CompletedCoefficientNormalization.scalar l E p.integers Y))
    (d.epsilon X) (CompletedCoefficientNormalization.scalar l E p.integers X)
    a.alpha δB δD a.epsilon_square b.scalar_square
  have hm : b.change = m := by
    apply pushout.hom_ext
    · exact by simpa only [m, pushout.inl_desc] using b.change_left
    · exact by simpa only [m, pushout.inr_desc] using b.change_right
  have : IsIso m := inferInstance
  have : IsIso b.change := hm ▸ this
  have he : b.alpha = (L.mapIso (p.beta Y)).inv ≫ b.sigma.hom ≫ b.change ≫
      (p.beta X).hom := by
    rw [← b.beta_square, ← Category.assoc]
    change b.alpha = ((L.mapIso (p.beta Y)).inv ≫ (L.mapIso (p.beta Y)).hom) ≫ b.alpha
    rw [Iso.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

private theorem coefficient_comparison_ext
    {X Y : Scheme.{u}} (_h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {f g : Z ⟶ completedIntegralCommRingSheafUnrestricted l E X}
    (hfg : ∀ n, f ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
      g ≫ completedIntegralCommRingProjectionUnrestricted l E X n) : f = g := by
  let V := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply V.map_injective
  apply limit.hom_ext
  intro n
  exact (V.map_comp _ _).symm.trans
    ((congrArg V.map (hfg n.unop)).trans (V.map_comp _ _))

private theorem root_comparison_exists
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purTwistZlOne Y l) ⟶ purTwistZlOne X l,
      IsIso τ ∧ IsPurRootLimitComparison h l τ := by
  let L := proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}
  let TY := proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)
  let TX := proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)
  obtain ⟨c, hc⟩ := (proEtaleRootsOfUnityInverseImageIso h).2.1 l (Fact.out : l.Prime)
  have : ∀ j, IsIso (c.app j) := by
    intro j
    rw [hc j.unop]
    exact AlgebraicGeometry.ProEtale.spRoots_cartesian h l (j.unop + 1)
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit TY L := pur_root_tower_preservation h l
  let τ := limit.post TY L ≫ lim.map c
  refine ⟨τ, inferInstance, ?_⟩
  intro n
  change (limit.post TY L ≫ limMap c) ≫ limit.π TX (op n) = _
  rw [Category.assoc, limMap_π, limit.post_π_assoc, hc]

private theorem constant_direct_comparison_naturality
    {X Y : Scheme.{u}} (h : X ⟶ Y) {A B : CommRingCat.{u + 1}} (f : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) _).map f ≫
        proEtaleConstantDirectImageMap h CommRingCat.{u + 1} B =
      proEtaleConstantDirectImageMap h CommRingCat.{u + 1} A ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology X) _).map f) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) _).homEquiv _ _).injective
  simp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, constantSheaf, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact NatTrans.congr_app ((toSheafification (ProEt.topology X) _).naturality
    ((Functor.const X.ProEtᵒᵖ).map f)) ((proEtaleBaseChange h).op.obj V)

private theorem coefficient_scalar_square
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F)
    (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X)
    (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l F Y) ⟶
        completedIntegralCommRingSheafUnrestricted l F X)
    (hE : IsPurIntegralCoefficientComparison h l E αE)
    (hF : IsPurIntegralCoefficientComparison h l F αF) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (integralCompletedScalarMap l E F ι Y) ≫ αF =
      αE ≫ integralCompletedScalarMap l E F ι X := by
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  apply coefficient_comparison_ext h l F
  intro n
  have hp (T : Scheme.{u}) : integralCompletedScalarMap l E F ι T ≫
      completedIntegralCommRingProjectionUnrestricted l F T n =
    completedIntegralCommRingProjectionUnrestricted l E T n ≫
      integralScalarQuotientSheafMap l E F ι T n :=
    (integralCompletedScalarMap_existsUnique l E F ι T).exists.choose_spec n
  rw [Category.assoc, hF, ← L.map_comp_assoc, hp Y, L.map_comp,
    Category.assoc]
  have hn : L.map (integralScalarQuotientSheafMap l E F ι Y n) ≫
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n + 1)))) =
    proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ≫
      integralScalarQuotientSheafMap l E F ι X n :=
    proEtaleConstantInverseImageMap_naturality h _
  rw [hn, ← Category.assoc, ← hE n]
  simpa only [Category.assoc] using congrArg (fun k ↦ αE ≫ k) (hp X).symm

private theorem integral_tensor_hom_ext
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {H : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}}
    {f g : purIntegralTwistAb S l E ⟶ H}
    (hfg : ∀ V b t,
      f.hom.app V (purTwistIntegralTensor S l E V b t) =
        g.hom.app V (purTwistIntegralTensor S l E V b t)) : f = g := by
  apply ((sheafificationAdjunction (ProEt.topology S) AddCommGrpCat.{u + 1}).homEquiv
    ((SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistConstantIntegersMap S l E)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l))).presheaf) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b t => exact hfg V b t
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- Inverse image of the integral Tate line, including field-inclusion compatibility.
Source: current blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist
(blueprint: lem-pur-integral-twist-line-inverse-image).
Proof:
1. Obtain the normalized completed-coefficient pushout presentations. The base
   completion comparison is invertible by preservation of finite constant towers.
   The pushout map on the base and the two constant coefficient maps is invertible.
   Its two inclusions identify it with the normalized change map. The beta square
   then gives invertibility of the coefficient comparisons and their projections.
2. The finite root comparisons form a natural transformation and are pointwise
   invertible. Preservation of the root-tower limit makes limit.post invertible.
   Compose it with the induced map of limits; its projections are the required ones.
3. Apply normalized integral tensor transport to each coefficient field, using the
   same root comparison. This gives the tensor formula and completed semilinearity.
4. The coefficient-inclusion square follows after every finite quotient projection
   from the integral scalar-map specification and naturality of constant sections.
   For the twist square pass under adjunction and test local pure tensors. Tensor
   induction before sheafification proves these tests determine the morphism.
   The degree-one scalar-map formula and both tensor formulas reduce equality to
   naturality of the constant-section comparison for the actual integer inclusion.
   All constructions use universal properties, also on the empty scheme. -/
theorem pur_integral_twist_line_inverse_image
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F) :
    ∃ (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
          completedIntegralCommRingSheafUnrestricted l E X)
      (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l F Y) ⟶
          completedIntegralCommRingSheafUnrestricted l F X)
      (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
      (ρE : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purIntegralTwistAb Y l E) ⟶ purIntegralTwistAb X l E)
      (ρF : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
        (purIntegralTwistAb Y l F) ⟶ purIntegralTwistAb X l F),
      (IsIso αE ∧ IsPurIntegralCoefficientComparison h l E αE) ∧
      (IsIso αF ∧ IsPurIntegralCoefficientComparison h l F αF) ∧
      (IsIso τ ∧ IsPurRootLimitComparison h l τ) ∧
      (IsIso ρE ∧ IsPurIntegralTwistComparison h l E αE τ ρE) ∧
      (IsIso ρF ∧ IsPurIntegralTwistComparison h l F αF τ ρF) ∧
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (integralCompletedScalarMap l E F ι Y) ≫ αF =
        αE ≫ integralCompletedScalarMap l E F ι X ∧
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
          (purIntegralTwistScalarMap Y l E F ι) ≫ ρF =
        ρE ≫ purIntegralTwistScalarMap X l E F ι := by
  obtain ⟨d, p, q, e, hp⟩ :=
    CompletedCoefficientNormalization.completed_coefficient_tensor_normalization l E F ι
  obtain ⟨a, b, c, _, _⟩ := hp X Y h
  have hE : IsPurIntegralCoefficientComparison h l E b.alpha := by
    intro n
    simpa only [normalization_inverse, normalization_delta] using b.projection n
  have hF : IsPurIntegralCoefficientComparison h l F c.alpha := by
    intro n
    simpa only [normalization_inverse, normalization_delta] using c.projection n
  have hEi : IsIso b.alpha := normalization_alpha_isIso h l E d p a b
  have hFi : IsIso c.alpha := normalization_alpha_isIso h l F d q a c
  obtain ⟨τ, hτi, hτ⟩ := root_comparison_exists h l
  have := hEi
  have := hFi
  have := hτi
  obtain ⟨ρE, hρEi, hρE⟩ := pur_integral_tensor_transport h l E b.alpha τ hE hτ
  obtain ⟨ρF, hρFi, hρF⟩ := pur_integral_tensor_transport h l F c.alpha τ hF hτ
  refine ⟨b.alpha, c.alpha, τ, ρE, ρF, ⟨hEi, hE⟩, ⟨hFi, hF⟩, ⟨hτi, hτ⟩,
    ⟨hρEi, hρE⟩, ⟨hρFi, hρF⟩, coefficient_scalar_square h l E F ι _ _ hE hF, ?_⟩
  apply ((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply integral_tensor_hom_ext Y l E
  intro V b₀ t
  have hsY : ∀ U b t,
      (twistScalarMaps l E Y F ι 1).val.app U (purTwistIntegralTensor Y l E U b t) =
        purTwistIntegralTensor Y l F U ((twistConstantIntegerMap l E Y F ι).hom.app U b) t :=
    (twistScalarMaps_existsUnique l E Y F ι).exists.choose_spec.2.1
  have hsX : ∀ U b t,
      (twistScalarMaps l E X F ι 1).val.app U (purTwistIntegralTensor X l E U b t) =
        purTwistIntegralTensor X l F U ((twistConstantIntegerMap l E X F ι).hom.app U b) t :=
    (twistScalarMaps_existsUnique l E X F ι).exists.choose_spec.2.1
  change
    (((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρF).hom.app V
        ((twistScalarMaps l E Y F ι 1).val.app V (purTwistIntegralTensor Y l E V b₀ t)) =
      (twistScalarMaps l E X F ι 1).val.app ((proEtaleBaseChange h).op.obj V)
        ((((proEtaleSheafAdjunction h AddCommGrpCat.{u + 1}).homEquiv _ _) ρE).hom.app V
          (purTwistIntegralTensor Y l E V b₀ t))
  rw [hsY, hρF.1, hρE.1, hsX]
  congr 1
  exact congrArg (fun k ↦ k.hom.app V b₀)
    (constant_direct_comparison_naturality h (CommRingCat.ofHom
      (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
        ((integralScalarIntegerInclusion l E F ι).comp
          ULift.ringEquiv.{u, u + 1}.toRingHom))))

end AlgebraicGeometry.Scheme
