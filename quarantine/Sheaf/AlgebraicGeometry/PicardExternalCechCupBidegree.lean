/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProduct
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Bilinear external Alexander--Whitney summands
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-bidegree).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Coordinates for one external Alexander--Whitney tensor summand.
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-bidegree). -/
def IsPicardExternalCechCupBidegree
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ) (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) : Prop :=
  ∀ (a : ((picardCechFunctor f U).obj F).X p)
        (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
        TopCat.Presheaf.cechComplexFunctorXAddEquiv
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)
          (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q) (h (a ⊗ₜ[k] b)) y =
          tmulSection
            (((fun (Q : X.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.fst f g ⁻¹ᵁ Q) (s : Γ(F, Q)) ↦
              ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.fst f g))).unit.app F).val.app (op Q) s))
              (⨅ l, U (y (cupFront p q l)).1) _
              (by
                intro x hx
                change (pullback.fst f g).base x ∈ ⨅ l, U (y (cupFront p q l)).1
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupFront p q l) hx).1)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a
                (fun l ↦ (y (cupFront p q l)).1))))
            (((fun (Q : Y.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.snd f g ⁻¹ᵁ Q) (s : Γ(G, Q)) ↦
              ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.snd f g))).unit.app G).val.app (op Q) s))
              (⨅ l, V (y (cupBack p q l)).2) _
              (by
                intro x hx
                change (pullback.snd f g).base x ∈ ⨅ l, V (y (cupBack p q l)).2
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupBack p q l) hx).2)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b
                (fun l ↦ (y (cupBack p q l)).2))))

private def scalarCechCoordinate
    {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ) (z : Fin (n + 1) → μ) :
    ((picardCechFunctor t A).obj M).X n ⟶ scalarObj t M (op (⨅ i, A (z i))) :=
  TopCat.Presheaf.cechComplexFunctorπ A (scalarPresheaf t M) n z ≫
    (scalarPresheaf t M).map (homOfLE (TopCat.Presheaf.iInf_le_piObj A z)).op

private def scalarUnitSection
    {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (s : T ⟶ Spec (CommRingCat.of k)) (a : T ⟶ Z) (ha : a ≫ t = s)
    (M : Z.Modules) (Q : Z.Opens) :
    scalarObj t M (op Q) ⟶ scalarObj s ((tensorPullback a).obj M) (op (a ⁻¹ᵁ Q)) :=
  ((((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    _ _).homEquiv _ _) (Classical.choose
      (exists_scalarPullbackCoefficient t s a ha M))).hom.app (op Q)

private lemma scalarUnitSection_apply
    {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (s : T ⟶ Spec (CommRingCat.of k)) (a : T ⟶ Z) (ha : a ≫ t = s)
    (M : Z.Modules) (Q : Z.Opens) (z : scalarObj t M (op Q)) :
    scalarUnitSection t s a ha M Q z =
      ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app
        (op Q) z :=
  Classical.choose_spec (exists_scalarPullbackCoefficient t s a ha M) Q z

private def scalarPulledSection
    {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (s : T ⟶ Spec (CommRingCat.of k)) (a : T ⟶ Z) (ha : a ≫ t = s)
    (M : Z.Modules) (Q : Z.Opens) (W : T.Opens) (hW : W ≤ a ⁻¹ᵁ Q) :
    scalarObj t M (op Q) ⟶ scalarObj s ((tensorPullback a).obj M) (op W) :=
  scalarUnitSection t s a ha M Q ≫
    (scalarPresheaf s ((tensorPullback a).obj M)).map (homOfLE hW).op

private lemma scalarPulledSection_apply
    {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (s : T ⟶ Spec (CommRingCat.of k)) (a : T ⟶ Z) (ha : a ≫ t = s)
    (M : Z.Modules) (Q : Z.Opens) (W : T.Opens) (hW : W ≤ a ⁻¹ᵁ Q)
    (z : scalarObj t M (op Q)) :
    scalarPulledSection t s a ha M Q W hW z =
      ((tensorPullback a).obj M).presheaf.map (homOfLE hW).op
        (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app
          (op Q) z) := by
  change (scalarPresheaf s ((tensorPullback a).obj M)).map (homOfLE hW).op
    (scalarUnitSection t s a ha M Q z) = _
  rw [scalarUnitSection_apply]
  rfl

private def scalarCechAssemble
    {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ) (B : ModuleCat.{w} k)
    (h : ∀ z : Fin (n + 1) → μ, B ⟶ scalarObj t M (op (⨅ i, A (z i)))) :
    B ⟶ ((picardCechFunctor t A).obj M).X n :=
  Pi.lift (fun z ↦ h z ≫ (scalarPresheaf t M).map
    (homOfLE (TopCat.Presheaf.piObj_le_iInf A z)).op)

private lemma scalarCechAssemble_apply
    {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ) (B : ModuleCat.{w} k)
    (h : ∀ z : Fin (n + 1) → μ, B ⟶ scalarObj t M (op (⨅ i, A (z i))))
    (b : B) (z : Fin (n + 1) → μ) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n
      (scalarCechAssemble t A M n B h b) z = h z b := by
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  have hp := ConcreteCategory.congr_hom (Pi.lift_π
    (fun z ↦ h z ≫ (scalarPresheaf t M).map
      (homOfLE (TopCat.Presheaf.piObj_le_iInf A z)).op) z) b
  simp only [ConcreteCategory.comp_apply] at hp
  change (scalarPresheaf t M).map _
    ((Pi.π (fun z : Fin (n + 1) → μ ↦
      (scalarPresheaf t M).obj (op (∏ᶜ fun i ↦ A (z i)))) z) (scalarCechAssemble t A M n B h b)) = _
  refine (congrArg (fun v ↦ (scalarPresheaf t M).map
    (homOfLE (TopCat.Presheaf.iInf_le_piObj A z)).op v) hp).trans ?_
  exact (TopCat.Presheaf.map_map_apply (scalarPresheaf t M) _ _ (𝟙 _) _).trans
    (TopCat.Presheaf.map_apply_self (scalarPresheaf t M) (𝟙 _) _)

/-- The front/back section formula factors through the tensor product in one bidegree.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech, and Tag 07MB.
(blueprint: lem-sc-picard-external-cech-cup-bidegree).
Proof: For each product tuple, pull the front section of F and the back section of G
along the canonical pullback adjunction units, and restrict both to the full
product intersection. These operations are additive. A scalar from k acts through
the two structure maps to Spec k; the pullback square equates these actions on the
product. Thus each resulting tensor section is k-bilinear. Taking the product over
all tuples preserves bilinearity. The Cech coordinate equivalence transports this
pairing to the target degree, and the tensor universal property gives h with the
stated pure-tensor coordinates. No differential identity is asserted here.
For empty index families the coordinate product is zero; zero coefficients give
zero pairings, and p = q = 0 uses the single common vertex without a sign. -/
theorem picardExternalCechCupBidegree_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules) (p q : ℕ) :
    ∃ h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q),
      IsPicardExternalCechCupBidegree f g U V F G p q h := by
  let W : ι × κ → (Limits.pullback f g).Opens :=
    fun ij ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
  let t := pullback.fst f g ≫ f
  let M := (tensorPullback (pullback.fst f g)).obj F
  let N := (tensorPullback (pullback.snd f g)).obj G
  let hfront (y : Fin (p + q + 1) → ι × κ) :
      (⨅ j, W (y j)) ≤ pullback.fst f g ⁻¹ᵁ (⨅ l, U (y (cupFront p q l)).1) := by
    intro x hx
    change (pullback.fst f g).base x ∈ ⨅ l, U (y (cupFront p q l)).1
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro l
    exact (iInf_le (fun j ↦ W (y j)) (cupFront p q l) hx).1
  let hback (y : Fin (p + q + 1) → ι × κ) :
      (⨅ j, W (y j)) ≤ pullback.snd f g ⁻¹ᵁ (⨅ l, V (y (cupBack p q l)).2) := by
    intro x hx
    change (pullback.snd f g).base x ∈ ⨅ l, V (y (cupBack p q l)).2
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro l
    exact (iInf_le (fun j ↦ W (y j)) (cupBack p q l) hx).2
  let front (y : Fin (p + q + 1) → ι × κ) :=
    scalarCechCoordinate f U F p (fun l ↦ (y (cupFront p q l)).1) ≫
      scalarPulledSection f t (pullback.fst f g) rfl F _ _ (hfront y)
  let back (y : Fin (p + q + 1) → ι × κ) :=
    scalarCechCoordinate g V G q (fun l ↦ (y (cupBack p q l)).2) ≫
      scalarPulledSection g t (pullback.snd f g) (pullback.condition (f := f) (g := g)).symm G _ _
        (hback y)
  let pair (y : Fin (p + q + 1) → ι × κ) :=
    (front y ⊗ₘ back y) ≫ scalarTensorCoefficientApp t M N (op (⨅ j, W (y j)))
  refine ⟨scalarCechAssemble t W (M ⊗ N) (p + q) _ pair, ?_⟩
  intro a b y
  rw [scalarCechAssemble_apply]
  change scalarTensorCoefficientApp t M N _ ((front y ⊗ₘ back y) (a ⊗ₜ[k] b)) = _
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  change tmulSection (front y a) (back y b) = _
  dsimp only [front, back]
  simp only [ConcreteCategory.comp_apply]
  rw [scalarPulledSection_apply, scalarPulledSection_apply]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
