module

public import Sheaf.Paper.EvenLineProductIntegrationMaps

import Sheaf.Paper.EvenLineBinaryProductNormalization
import Sheaf.Paper.EvenLineCoordinateIntertwining
import Sheaf.Paper.EvenTateLineSelfSymmetry
import Sheaf.Paper.EvenLineCoefficientProjectionNaturality

/-! # Symmetry of even Tate-line product integration

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: lem-pur-even-line-product-integration-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

section TensorProofs
variable {B : Type*} [Category B] [MonoidalCategory B]

private theorem tensorStep {N M M' U : B} (b : N ≅ M ⊗ U) (k : M ≅ M')
    (f : M' ⟶ 𝟙_ B) (t : U ⟶ 𝟙_ B) :
    b.hom ≫ tensorHom (k.hom ≫ f) t ≫ (λ_ (𝟙_ B)).hom =
      (b ≪≫ whiskerRightIso k U).hom ≫
        (tensorHom f t ≫ (λ_ (𝟙_ B)).hom) := by
  simp only [Iso.trans_hom, whiskerRightIso_hom, Category.assoc, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.id_comp]

private theorem tensorJoin {L R VL VR PL PR V PT : B}
    (nl : L ≅ PL) (nr : R ≅ PR) (kl : VL ≅ PL) (kr : VR ≅ PR)
    (kt : V ≅ PT) (a : PL ⊗ PR ≅ PT) (fl : L ⟶ VL) (fr : R ⟶ VR)
    (f : VL ⊗ VR ⟶ V) (hl : fl = nl.hom ≫ kl.inv) (hr : fr = nr.hom ≫ kr.inv)
    (hf : tensorHom kl.inv kr.inv ≫ f = a.hom ≫ kt.inv) :
    tensorHom fl fr ≫ f =
      ((whiskerRightIso nl R ≪≫ whiskerLeftIso PL nr) ≪≫ a).hom ≫ kt.inv := by
  rw [hl, hr, ← tensorHom_comp_tensorHom, Category.assoc, hf]
  simp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    MonoidalCategory.tensorHom_def, Category.assoc]

private theorem projectionAction_eq_id {K U V : B} (p : K ⊗ U ⟶ V) [IsIso p]
    (a : U ⟶ U) (b : V ⟶ V) (ha : a = 𝟙 _)
    (h : p ≫ b = tensorHom (𝟙 K) a ≫ p) : b = 𝟙 _ := by
  apply (cancel_epi p).mp
  simpa only [ha, id_tensorHom_id, Category.id_comp, Category.comp_id] using h

private theorem lastAdjacent_eq_id (swap : (M N : B) → M ⊗ N ≅ N ⊗ M)
    (M : B) (h : (swap M M).hom = 𝟙 _) (r : ℕ) :
    (lastAdjacent swap M r).hom = 𝟙 _ := by
  cases r <;> simp [lastAdjacent, h, positiveTensorPower]

private theorem lastSwap_eq_id (swap : (M N : B) → M ⊗ N ≅ N ⊗ M)
    (M : B) (h : (swap M M).hom = 𝟙 _) (r : ℕ) (i : Fin (r + 1)) :
    (lastSwap swap M r i).hom = 𝟙 _ := by
  cases r with
  | zero => rfl
  | succ r =>
    simp only [lastSwap]
    split
    · rfl
    · simp [lastAdjacent_eq_id swap M h, positiveTensorPower]

private theorem permutation_eq_id (swap : (M N : B) → M ⊗ N ≅ N ⊗ M)
    (M : B) (h : (swap M M).hom = 𝟙 _) (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) : (permutation swap M r σ).hom = 𝟙 _ := by
  induction r with
  | zero => rfl
  | succ r ih => simp [permutation, lastSwap_eq_id swap M h, ih, positiveTensorPower]

private theorem selfBraiding_eq_id [BraidedCategory B] {M : B} (e : M ≅ 𝟙_ B) :
    (β_ M M).hom = 𝟙 _ := by
  apply (cancel_mono (tensorHom e.hom e.hom)).mp
  rw [Category.id_comp, ← BraidedCategory.braiding_naturality]
  have h : (β_ (𝟙_ B) (𝟙_ B)).hom = 𝟙 _ := by
    apply (cancel_mono (λ_ (𝟙_ B)).hom).mp
    simpa only [Category.id_comp, unitors_equal] using braiding_leftUnitor (𝟙_ B)
  rw [h, Category.comp_id]

end TensorProofs

private theorem canonicalSelf_eq_id
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M : _root_.DerivedCategory C) (e : M ≅ 𝟙_ (_root_.DerivedCategory C)) :
    (((_root_.DerivedCategory.canonicalTensorSymmetry C).app M).app M).hom = 𝟙 _ := by
  let := _root_.DerivedCategory.braidedCategory' C
  exact selfBraiding_eq_id e

private theorem signedSelf_eq_id (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (hU : Nonempty (integral P Y 0 ≅ 𝟙_ (D P Y))) :
    (signedSymmetry P Y (integral P Y 0) (integral P Y 0)).hom = 𝟙 _ := by
  unfold signedSymmetry VectorIntegrationSite.symmetry
  exact canonicalSelf_eq_id
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (Ring P))) _ hU.some

private theorem tensorPowerRecursion
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (hprod : ∀ r : ℕ, IsIso (forward P Y aY r 0))
    (J : (r : ℕ) → integral P Y r ⟶ 𝟙_ (D P Y))
    (hJ₁ : J 0 = trace P Y aY)
    (hJsucc : ∀ r : ℕ, J (r + 1) =
      (binaryInverse P Y aY r 0 (hprod r)).hom ≫
        tensorHom (J r) (trace P Y aY) ≫ (λ_ (𝟙_ (D P Y))).hom) :
    ∀ r : ℕ, J r = (kappa P Y aY hprod r).hom ≫ powerTrace (trace P Y aY) r := by
  intro r
  induction r with
  | zero => simpa [kappa, powerTrace] using hJ₁
  | succ r ih =>
    rw [hJsucc, ih]
    exact tensorStep (binaryInverse P Y aY r 0 (hprod r)) (kappa P Y aY hprod r)
      (powerTrace (trace P Y aY) r) (trace P Y aY)

private theorem treeNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (hU : Nonempty (integral P Y 0 ≅ 𝟙_ (D P Y)))
    (hV : ∀ r : ℕ, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y (integral P Y r))
    (hprod : ∀ r : ℕ, IsIso (forward P Y aY r 0)) (t : ProductTree) :
    treeForward P Y aY t =
      (t.normalize (integral P Y 0)).hom ≫ (kappa P Y aY hprod t.index).inv := by
  induction t with
  | leaf =>
    change 𝟙 (integral P Y 0) = 𝟙 _ ≫ 𝟙 _
    exact (Category.id_comp _).symm
  | join l r hl hr =>
    exact tensorJoin (l.normalize (integral P Y 0)) (r.normalize (integral P Y 0))
      (kappa P Y aY hprod l.index) (kappa P Y aY hprod r.index)
      (kappa P Y aY hprod (l.index + r.index + 1))
      (appendPower (integral P Y 0) l.index r.index) _ _
      (forward P Y aY l.index r.index) hl hr
      (binaryProductNormalization P Y aY hU hV hprod l.index r.index)

/-- Tensor-power integration and all concrete product symmetries of the even Tate line.
Source: current blueprint, affine-space composition proof Steps 3--4, with the
finite ordinary proper/open expansion recorded by the node
(blueprint: lem-pur-even-line-product-integration-symmetry).

Proof: the finite Kummer line is locally constant flat of rank one, and the shifted
line has its flat representative in degree -2. Pullback/tensor comparison and twist
additivity identify its external powers with tate. Every intermediate object has
bounded etale origin: the inputs are ctf, the Tate factors are shifted flat lines,
and U is a unit. Thus all the concrete finite product words are in their stated
domains. Rewrite the two triple products in the common product compactification.
Their proper pieces have the same transpose, the tensor of the three ordinary
counits. Their open normalizations are equal by full faithfulness of extension by
zero: both restrict to the identity. Consequently the actual forward words are
associative. Rotations of a binary tree reduce it to the left-associated tree,
so every treeForward is the inverse kappa after normalize and is invertible.

The concrete binary forward symmetry identifies a geometric block swap with the
signed external tensor swap. Its scalar on shifts -2d and -2e is
(-1)^((-2d)(-2e))=1; the ordinary degree-zero Tate line has its canonical symmetric
multiplication. Hence this signed swap agrees with coordinateTate. Adjacent swaps
and the associator/hexagon/involution identities give the equality for every sigma.
This also proves that coordinateAction is invertible. Substitution in the given
recursion proves J=kappa followed by the tensor power of trace, by induction.
Naturality of signed symmetry for trace tensor trace, and symmetry of multiplication
on the flat degree-zero unit, imply that every tensor permutation fixes that tensor
power. Composing the kappa permutation equation proves coordinateAction followed by
J equals J; trace itself need not be the assumed object isomorphism U to the unit.

Finally apply the actual projection/exchange compatibility to the coordinate
Cartesian square over the identity. The product of projective lines compactification
carries that coordinate isomorphism, and the canonical compactification comparisons
intertwine projection. Conjugating the forward equation by its projection inverse
gives coefficientAction followed by Pi equal to Pi followed by 1_K tensor the action.
K stays first and is never crossed. Apply the already established invariance of J
and the right unitor to obtain the last equality. This uses only finite projection
and exchange, ordinary compactification comparisons, and signed tensor coherence;
no exceptional purity, duality axiom, or coordinate invariance is assumed. -/
theorem evenLineProductIntegrationSymmetry
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hU : Nonempty (integral P Y 0 ≅ 𝟙_ (D P Y)))
    (hV : ∀ r : ℕ, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y (integral P Y r))
    (hprod : ∀ r : ℕ, IsIso (forward P Y aY r 0))
    (J : (r : ℕ) → integral P Y r ⟶ 𝟙_ (D P Y))
    (hJ₁ : J 0 = trace P Y aY)
    (hJsucc : ∀ r : ℕ, J (r + 1) =
      (binaryInverse P Y aY r 0 (hprod r)).hom ≫
        tensorHom (J r) (trace P Y aY) ≫ (λ_ (𝟙_ (D P Y))).hom) :
    (∀ r : ℕ, J r = (kappa P Y aY hprod r).hom ≫ powerTrace (trace P Y aY) r) ∧
    (∀ t : ProductTree, IsIso (treeForward P Y aY t) ∧
      treeForward P Y aY t =
        (t.normalize (integral P Y 0)).hom ≫ (kappa P Y aY hprod t.index).inv) ∧
    (∀ (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))),
      IsIso (coordinateAction P Y aY r σ) ∧
      coordinateAction P Y aY r σ ≫ (kappa P Y aY hprod r).hom =
        (kappa P Y aY hprod r).hom ≫ (permutation (signedSymmetry P Y) (integral P Y 0) r σ).hom ∧
      coordinateAction P Y aY r σ ≫ J r = J r) ∧
    (∀ (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))),
      (coordinateTate P Y r σ).hom ≫
          (inverseImage (Ring P) (proj Y r)).map 
            (permutation (signedSymmetry P Y) (shiftedLine P Y) r σ).hom =
        (coordinateTate P Y r σ).hom) ∧
    (∀ d e : ℕ, (-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1) ∧
    (∀ (r : ℕ) (K : D P Y)
      (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K)
      (σ : Equiv.Perm (Fin (r + 1))),
      coefficientAction P Y aY r σ K hK ≫ coefficientTrace P Y aY r K hK (J r) =
        coefficientTrace P Y aY r K hK (J r)) := by
  have hrec := tensorPowerRecursion P Y aY hprod J hJ₁ hJsucc
  have hperm := permutation_eq_id (signedSymmetry P Y) (integral P Y 0)
    (signedSelf_eq_id P Y hU)
  have haction : ∀ r σ, coordinateAction P Y aY r σ = 𝟙 _ := by
    intro r σ
    apply (cancel_mono (kappa P Y aY hprod r).hom).mp
    simpa only [hperm, Category.comp_id, Category.id_comp] using
      coordinateIntertwining P Y aY hU hV hprod r σ
  refine ⟨hrec, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have ht := treeNormalization P Y aY hU hV hprod t
    rw [ht]
    exact ⟨inferInstance, rfl⟩
  · intro r σ
    rw [haction r σ, hperm r σ]
    exact ⟨inferInstance, by simp, by simp⟩
  · intro r σ
    rw [permutation_eq_id (signedSymmetry P Y) (shiftedLine P Y)
      (evenTateLineSelfSymmetry P Y aY) r σ]
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  · intro d e
    rw [Nat.mul_assoc, pow_mul]
    norm_num
  · intro r K hK σ
    have := projection_isIso P Y aY r K hK
    have hid : coefficientAction P Y aY r σ K hK = 𝟙 _ :=
      projectionAction_eq_id (B := D P Y) (K := K) (U := integral P Y r)
        (V := (support P Y r).obj
          ((inverseImage (Ring P) (proj Y r)).obj K ⊗ tate P Y r))
      (VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
        (compactification Y r) (tate P Y r) K)
      (coordinateAction P Y aY r σ) (coefficientAction P Y aY r σ K hK)
      (haction r σ) (coefficientProjectionNaturality P Y aY r K hK σ)
    rw [hid, Category.id_comp]

end AlgebraicGeometry.ProEtale.EvenLineProduct


