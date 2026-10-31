/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Bimod

/-! # Finite-free coordinates for relative tensor products

Source: Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence
(blueprint: lem-sfb-relative-tensor-finite-free-coordinates).

The auxiliary instances select the recorded canonical sheaf tensor, derive its required
interfaces from the recorded sheaf-tensor theorem, and select finite biproducts from
existing finite products. No tensor, action, or coequalizer is redefined.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

/-- Left exact sheafification on the essentially small site, transported from its small model.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, with sheafification
as in `sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} := by
  let : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- The canonical sheafified tensor over the integers, selected from the recorded structure.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, using
`sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafMonoidal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).monoidal

/-- The symmetry of the same canonical sheaf tensor.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, using
`sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafSymmetric
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : SymmetricCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).symmetric

/-- Closedness of the canonical sheaf tensor, supplied by its recorded properties theorem.
The choice here is only a right adjoint to a fixed functor, uniquely determined up to
natural isomorphism; it does not choose the tensor or the relative tensor. It is not an
instance: it is used only to derive the Prop-valued additivity below, so importers do not
receive a chosen internal Hom.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, using
`sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
@[instance_reducible]
noncomputable def sfbCoordinateSheafClosed
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalClosed (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0}
    (A := AddCommGrpCat.{w}) J).2.1.some

/-- Additivity of the canonical sheaf tensor from its closed symmetric structure.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence; proof step 1 of
(blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafPreadditive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalPreadditive (Sheaf J AddCommGrpCat.{w}) :=
  letI := sfbCoordinateSheafClosed J
  sfbSheafTensor_monoidalPreadditive

/-- Left tensor preserves the coequalizers used for the relative tensor.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, and the properties of
`sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafLeftColimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
  ((sfbSheafTensor_properties (A := AddCommGrpCat.{w}) J).2.2 F).1

/-- Right tensor preserves the coequalizers used for the relative tensor.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence, and the properties of
`sk-def-sfb-sheaf-tensor` (blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateSheafRightColimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
  ((sfbSheafTensor_properties (A := AddCommGrpCat.{w}) J).2.2 F).2.1

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J AddCommGrpCat.{w}) [MonObj R] [IsCommMonObj R]

/-- The finite biproducts of internal modules, obtained from their existing finite products.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, last sentence; proof step 2 of
(blueprint: lem-sfb-relative-tensor-finite-free-coordinates). -/
noncomputable instance sfbCoordinateModuleBiproducts :
    HasFiniteBiproducts (Mod (Sheaf J AddCommGrpCat.{w}) R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private lemma coordinate_tensorUnit_hom
    {H : Type*} [Category H] [MonoidalCategory H] [BraidedCategory H]
    [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {S : H} [MonObj S] [IsCommMonObj S]
    (M : Mod H S) :
    Mod.tensorObjπ (Mod.regular S) M ≫ (λ_ M).hom.hom = γ[S,M.X] := by
  change Mod.tensorObjπ (Mod.regular S) M ≫
    (Bimod.whiskerRight (Mod.toBimodRegularIso (R := S)).hom
      ((Mod.toBimod S).obj M)).hom ≫
      Bimod.LeftUnitorBimod.hom ((Mod.toBimod S).obj M) = _
  dsimp only [Mod.tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

private lemma coordinate_tensorUnit_inv
    {H : Type*} [Category H] [MonoidalCategory H] [BraidedCategory H]
    [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {S : H} [MonObj S] [IsCommMonObj S]
    (M : Mod H S) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[S] ▷ M.X ≫
      Mod.tensorObjπ (Mod.regular S) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [Category.assoc, Category.assoc, coordinate_tensorUnit_hom,
    ModObj.one_smul_self, Iso.inv_hom_id]
  exact congrArg Mod.Hom.hom (λ_ M).inv_hom_id

private noncomputable def coordinateIso
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    {P : A} {n : ℕ} (θ : (⨁ fun _ : Fin n ↦ 𝟙_ A) ≅ P)
    (M : A) : P ⊗ M ≅ ∏ᶜ (fun _ : Fin n ↦ M) :=
  whiskerRightIso θ.symm M ≪≫ rightDistributor (fun _ : Fin n ↦ 𝟙_ A) M ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ λ_ M) ≪≫ biproduct.isoProduct _

private lemma coordinateIso_π
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    {P : A} {n : ℕ} (θ : (⨁ fun _ : Fin n ↦ 𝟙_ A) ≅ P)
    (M : A) (i : Fin n) :
    (coordinateIso θ M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i =
      ((θ.inv ≫ biproduct.π (fun _ : Fin n ↦ 𝟙_ A) i) ▷ M) ≫ (λ_ M).hom := by
  simp [coordinateIso, biproduct.isoProduct_hom, comp_whiskerRight, Category.assoc]

private lemma coordinateIso_inv
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    {P : A} {n : ℕ} (θ : (⨁ fun _ : Fin n ↦ 𝟙_ A) ≅ P)
    (M : A) :
    (coordinateIso θ M).inv = ∑ i : Fin n, Pi.π (fun _ : Fin n ↦ M) i ≫
      (λ_ M).inv ≫ ((biproduct.ι (fun _ : Fin n ↦ 𝟙_ A) i ≫ θ.hom) ▷ M) := by
  classical
  simp [coordinateIso, rightDistributor_inv, Preadditive.comp_sum,
    Preadditive.sum_comp, biproduct.isoProduct_inv, comp_whiskerRight, Category.assoc]

private lemma coordinateIso_naturality
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    {P : A} {n : ℕ} (θ : (⨁ fun _ : Fin n ↦ 𝟙_ A) ≅ P)
    {M M' : A} (f : M ⟶ M') :
    (P ◁ f) ≫ (coordinateIso θ M').hom =
      (coordinateIso θ M).hom ≫ Limits.Pi.map (fun _ : Fin n ↦ f) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, coordinateIso_π, Pi.map_π]
  rw [← Category.assoc (coordinateIso θ M).hom (Pi.π _ i) f, coordinateIso_π]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality]
  rw [← whisker_exchange_assoc]

/-- Finite-free tensor coordinates, with both relative-unitor normalizations, both
module-valued coordinate equations, both underlying-sheaf equations and naturality.

Source: blueprint `sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/`
`lem-sfb-subfield-flat.proof.md`, last sentence
(blueprint: lem-sfb-relative-tensor-finite-free-coordinates).

Proof, following the node:
1. Sheafification is additive by uniqueness of extension from its unit; objectwise
integer tensor is additive in each variable. Module morphisms are closed under sums
and zero, so modules form a preadditive category and the forgetful functor is additive.
These structures are already provided by the imported APIs.
2. Form finite products with coordinatewise action. The inclusions given by identity
in one coordinate and zero in the others are linear. Projection checks show the
biproduct identities, including the empty case. Conjugating them by the chosen basis
θ gives q_i e_j = δ_ij and the sum of e_i q_i equal to the identity.
3. The relative tensor map descends the ambient tensor of maps by the coequalizer
universal property (`def-sfb-modobj-relative-tensor`). Its projection is epi; cancellation
therefore proves additivity of relative tensor maps and preservation of finite sums.
4. The relative left unitor descends the action, since the bimodule left unitor does
(`lem-sfb-bimod-monoidal`). Inserting the ring unit followed by the coequalizer projection
is a right inverse by the module unit axiom (`sk-def-sfb-module-objects`); invertibility
of the unitor identifies this with its inverse. These are the first two identities.
5. Let A_i = L_M (q_i tensor 1), B_i = (e_i tensor 1) L_M inverse. Pair the A_i to
get D_M and set S_M to the sum of B_i rho_i. Additivity and the basis equations give
A_i B_j = δ_ij, S_M D_M = 1, and D_M S_M = 1 by projections. This proves the
isomorphism and both module coordinate equations.
6. Precompose the projection equations with the canonical coequalizer projection.
Functoriality from step 3 and the first normalization from step 4 yield the underlying
forward equation. Apply the additive forgetful functor to S_M, substitute the second
normalization and use tensor functoriality to obtain exactly the inverse sum formula.
7. Naturality of L and tensor bifunctoriality give the naturality equation after every
product projection, hence the equation itself. The components are isomorphisms by
step 5. For n = 0, the basis identity is 1_N = 0; tensor additivity implies
1_(N tensor M) = 0, and all inverse computations remain valid with empty sums.
-/
theorem sfb_relative_tensor_finite_free_coordinates
    (N : Mod (Sheaf J AddCommGrpCat.{w}) R) (n : ℕ)
    (θ : (⨁ fun _ : Fin n ↦ Mod.regular R) ≅ N) :
    (∀ M : Mod (Sheaf J AddCommGrpCat.{w}) R,
      Mod.tensorObjπ (Mod.regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X] ∧
      (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[R] ▷ M.X ≫
        Mod.tensorObjπ (Mod.regular R) M) ∧
    ∃ D : tensorLeft N ≅
        Functor.pi' (fun _ : Fin n ↦ 𝟭 (Mod (Sheaf J AddCommGrpCat.{w}) R)) ⋙
          Limits.Pi.functor (Fin n),
      (∀ (M : Mod (Sheaf J AddCommGrpCat.{w}) R) (i : Fin n),
        (D.app M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i =
          ((θ.inv ≫ biproduct.π (fun _ : Fin n ↦ Mod.regular R) i) ▷ M) ≫
            (λ_ M).hom) ∧
      (∀ M : Mod (Sheaf J AddCommGrpCat.{w}) R,
        (D.app M).inv = ∑ i : Fin n, Pi.π (fun _ : Fin n ↦ M) i ≫
          (λ_ M).inv ≫ ((biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i ≫ θ.hom) ▷ M)) ∧
      (∀ (M : Mod (Sheaf J AddCommGrpCat.{w}) R) (i : Fin n),
        Mod.tensorObjπ N M ≫ ((D.app M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i).hom =
          (θ.inv ≫ biproduct.π (fun _ : Fin n ↦ Mod.regular R) i).hom ▷ M.X ≫ γ[R,M.X]) ∧
      (∀ M : Mod (Sheaf J AddCommGrpCat.{w}) R,
        (D.app M).inv.hom = ∑ i : Fin n,
          (Pi.π (fun _ : Fin n ↦ M) i).hom ≫ (λ_ M.X).inv ≫
            (η[R] ≫ (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i ≫ θ.hom).hom) ▷ M.X ≫
              Mod.tensorObjπ N M) ∧
      (∀ (M M' : Mod (Sheaf J AddCommGrpCat.{w}) R) (f : M ⟶ M'),
        (N ◁ f) ≫ (D.app M').hom = (D.app M).hom ≫ Limits.Pi.map (fun _ : Fin n ↦ f)) := by
  classical
  let D : tensorLeft N ≅
      Functor.pi' (fun _ : Fin n ↦ 𝟭 (Mod (Sheaf J AddCommGrpCat.{w}) R)) ⋙
        Limits.Pi.functor (Fin n) :=
    NatIso.ofComponents (coordinateIso θ) (fun f ↦ coordinateIso_naturality θ f)
  refine ⟨fun M ↦ ⟨coordinate_tensorUnit_hom M, coordinate_tensorUnit_inv M⟩,
    D, ?_, ?_, ?_, ?_, ?_⟩
  · exact coordinateIso_π θ
  · exact coordinateIso_inv θ
  · intro M i
    change Mod.tensorObjπ N M ≫
      ((coordinateIso θ M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i).hom = _
    rw [coordinateIso_π]
    simp only [Mod.comp_hom']
    rw [Mod.tensorObjπ_whiskerRight_assoc]
    erw [coordinate_tensorUnit_hom]
    rfl
  · intro M
    change (coordinateIso θ M).inv.hom = _
    rw [coordinateIso_inv]
    change (Mod.forget R).map (∑ i : Fin n, _) = _
    rw [Functor.map_sum]
    simp only [Mod.forget_map, Mod.comp_hom']
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinate_tensorUnit_inv]
    simp only [Category.assoc]
    erw [Mod.tensorObjπ_whiskerRight]
    simp only [Mod.comp_hom', comp_whiskerRight, Category.assoc]
    rfl
  · intro M M' f
    exact coordinateIso_naturality θ f

end CategoryTheory
