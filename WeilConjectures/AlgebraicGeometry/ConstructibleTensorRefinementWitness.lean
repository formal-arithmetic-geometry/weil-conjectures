/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Tensor witnesses on prescribed fibre-product strata

Source: Stacks Project, Tag 095I, lemma-tensor-product-constructible,
with the module comparisons of Tags 03CB and 03EL
(blueprint: lem-fd-constructible-tensor-refinement-witness).

The tensor is ordinary, with coefficients in ModuleCat. The canonical isomorphism
is the monoidal pullback comparison followed by the two adjunction-composition
comparisons. No choice of an arbitrary isomorphism enters its definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The coefficient-linear tensor comparison on the actual fibre product.
The second composition comparison uses the pullback equation, so its target uses
exactly the second projection. All functors have values in Λ-modules; scalar
identifications are the constant-coefficient inverse-image identifications.
Source: Stacks Project, Tags 095I, 03CB and 03EL
(blueprint: lem-fd-constructible-tensor-refinement-witness). -/
noncomputable def constructibleRefinementTensorIso
    {X Z W : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (i : Z ⟶ X) (j : W ⟶ X)
    (A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst i j ≫ i)).obj (A ⊗ B) ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst i j)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj A) ⊗
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i j)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj B) :=
  (Functor.Monoidal.μIso
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst i j ≫ i)) A B).symm ≪≫
    tensorIso
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.fst i j) i).app A)
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd i j) j
        (pullback.fst i j ≫ i) pullback.condition).app B)

/-- The canonical comparisons on fibre-product strata are natural in both sheaves.
Source: Stacks Project, Tags 095I, 03CB and 03EL
(blueprint: lem-fd-constructible-tensor-refinement-witness).

Proof: the inverse monoidal tensorator is natural in both factors. The two
composition comparisons are natural transformations obtained as mates of the
pullback-pasting comparison for direct images (lem-weil-pbc-inverse-image-composition).
Tensor their naturality squares and compose with the tensorator square. This gives
the displayed equality. All arrows are module morphisms, so the square is linear. -/
theorem constructibleRefinementTensorIso_naturality
    {X Z W : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (i : Z ⟶ X) (j : W ⟶ X)
    {A A' B B' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : A ⟶ A') (b : B ⟶ B') :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst i j ≫ i)).map (a ⊗ₘ b) ≫
        (constructibleRefinementTensorIso i j A' B').hom =
      (constructibleRefinementTensorIso i j A B).hom ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst i j)).map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).map a) ⊗ₘ
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i j)).map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).map b)) := by
  simp only [constructibleRefinementTensorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, tensorIso_hom, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  congr 1
  exact NatTrans.tensor_naturality
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.fst i j) i).hom
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd i j) j
      (pullback.fst i j ≫ i) pullback.condition).hom a b

/-- The prescribed fibre-product strata witness constructibility of the tensor.
Source: Stacks Project, Tag 095I, lemma-tensor-product-constructible
(blueprint: lem-fd-constructible-tensor-refinement-witness).

Proof:
1. Apply lem-weil-pbc-constructible-stratification-intersection to the given
   constructible locally closed partitions. The actual fibre products are immersed
   in X, have the intersection images, and these images partition X.
2. prop-weil-pbc-inverse-image-modules-exact identifies constant coefficient rings
   and module inverse images. The adjunction mates of
   lem-weil-pbc-inverse-image-composition give the two linear composition comparisons;
   constant scalars are unchanged, hence these comparisons are module-linear.
3. Apply lem-sfb-finite-type-constant-module-pullback to both projections.
   lem-weil-pbc-etale-base-change-continuous and
   lem-weil-pbc-etale-base-change-finite-limits supply its site hypotheses;
   lemma-constructible-pullback-constant supplies the unchanged constant models.
   Covering families at the final object and covering sieves on all objects give
   equivalent local trivializations by base change. A finitely generated module
   over finite Λ is finite, as a quotient of a finite free module.
4. lem-weil-pbc-ringed-topoi-module-pullback-tensor supplies the ordinary tensor
   comparison. Compose with the comparisons of step 2; this is precisely
   constructibleRefinementTensorIso, natural by the preceding theorem.
5. Refine the two trivializing covers by their fibre products. Base change and
   composition preserve etale covers. lem-weil-pbc-etale-inverse-image-restriction
   identifies restrictions with inverse images, linearly by naturality under
   multiplication by constant scalars. On this cover the tensor is constant with
   value M ⊗ N by lem-pc-sites-module-sheafification-tensor applied to constant
   presheaves. It is finite: pure tensors give a surjection from Λ^(M × N).
6. Transfer finite local constancy through the canonical comparison of step 4.
   The actual fibre-product partition and these restrictions satisfy clauses (a)
   and (b) of def-weil-pbc-etale-constructible-sheaf. No flatness, quasi-compactness
   or Noetherian assumption occurs. -/
theorem constructible_tensor_refinement_witness
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S T : FiniteLocallyClosedStratification X)
    (hS : ∀ k, Topology.IsConstructible (S.stratum k))
    (hT : ∀ l, Topology.IsConstructible (T.stratum l))
    (hA : ∀ k, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj A))
    (hB : ∀ l, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (T.immersion l)).obj B)) :
    (∀ (k : Fin S.n) (l : Fin T.n),
      IsImmersion (pullback.fst (S.immersion k) (T.immersion l) ≫ S.immersion k) ∧
      Set.range (pullback.fst (S.immersion k) (T.immersion l) ≫ S.immersion k) =
        S.stratum k ∩ T.stratum l ∧
      Topology.IsConstructible (S.stratum k ∩ T.stratum l)) ∧
    (⋃ (k : Fin S.n) (l : Fin T.n), S.stratum k ∩ T.stratum l) = Set.univ ∧
    Pairwise (Function.onFun Disjoint
      (fun kl : Fin S.n × Fin T.n ↦ S.stratum kl.1 ∩ T.stratum kl.2)) ∧
    (∀ (k : Fin S.n) (l : Fin T.n),
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst (S.immersion k) (T.immersion l))).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj A)) ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (S.immersion k) (T.immersion l))).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (T.immersion l)).obj B)) ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst (S.immersion k) (T.immersion l))).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj A) ⊗
        (Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (S.immersion k) (T.immersion l))).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (T.immersion l)).obj B)) ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst (S.immersion k) (T.immersion l) ≫ S.immersion k)).obj (A ⊗ B))) ∧
    IsConstructibleEtaleModuleSheaf (A ⊗ B) := by
  classical
  let S' : Stratification X :=
    { S with isConstructible_stratum := hS }
  let T' : Stratification X :=
    { T with isConstructible_stratum := hT }
  have hleft (k : Fin S.n) (l : Fin T.n) := by
    let := hA k
    exact IsFiniteLocallyConstantSheaf.upperStar
      (pullback.fst (S.immersion k) (T.immersion l))
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj A)
  have hright (k : Fin S.n) (l : Fin T.n) := by
    let := hB l
    exact IsFiniteLocallyConstantSheaf.upperStar
      (pullback.snd (S.immersion k) (T.immersion l))
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (T.immersion l)).obj B)
  have htensor (k : Fin S.n) (l : Fin T.n) := by
    exact (show IsFiniteLocallyConstantSheaf _ from
      { toIsLocallyConstantSheaf := IsLocallyConstantSheaf.tensorObj_part
          (hleft k l).toIsLocallyConstantSheaf (hright k l).toIsLocallyConstantSheaf
        toIsFiniteSheaf := IsFiniteSheaf.tensorObj_part
          (hleft k l).toIsFiniteSheaf (hright k l).toIsFiniteSheaf })
  have hpull (k : Fin S.n) (l : Fin T.n) := by
    let := htensor k l
    exact IsFiniteLocallyConstantSheaf.of_iso
      (constructibleRefinementTensorIso (S.immersion k) (T.immersion l) A B).symm
  refine ⟨?_, ?_, ?_, fun k l ↦ ⟨hleft k l, hright k l, htensor k l, hpull k l⟩, ?_⟩
  · intro k l
    let := S.isImmersion k
    let := T.isImmersion l
    refine ⟨inferInstance, ?_, (hS k).inter (hT l)⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_fst,
      Set.image_preimage_eq_inter_range, S.range_immersion, T.range_immersion,
      Set.inter_comm]
  · simp_rw [← Set.inter_iUnion, T.iUnion_stratum_eq_univ, Set.inter_univ]
    exact S.iUnion_stratum_eq_univ
  · intro kl kl' hne
    by_cases h : kl.1 = kl'.1
    · have h' : kl.2 ≠ kl'.2 := fun hh ↦ hne (Prod.ext h hh)
      exact (T.pairwise_disjoint_stratum h').mono
        Set.inter_subset_right Set.inter_subset_right
    · exact (S.pairwise_disjoint_stratum h).mono
        Set.inter_subset_left Set.inter_subset_left
  · refine ⟨S'.inter T', fun q ↦ ?_⟩
    exact (finite_locally_constant_module_values_iff _).1.mpr
      (hpull (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)

end AlgebraicGeometry.Scheme
