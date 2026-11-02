/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentScalarModelData
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Isomorphisms on a finite clopen partition for internal derived modules

Source: HRS Theorem 4.13, last paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
universe v u w
open CategoryTheory CategoryTheory.Limits
private theorem iso_of_exact_product_decomposition
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    (I : Type w) [Finite I] (H : I → C ⥤ C)
    [∀ i, (H i).Additive] [∀ i, PreservesFiniteLimits (H i)]
    [∀ i, PreservesFiniteColimits (H i)]
    (η : ∀ i, 𝟭 C ⟶ H i)
    (hη : ∀ M : C, IsLimit (Fan.mk M (fun i ↦ (η i).app M)))
    (K L : DerivedCategory C)
    (h : ∀ i, Nonempty ((H i).mapDerivedCategory.obj K ≅
      (H i).mapDerivedCategory.obj L)) : Nonempty (K ≅ L) := by
  classical
  let : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let P := Q.objPreimage K
  let R := Q.objPreimage L
  let eP : Q.obj P ≅ K := Q.objObjPreimageIso K
  let eR : Q.obj R ≅ L := Q.objObjPreimageIso L
  let ηc (S : CochainComplex C ℤ) (i : I) :
      S ⟶ ((H i).mapHomologicalComplex (.up ℤ)).obj S :=
    { f n := (η i).app (S.X n)
      comm' n m _ := ((η i).naturality (S.d n m)).symm }
  have hlim (S : CochainComplex C ℤ) : IsLimit (Fan.mk S (ηc S)) := by
    apply HomologicalComplex.isLimitOfEval
    intro n
    exact (isLimitMapConeFanMkEquiv (HomologicalComplex.eval C (.up ℤ) n) _ _).symm
      (hη (S.X n))
  have hq (S : CochainComplex C ℤ) := DerivedCategory.isLimitFanMkQObj (hlim S)
  let e (i : I) : Q.obj (((H i).mapHomologicalComplex (.up ℤ)).obj P) ≅
      Q.obj (((H i).mapHomologicalComplex (.up ℤ)).obj R) :=
    ((H i).mapDerivedCategoryFactors.app P).symm ≪≫
      (H i).mapDerivedCategory.mapIso eP ≪≫ (h i).some ≪≫
      (H i).mapDerivedCategory.mapIso eR.symm ≪≫
      (H i).mapDerivedCategoryFactors.app R
  exact ⟨eP.symm ≪≫ (hq P).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    Pi.mapIso e ≪≫ ((hq R).conePointUniqueUpToIso (limit.isLimit _)).symm ≪≫ eR⟩

namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
private theorem finite_disjoint_internal_model_gluing
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X) (hj : IsColimit (Cofan.mk X j))
    [∀ i, PreservesFiniteColimits (CondensedRing.lowerStar Λ.X (j i))]
    (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (h : ∀ i, Nonempty ((CondensedRing.upperStar Λ.X (j i)).mapDerivedCategory.obj K ≅
      (CondensedRing.upperStar Λ.X (j i)).mapDerivedCategory.obj L)) :
    Nonempty (K ≅ L) := by
  let H (i : I) := CondensedRing.upperStar Λ.X (j i) ⋙ CondensedRing.lowerStar Λ.X (j i)
  apply iso_of_exact_product_decomposition I H
    (fun i ↦ (CondensedRing.upperStarLowerStarAdjunction Λ.X (j i)).unit)
    (fun M ↦ CondensedRing.isLimitFanUnitOfIsColimitCofan Λ.X hj M) K L
  intro i
  exact ⟨(Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
    (CondensedRing.lowerStar Λ.X (j i)).mapDerivedCategory.mapIso (h i).some ≪≫
      ((Functor.mapDerivedCategoryCompIso _ _).app L).symm⟩
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
/-- Isomorphisms between the actual derived restrictions to a finite clopen partition
produce an isomorphism of internal derived module objects on the whole scheme.

Source: HRS Theorem 4.13, final gluing step
(blueprint: lem-pod-condensed-finite-clopen-internal-model-gluing).

Proof: the source library identifies an internal module with the product of the
pushforwards of its restrictions. A clopen direct image is exact: its complementary
open is also closed, hence quasi-compact, and the closed-support adjunction applies.
Apply the product decomposition degreewise to any complex. Evaluation functors
jointly reflect limits, and finite products are exact in an abelian category; thus
the decomposition remains a product after unbounded derived localization. Canonical
exact-functor composition isomorphisms identify its factors with the direct images
of the derived restrictions. Apply direct image to the supplied local isomorphisms
and use uniqueness of products to obtain a global isomorphism. Empty partitions
and empty pieces satisfy the same product argument. -/
theorem finite_clopen_internal_model_gluing
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (h : ∀ i, Nonempty ((CondensedRing.upperStar Λ.X (j i)).mapDerivedCategory.obj K ≅
      (CondensedRing.upperStar Λ.X (j i)).mapDerivedCategory.obj L)) :
    Nonempty (K ≅ L) := by
  have he (i : I) : PreservesFiniteColimits (CondensedRing.lowerStar Λ.X (j i)) := by
    let U : X.Opens := ⟨(Set.range (j i))ᶜ,
      (j i).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact (j i).isOpenEmbedding.isOpen_range.isClosed_compl)
    exact CondensedRing.closedSupport_lowerStarExact Λ.X (j i) U.ι (by
      rw [Scheme.Opens.range_ι]
      exact compl_compl (Set.range (j i)) |>.symm)
  let := he
  apply finite_disjoint_internal_model_gluing Λ j _ K L h
  exact (nonempty_isColimit_cofanMk_of j (by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hc x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩) (by
      intro i k hik
      change Disjoint (j i).opensRange (j k).opensRange
      rw [disjoint_iff_inf_le]
      intro x hx
      exact (hd hik).le_bot hx)).some
end AlgebraicGeometry.ProEtale
