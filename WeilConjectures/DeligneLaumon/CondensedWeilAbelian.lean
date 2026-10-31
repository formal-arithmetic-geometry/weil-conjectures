/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData
import WeilConjectures.AlgebraicGeometry.CoefficientHeartClosure
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-! # Abelian operations on lisse condensed Weil modules

Source: Weil II (1.1.12), using coefficient-heart closure and exact Frobenius pullback.
(blueprint: lem-dl-a1-condensed-weil-abelian).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

private lemma abelian_exact_of_closure {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    Nonempty (Abelian P.FullSubcategory) ∧
      PreservesFiniteLimits P.ι ∧ PreservesFiniteColimits P.ι := by
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact P.prop_of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (P.prop_biprod (hD ⟨.left⟩) (hD ⟨.right⟩)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  have : Abelian P.FullSubcategory := inferInstance
  have : HasBinaryBiproducts P.FullSubcategory :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : ∀ {A B : P.FullSubcategory} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) P.ι := fun {_ _} f ↦ P.preservesKernels_ι f
  have : ∀ {A B : P.FullSubcategory} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) P.ι := fun {_ _} f ↦ P.preservesCokernels_ι f
  exact ⟨⟨inferInstance⟩, Functor.preservesFiniteLimits_of_preservesKernels P.ι,
    Functor.preservesFiniteColimits_of_preservesCokernels P.ι⟩

private lemma lisse_algebras_abelian {C : Type*} [Category C] [Abelian C]
    (H : C ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderExtensions]
    [Q.IsClosedUnderKernels] [Q.IsClosedUnderCokernels]
    (F₀ : (Q.inverseImage (Endofunctor.IsoAlgebra.forget H)).FullSubcategory) :
    Nonempty (Abelian (Q.inverseImage (Endofunctor.IsoAlgebra.forget H)).FullSubcategory) ∧
      PreservesFiniteLimits
        ((Q.inverseImage (Endofunctor.IsoAlgebra.forget H)).ι ⋙ Endofunctor.IsoAlgebra.forget H) ∧
      PreservesFiniteColimits
        ((Q.inverseImage (Endofunctor.IsoAlgebra.forget H)).ι ⋙
          Endofunctor.IsoAlgebra.forget H) := by
  let F := Endofunctor.IsoAlgebra.forget H
  let P := Q.inverseImage F
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have : P.IsClosedUnderExtensions := inferInstance
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hXY⟩
    exact Q.prop_of_isLimit_kernelFork (k.mapIsLimit h F) hXY.1 hXY.2⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hXY⟩
    exact Q.prop_of_isColimit_cokernelCofork (k.mapIsColimit h F) hXY.1 hXY.2⟩
  have : P.ContainsZero :=
    ⟨⟨kernel (𝟙 F₀.obj), isZero_kernel_of_mono _,
      P.prop_kernel _ F₀.property F₀.property⟩⟩
  obtain ⟨hab, hlim, hcolim⟩ := abelian_exact_of_closure P
  have : PreservesFiniteLimits P.ι := hlim
  have : PreservesFiniteColimits P.ι := hcolim
  exact ⟨hab, comp_preservesFiniteLimits P.ι F, comp_preservesFiniteColimits P.ι F⟩


set_option maxHeartbeats 4000000 in
-- Exactness transfers through two dependent full subcategory and module interfaces.
/-- Lisse Weil modules form an abelian category and forgetting the descent structure is exact.
A supplied lisse object supplies a zero object by taking its identity kernel.

Source: Weil II (1.1.12), generic-fibre proof step 8, and coefficient-heart closure.
(blueprint: lem-dl-a1-condensed-weil-abelian).

Proof: the ambient category of Weil modules is abelian because Frobenius pullback is exact
and additive. Its forgetful functor preserves kernels, cokernels and extensions. Pull the
lisse closure properties back along this functor. Local finite freeness is invariant under
isomorphism by using the same trivializing cover. The kernel of the identity of F0 is a
lisse zero object. Extension closure gives binary biproducts. The abelian full-subcategory
criterion now applies, and kernel and cokernel preservation give exactness of the inclusion.
Compose that inclusion with the exact ambient forgetful functor. -/
theorem lisse_weil_abelian (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (g : X ≅ X) (F₀ : Lisse ell g) :
    Nonempty (Abelian (Lisse ell g)) ∧
      PreservesFiniteLimits (forget ell g) ∧ PreservesFiniteColimits (forget ell g) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ell
  let Q : ObjectProperty (RealCondensedFibre.Modules Λ X) := IsLisseCoefficientModule Λ
  obtain ⟨he, hk, hc⟩ :=
    (coefficientHeart_closure ell (Profinite.padicAlgClCondensedRing ell) (Or.inr rfl)).1 X
  have : Q.IsClosedUnderExtensions := he
  have : Q.IsClosedUnderKernels := hk
  have : Q.IsClosedUnderCokernels := hc
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro M N e hM
    obtain ⟨U, hU⟩ := hM
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨n, ⟨en⟩⟩ := hU i
    exact ⟨n, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ en⟩⟩⟩
  exact lisse_algebras_abelian (CondensedRing.upperStar Λ g.hom) Q F₀

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
