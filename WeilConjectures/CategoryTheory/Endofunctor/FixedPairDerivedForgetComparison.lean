/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.KInjectiveExactSquare.KInjectiveExactSquareComparison
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Derived forgetting of fixed pairs

Source: `WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean`, Free and
isGrothendieckAbelian; `DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean`,
Free.preservesHomology_functor and rightDerivedFunctorMapOfNatIsoCompForgetIso;
`DerivedCategory/RightDerivedFunctor/IsoAlgebraComp.lean`, derived conservativity
(blueprint: lem-sf-fixed-pair-derived-forget-comparison).

The fixed-pair category is the existing full subcategory `Endofunctor.IsoAlgebra`.
Right derivation uses the recorded arbitrary-quasi-isomorphism interface. The comparison
is characterized by its derived units; evaluating its equation on the homotopy class
of a degree-zero complex gives the requested comparison of maps from single objects.
-/

@[expose] public section

set_option autoImplicit false

universe uC uD vC vD wC wD wF wH

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- Structural clauses for forgetting fixed pairs. Source: Endofunctor/IsoAlgebra.lean,
Free.adjunction and isGrothendieckAbelian; RightDerivedFunctor/IsoAlgebra.lean,
Free.preservesHomology_functor and preservesKInjectiveComplexes_forget; IsoAlgebraComp.lean,
isIso_of_isIso_forget_mapDerivedCategory_map
(blueprint: lem-sf-fixed-pair-derived-forget-comparison).

Proof plan (steps 1--8 of the node): create limits and colimits on underlying objects,
using preservation by the autoequivalence. Addition of commuting maps gives the
preadditive structure; created kernels and cokernels give abelianness and exactness.
An invertible commuting map has a commuting inverse. Construct the free pair as the
coproduct of integer powers, using the quasi-inverse in negative degrees and shifting
summands. Maps out of it are determined by their degree-zero summand, with positive
and negative recursion giving the adjunction. Its value on a generator is a generator;
filtered colimits are exact after forgetting, giving the Grothendieck property
(lem-sfb-grothendieck-filtered-finite-limits, lem-galois-equivalence-preserves-limits).
Direct sums are filtered colimits of finite sums, so the free functor is exact. Its
right adjoint preserves injectives and K-injectives (lem-exc-rg-right-adjoint-preserves-
injectives, lem-weil-pbc-right-adjoint-preserves-kinjective). Finally, forgetting
commutes with cohomology and detects its isomorphisms, hence detects derived
isomorphisms (lem-sf-exact-functor-derived-triangulated,
lem-weil-pbc-unbounded-derived-iso-cohomology). -/
theorem fixedPair_forget_properties
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wF} (IsoAlgebra F)] :
    IsGrothendieckAbelian.{vC} (IsoAlgebra F) ∧
      PreservesFiniteLimits (forget F) ∧ PreservesFiniteColimits (forget F) ∧
      (forget F).ReflectsIsomorphisms ∧
      Nonempty (Free.functor F ⊣ forget F) ∧
      PreservesFiniteLimits (Free.functor F) ∧ PreservesFiniteColimits (Free.functor F) ∧
      (∀ M : C, ((Free.functor F).obj M).carrier = ∐ (Free.obj F M)) ∧
      (∀ (M : C) (n : ℤ),
        F.map (Sigma.ι (Free.obj F M) n) ≫ ((Free.functor F).obj M).str.hom =
          (Free.objSucc F M n).hom ≫ Sigma.ι (Free.obj F M) (n + 1)) ∧
      (forget F).PreservesInjectiveObjects ∧ (forget F).PreservesKInjectiveComplexes ∧
      (forget F).mapDerivedCategory.ReflectsIsomorphisms := by
  have hfree : PreservesFiniteLimits (Free.functor F) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have hinj : (forget F).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Free.adjunction F)
  have hreflect : (forget F).mapDerivedCategory.ReflectsIsomorphisms :=
    ⟨fun f _ ↦ by
      rw [DerivedCategory.isIso_iff]
      intro n
      have : IsIso ((forget F).map ((DerivedCategory.homologyFunctor _ n).map f)) :=
        (NatIso.isIso_map_iff ((forget F).mapDerivedCategoryHomologyFunctorIso n) f).2
          (by rw [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _ (forget F)⟩
  exact ⟨isGrothendieckAbelian F, inferInstance, inferInstance, inferInstance,
    ⟨Free.adjunction F⟩, hfree, inferInstance, fun _ ↦ rfl,
    fun M n ↦ Free.map_ι_comp_str F M n, hinj, inferInstance, hreflect⟩

-- Naturality propagates an equality of units along arbitrary K-injective resolutions.

end CategoryTheory.Endofunctor.IsoAlgebra
