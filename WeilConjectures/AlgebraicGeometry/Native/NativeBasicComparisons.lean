/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.WeilSheaf.FiniteLeray
import WeilConjectures.WeilSheaf.LowerStarId
import WeilConjectures.WeilSheaf.UpperStarId
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction

/-! # Basic comparisons for native derived Weil sheaves

Source: WeilSheaf/FiniteLeray.lean, `rightDerivedLowerStarCompIso`;
WeilSheaf/LowerStarComp.lean and LowerStarId.lean; WeilSheaf/OpenImmersion.lean,
exactness and constructibility of extension by zero.
(blueprint: lem-sf-native-weil-basic-comparisons)

The functors act on the ordinary derived categories of all pro-etale Weil sheaves.
The constructible subcategory is exactly `WeilComplex.objectProperty`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

/-- Direct-image composition and identities, and exact open extension with its bounded
constructibility and composition comparisons, in the native equivariant derived categories.

Source: WeilSheaf/FiniteLeray.lean, `preservesKInjectiveComplexes_lowerStar` and
`rightDerivedLowerStarCompIso`; LowerStarComp.lean, `lowerStarCompIso`;
LowerStarId.lean, `lowerStarIdIso`; OpenImmersion.lean, exactness instances and
`isAdicConstructibleSheaf_extensionByZero`.
(blueprint: lem-sf-native-weil-basic-comparisons)

Proof plan, in the order of the DAG proof:
1. The twisted action-site presentation (`lem-sf-twisted-action-ringed-site`) makes the
native category Grothendieck, with exact conservative carrier creating limits and colimits.
`prop-pur-kinjective-resolutions-exist` supplies native K-injective resolutions.
2. Write the locally finite function sheaf as the sheafified colimit of finite-extension
continuous function sheaves. The canonical pullback maps for these are isomorphisms by
`lem-weil-pbc-continuous-coefficient-general-pullback-isIso`. Inverse image preserves the
colimit (`situation-conventions` and
`def-weil-proetale-inverse-image`), so the canonical coefficient pullback is an isomorphism.
3. The module adjunction (`lem-weil-pbc-ringed-topoi-module-adjunction`) consequently has
exact left adjoint (`lem-weil-pbc-site-pullback-abelian-exact`). The unit and counit commute
with Frobenius on the same pulled-back test and section; their mate is the actual framework
comparison. Thus `lem-sf-fixed-pair-adjunction-lift` gives the native adjunction.
4. Fibre-product identifications on test objects give the underived direct-image
composition and identity isomorphisms and commute with the coefficient actions and Frobenius.
5. The exact-left-adjoint criterion (`lem-weil-pbc-right-adjoint-preserves-kinjective`)
shows that direct image preserves K-injectives. On one native K-injective resolution the
composition comparison is the underived chain isomorphism. Total derivation and the Hom
bijection (`lem-weil-pbc-kinjective-total-derived`, `def-sfb-right-derived-functor`,
`lem-weil-pbc-kinjective-hom-derived`) make it natural on the full derived category.
6. The same computation for the identity gives its derived identity comparison, without
any bound or constructibility restriction.
7. Localize the pro-etale site at the open (`lem-weil-proetale-weakly-etale-localization`).
The exact module extension by zero of `lem-weil-pbc-ringed-sheaf-slice-adjunction` has the
framework's carrier. Its unit and counit commute with Frobenius on sections, so the lifted
native extension is exact, using the conservative carrier from step 1.
8. Exact-functor descent (`situation-conventions`) gives precisely
`mapDerivedCategory`. Its cohomology is extension by zero of the cohomology, so it preserves
the finite cohomological interval.
9. `lem-sf-native-weil-open-exact-constructible` supplies the framework's locally finite
stratified constructibility for each cohomology sheaf. Together with step 8 it gives the
bounded constructible assertion, with exactly `WeilComplex.objectProperty`.
10. Successive open restrictions are restriction to the same open with the same Frobenius.
The native extension/restriction adjunctions and
`lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection` give natural successive-open and
identity-open extension isomorphisms in the native sheaf categories.
11. Descend these isomorphisms termwise using `lem-sfb-exact-derived-composition` and
`lem-sfb-exact-derived-natural-iso`. The identity localization factorization of
`def-weil-abstract-derived-category` gives the identity derived functor. All steps are local
on the geometric-fibre sites and use no absolute separatedness.
-/
theorem nativeWeilBasicComparisons (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    (∀ (S T H : Scheme.{u})
      [S.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
      [H.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (H ↘ Spec (CommRingCat.of k₀))]
      (f : S ⟶ T) (g : T ⟶ H)
      [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l (f ≫ g)).rightDerivedFunctor ≅
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor)) ∧
    (∀ (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 S)).rightDerivedFunctor ≅
        𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l S)))) ∧
    (∀ (U S : Scheme.{u})
      [U.Over (Spec (CommRingCat.of k₀))] [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))]
      [IsOpenImmersion j] [QuasiCompact j],
      PreservesFiniteLimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      PreservesFiniteColimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      ∀ (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l U)),
        WeilComplex.objectProperty k₀ l U K →
          WeilComplex.objectProperty k₀ l S
            ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.obj K)) ∧
    (∀ (U S T : Scheme.{u})
      [U.Over (Spec (CommRingCat.of k₀))] [S.Over (Spec (CommRingCat.of k₀))]
      [T.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ S) (i : S ⟶ T)
      [j.IsOver (Spec (CommRingCat.of k₀))] [i.IsOver (Spec (CommRingCat.of k₀))]
      [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i] [QuasiCompact i],
      Nonempty ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ≅
          (ProEtaleWeilSheaf.extensionByZero k₀ l (j ≫ i)).mapDerivedCategory)) ∧
    (∀ (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.extensionByZero k₀ l (𝟙 S)).mapDerivedCategory ≅
        𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l S)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S T H _ _ _ _ _ _ f g _ _
    exact ⟨ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l f g⟩
  · intro S _ _
    exact ⟨Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l S) ≪≫
      (𝟭 (ProEtaleWeilSheaf k₀ l S)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _⟩
  · intro U S _ _ _ _ j _ _ _
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro K hK
    refine ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j).bounded_mapDerivedCategory_obj hK.1,
      fun n ↦ ?_⟩
    exact (WeilSheaf.objectProperty k₀ l S).prop_of_iso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategoryHomologyFunctorIso
        n).app K)
      (WeilSheaf.isAdicConstructibleSheaf_extensionByZero j _ (hK.2 n))
  · intro U S T _ _ _ _ _ _ j i _ _ _ _ _ _
    let adj := (nativeOpenAdjunction k₀ l j).comp (nativeOpenAdjunction k₀ l i)
    let adj' := (nativeOpenAdjunction k₀ l (j ≫ i)).ofNatIsoRight
      (ProEtaleWeilSheaf.upperStarCompIso k₀ l j i)
    exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointUniq adj adj')⟩
  · intro S _ _
    let adj := (nativeOpenAdjunction k₀ l (𝟙 S)).ofNatIsoRight
      (ProEtaleWeilSheaf.upperStarIdIso k₀ l S)
    exact ⟨Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointUniq adj Adjunction.id) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩

end AlgebraicGeometry
