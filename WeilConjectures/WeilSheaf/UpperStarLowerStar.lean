/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCounit

/-!
# The counit `φ^* φ_* ⟶ 𝟭` of Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the counit `φ̄^* φ̄_* ⟶ 𝟭` of the pro-étale adjunction
along the base change `φ̄ : X̄ ⟶ Ȳ` is compatible with the Weil structures, the adjunction units and
counits of the six operations being Weil-equivariant (blueprint `lem-fix-weil-operations`). It
therefore induces a counit `φ^* φ_* ⟶ 𝟭` of Weil sheaves. Along an open immersion `j` the counit
is invertible, so `j^* j_* F ≅ F` for every Weil sheaf `F` on the open.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.lowerStarCompUpperStarCounit`: the counit `φ^* φ_* ⟶ 𝟭`.
- `AlgebraicGeometry.WeilSheaf.upperStarDirectImageIso`: `j^* j_* F ≅ F` for an open immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- **The counit of `φ̄^* ⊣ φ̄_*` is Frobenius-equivariant**: for an `ℓ`-adic sheaf `M` on `X̄`, the
Frobenius pullback of the counit `φ̄^* φ̄_* M ⟶ M` is the counit at `Fr_X^* M`, conjugated by the
Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*`
(`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` and
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`). This is the
statement that the adjunction counit carries a Weil structure.
(blueprint: `lem-fix-weil-operations`, the adjunction counits) -/
theorem ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius :
    IsoAlgebra.CounitCompatible
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
      (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).counit := by
  sorry

variable (k₀ l) in
/-- The counit `φ^* φ_* ⟶ 𝟭` of pro-étale Weil sheaves: the counit of `φ̄^* ⊣ φ̄_*`, which is
compatible with the Weil structures
(`AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius`). -/
noncomputable def ProEtaleWeilSheaf.lowerStarCompUpperStarCounit :
    IsoAlgebra.mapOfNatIso (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ
        (comp_over φ (Spec (CommRingCat.of k₀)))) ⋙
      IsoAlgebra.mapOfNatIso (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
        (comp_over φ (Spec (CommRingCat.of k₀)))) ⟶ 𝟭 (ProEtaleWeilSheaf k₀ l X) :=
  IsoAlgebra.mapOfNatIsoCompCounit
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
      (comp_over φ (Spec (CommRingCat.of k₀))))).counit
    (ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius φ)

/-- Along an open immersion the counit `j^* j_* ⟶ 𝟭` of pro-étale Weil sheaves is invertible: the
counit of the pro-étale adjunction along the open immersion `j̄` is. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCompUpperStarIso [IsOpenImmersion φ] :
    IsoAlgebra.mapOfNatIso (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ
        (comp_over φ (Spec (CommRingCat.of k₀)))) ⋙
      IsoAlgebra.mapOfNatIso (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
        (comp_over φ (Spec (CommRingCat.of k₀)))) ≅ 𝟭 (ProEtaleWeilSheaf k₀ l X) :=
  IsoAlgebra.mapOfNatIsoCompCounitIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
      (comp_over φ (Spec (CommRingCat.of k₀))))).counit
    (ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius φ)

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The restriction of the direct image to the open**: for an open immersion `j : U ↪ X`, the
counit `j^* j_* ⟶ 𝟭` of Weil sheaves is an isomorphism. -/
noncomputable def lowerStarCompUpperStarIso [IsOpenImmersion φ] :
    WeilSheaf.lowerStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.upperStar φ ≅ 𝟭 _ :=
  ((WeilSheaf.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarCompUpperStarIso φ) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- **The restriction of the direct image to the open**: `j^* j_* F ≅ F` for an open immersion
`j : U ↪ X` and a Weil sheaf `F` on `U`. -/
noncomputable def upperStarDirectImageIso [IsOpenImmersion φ] (F : WeilSheaf k₀ l X) :
    (WeilSheaf.upperStar φ).obj ((WeilSheaf.lowerStar φ).obj F) ≅ F :=
  (lowerStarCompUpperStarIso φ).app F

end WeilSheaf

end AlgebraicGeometry
