/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.TateTwistNativeTensor
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
public import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.TraceFormula.PurityDevissage
import WeilConjectures.WeilSheaf.SmoothPurityMapOfOrientation
import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent
import WeilConjectures.WeilSheaf.SmoothPurityOrientationOfTateEncoding

/-!
# Smooth purity for Weil complexes

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of
finite type, the exceptional inverse image of Weil complexes is the twisted shifted pullback,
`Rf^! ≅ f^*(d)[2d]`; equivalently, `f^*(d)[2d]` is right adjoint to the direct image with compact
support `Rf₀!`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`).

## Implementation details

Forgetting the Weil structure, the underlying complex of `Rf^! L` on the geometric fibre `X̄` is
`Rf̄^!` of that of `L`. Through this identification, the purity map
`γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` of Weil complexes is the geometric purity map
`f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`, which is an isomorphism by smooth purity over `k̄`; since
forgetting the Weil structure reflects isomorphisms, `γ_f` is an isomorphism.

The map `γ_f` is the composite `f^* L(d)[2d] ≅ f^* L ⊗ ℚ̄_ℓ(d)[2d] ≅ f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L`
of the identification of the Tate twist with a tensor product, the inverse of the Weil
orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` and the co-projection map of Weil complexes.

The Frobenius-equivariant orientation is proved from the native Tate encoding and the
invertibility of the exceptional unit base change along `k₀ ⟶ k̄₀` (by Verdier duality). The
co-projection map still rests on a statement with `sorry`: the Weil projection formula
`AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso`.

The general statement `nonempty_derivedLowerShriek_adjunction_of_smooth` (no separatedness of the
base) is stated with `sorry`; the separated case
`nonempty_derivedLowerShriek_adjunction_of_smooth_of_isSeparated` is proved and is the one used by
`AlgebraicGeometry.Scheme.weil_conjectures`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Geometric

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- **Frobenius equivariance of the orientation of a smooth morphism**: for a smooth separated
morphism `f : X ⟶ Y` of pure relative dimension `d`, there is an isomorphism
`Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of the underlying complexes on the geometric fibre `X̄` which commutes
with the Frobenius structures `Fr_X^* (-) ≅ (-)` of the two Weil complexes. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨α⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ l X d
  exact exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding f d α

/-- **The Weil orientation of a smooth morphism**: for a smooth separated morphism `f : X ⟶ Y` of
pure relative dimension `d`, the relative dualizing complex `Rf^! ℚ̄_ℓ` is isomorphic to
`ℚ̄_ℓ(d)[2d]` as a Weil complex. -/
theorem nonempty_upperShriek_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨g, hg⟩ :=
    exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso (k₀ := k₀) (l := l) f d
  obtain ⟨e⟩ := Endofunctor.IsoAlgebra.nonempty_iso_of_forget_mapDerivedCategory_iso _ g hg
  exact ⟨ObjectProperty.isoMk _ e⟩

/-- **Weil equivariance of the purity map**: let `f : X ⟶ Y` be smooth separated of pure
relative dimension `d`, and let `φ_L` identify the underlying complex on `X̄` of `Rf^! L` with
`Rf̄^!` of the underlying complex `L̄` of `L`. Then there is a natural morphism of Weil complexes
`γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which, read through `φ_L`, is the geometric purity map
`γ_{f̄,L̄} : f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄` up to an isomorphism `ψ_L` of the sources. -/
theorem exists_natTrans_forget_eq_upperShriekUnitTensorMap (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (φ : ∀ L : WeilComplex k₀ l Y, (adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
          (forget.obj ((upperShriek f).obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
        (geometricFiberBoundedConstructibleObj L)).obj) :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, ∃ ψ : (adicSheafDerivedEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
            (forget.obj ((upperStar f ⋙ tateTwist k₀ l X d ⋙
              shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
              (geometricFiberBoundedConstructibleObj L) ⊗
            (CondensedRing.boundedConstructibleUpperShriek l
              (geometricFiberHom (k₀ := k₀) f)).obj (𝟙_ _)).obj,
        (adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (γ.app L)) ≫ (φ L).hom =
          ψ.hom ≫ (ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
            (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)) := by
  obtain ⟨θ⟩ := nonempty_upperShriek_obj_adicConstant_iso_of_smooth (k₀ := k₀) (l := l) f d
  exact exists_natTrans_forget_eq_upperShriekUnitTensorMap_of_orientation
    (k₀ := k₀) (l := l) f d θ φ

/-- **The purity map of Weil complexes**: for a smooth separated morphism `f : X ⟶ Y` of pure
relative dimension `d` of `k₀`-schemes of finite type, there is a natural morphism of Weil
complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which is an isomorphism on the underlying `ℓ`-adic
complexes on the geometric fibre `X̄`. -/
theorem exists_natTrans_upperShriek_isIso_forget_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, IsIso (forget.map (γ.app L)) := by
  have φ (L : WeilComplex k₀ l Y) :=
    (nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek f
      (derivedLowerShriekUpperShriekAdjunction f) L).some
  obtain ⟨γ, hγ⟩ :=
    exists_natTrans_forget_eq_upperShriekUnitTensorMap (l := l) f d φ
  refine ⟨γ, fun L ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := hγ L
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := d) (f := f)
  have : Smooth (geometricFiberHom (k₀ := k₀) f).left :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f (comp_over f _) ‹_›
  have := CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)
  have : IsIso ((adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (γ.app L))) := by
    rw [(Iso.eq_comp_inv _).2 hψ]
    infer_instance
  exact isIso_of_reflects_iso _ (adicSheafDerivedEquivCondensedMod l _).functor

end Geometric

/-- **Smooth purity for Weil complexes** (separated base): for a smooth separated morphism
`f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of finite type, the twisted shifted
pullback `K ↦ f^* K(d)[2d]` of Weil complexes is right adjoint to the direct image with compact
support `Rf₀!`; that is, `Rf^! ≅ f^*(d)[2d]`. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth_of_isSeparated (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l f ⊣
      upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)) := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have := isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l) f
  obtain ⟨γ, hγ⟩ := exists_natTrans_upperShriek_isIso_forget_of_smooth (k₀ := k₀) (l := l) f d
  have (L : WeilComplex k₀ l Y) : IsIso (γ.app L) := by
    have : IsIso ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map (γ.app L).hom) :=
      hγ L
    have : IsIso ((ObjectProperty.ι (WeilComplex.objectProperty k₀ l X)).map (γ.app L)) :=
      Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map (γ.app L).hom
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact ⟨(derivedLowerShriekUpperShriekAdjunction f).ofNatIsoRight (asIso γ).symm⟩

/-- **Smooth purity for Weil complexes**: for a smooth separated morphism `f : X ⟶ Y` of pure
relative dimension `d` of `k₀`-schemes of finite type, the twisted shifted pullback
`K ↦ f^* K(d)[2d]` of Weil complexes is right adjoint to the direct image with compact support
`Rf₀!`; that is, `Rf^! ≅ f^*(d)[2d]`. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty (derivedLowerShriek k₀ l f ⊣
      upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)) :=
  sorry

variable {f} in
/-- **The exceptional inverse image of `ℚ̄_ℓ` along a smooth morphism**: for a smooth separated
morphism `f : X ⟶ Y` of pure relative dimension `d` and any right adjoint `G` of `Rf₀!`,
`G ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`. -/
theorem nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {G : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ G) :
    Nonempty (G.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨adj'⟩ :=
    nonempty_derivedLowerShriek_adjunction_of_smooth_of_isSeparated (k₀ := k₀) (l := l) f d
  let e : (upperStar f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
    (ObjectProperty.isoMk _ (((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategorySingleFunctor
      0).app (WeilSheaf.adicConstant k₀ l Y).obj) :
        _ ≅ WeilSheaf.toComplex.obj
          ((WeilSheaf.upperStar f).obj (WeilSheaf.adicConstant k₀ l Y))) ≪≫
      WeilSheaf.toComplex.mapIso (WeilSheaf.upperStarAdicConstantIso f)
  exact ⟨(adj.rightAdjointUniq adj').app _ ≪≫
    (tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)).mapIso e⟩

end WeilComplex

end AlgebraicGeometry
