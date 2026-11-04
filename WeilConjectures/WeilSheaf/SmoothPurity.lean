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

/-!
# Smooth purity for Weil complexes

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of
finite type, the exceptional inverse image of Weil complexes is the twisted shifted pullback,
`Rf^! ≅ f^*(d)[2d]`. Since `Rf^!` is characterized as the right adjoint of the direct image with
compact support `Rf₀!` (`def-weil-exceptional-inverse-image`), this is the statement that
`f^*(d)[2d]` is right adjoint to `Rf₀!`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`, the Weil stage
`Λ = ℚ̄_ℓ` of `sk-thm-purity-transport`).

## Proof

`Rf₀!` has a right adjoint `Rf^!`
(`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`), so it suffices to show
`f^*(d)[2d] ≅ Rf^!`. Forgetting the Weil structure, the underlying complex of `Rf^! L` on the
geometric fibre `X̄` is `Rf̄^!` of that of `L`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`).
Through this identification, the purity map `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` of Weil complexes
is the geometric purity map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap`),
which is an isomorphism by smooth purity over `k̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`). Forgetting
the Weil structure reflects isomorphisms
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map`), so `γ_f`
is an isomorphism.

As in the blueprint (`def-pur-smooth-purity-map`), `γ_f` is the composite
`f^* L(d)[2d] ≅ f^* L ⊗ ℚ̄_ℓ(d)[2d] ≅ f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L` of
- the identification of the Tate twist with a tensor product
  (`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`);
- the inverse of the Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
  (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_smooth`);
- the co-projection map of Weil complexes, which lies over the geometric one
  (`AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap`).

## Unfinished

The three inputs of `γ_f` listed above are stated with `sorry`:
- the Weil orientation needs the Frobenius equivariance of the smooth purity isomorphism
  `Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` (`thm-pur-weil-equivariance-of-purity-and-trace`). The condensed
  orientation `AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation` is not canonical, and
  `AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism` is for finite coefficients
  over `Spec k₀`;
- the co-projection map needs the compatibility of forgetting the Weil structure with the native
  tensor product, the projection formula and the counit of `Rf₀! ⊣ Rf^!`;
- the identification of the Tate twist needs a comparison of
  `AlgebraicGeometry.WeilComplex.tensorLisse` with the native tensor product.
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

/-- A diagram lemma for `exists_natTrans_forget_eq_upperShriekUnitTensorMap`:
if `G (H p)` is `ψ' ≫ u ≫ φ'⁻¹`, then `G (H (a ≫ p)) ≫ φ` is
`(G (H a) ≫ ψ' ≫ u ≫ φ'⁻¹ ≫ φ ≫ u⁻¹) ≫ u`. -/
private lemma comp_map_comp_hom_eq_of_eq {A B C : Type*} [Category* A] [Category* B]
    [Category* C] (H : A ⥤ B) (G : B ⥤ C) {S T R : A} {P Q : C} (a : S ≅ T) (p : T ⟶ R)
    {φ φ' : G.obj (H.obj R) ≅ Q} {ψ' : G.obj (H.obj T) ≅ P} {u : P ≅ Q}
    (h : G.map (H.map p) = (ψ'.hom ≫ u.hom) ≫ φ'.inv) :
    G.map (H.map (a.hom ≫ p)) ≫ φ.hom =
      (G.mapIso (H.mapIso a) ≪≫ ψ' ≪≫ u ≪≫ φ'.symm ≪≫ φ ≪≫ u.symm).hom ≫ u.hom := by
  simp [h]

/-- **The Weil orientation of a smooth morphism** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ` with Weil
structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d`, the
relative dualizing complex `Rf^! ℚ̄_ℓ` is isomorphic to `ℚ̄_ℓ(d)[2d]` as a Weil complex.

On the geometric fibre this is the smooth purity isomorphism `Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`). The content is that the orientation
commutes with the Frobenius structures, as in the finite-coefficient statement over `Spec k₀`
`AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism`. A Frobenius-equivariant
isomorphism of underlying complexes lifts to a morphism of Weil complexes
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_mapDerivedCategory_map_eq`), which is then an
isomorphism since forgetting the Weil structure reflects isomorphisms. This is stated with
`sorry`; see the module docstring.

`AlgebraicGeometry.WeilComplex.nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth` is the same
statement for an arbitrary right adjoint of `Rf₀!`, deduced from smooth purity. -/
theorem nonempty_upperShriek_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) :=
  sorry

/-- **Weil equivariance of the purity map** (blueprint:
`thm-pur-weil-equivariance-of-purity-and-trace`, at the coefficient stage `ℚ̄_ℓ`): let
`f : X ⟶ Y` be smooth separated of pure relative dimension `d`, and let `φ_L` identify the
underlying complex on `X̄` of `Rf^! L` with `Rf̄^!` of the underlying complex `L̄` of `L` (such
identifications exist by
`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`).
Then there is a natural morphism of Weil complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which,
read through `φ_L`, is the geometric purity map
`γ_{f̄,L̄} : f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`) up to an isomorphism `ψ_L`
of the sources.

The source isomorphism `ψ_L` is the comparison of pullback, Tate twist and shift with forgetting
the Weil structure, followed by the smooth purity isomorphism `Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`); here it is only required to exist.
The content is the construction of `γ_f` as a morphism of Weil complexes: the geometric purity map
must commute with the Frobenius structures. As in the blueprint (`def-pur-smooth-purity-map`),
`γ_f` is the co-projection map
(`AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap`)
precomposed with the Weil orientation
(`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_smooth`) and the
identification of the Tate twist with a tensor product
(`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`).
Since the geometric purity map is an isomorphism, the identification of the targets coming with
the co-projection map can be replaced by `φ_L`. -/
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
  obtain ⟨π, hπ⟩ :=
    exists_coprojection_forget_eq_upperShriekUnitTensorMap (k₀ := k₀) (l := l) f
  obtain ⟨θ⟩ := nonempty_upperShriek_obj_adicConstant_iso_of_smooth (k₀ := k₀) (l := l) f d
  obtain ⟨τ⟩ := nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift k₀ l X d (2 * d)
  -- `f^* L(d)[2d] ≅ f^* L ⊗ ℚ̄_ℓ(d)[2d] ≅ f^* L ⊗ Rf^! ℚ̄_ℓ`
  let e : (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
      (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)) ≅
      (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
        ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) :=
    NatIso.ofComponents (fun K ↦ Iso.prod (Iso.refl K) θ.symm) (fun _ ↦ by
      ext <;> simp)
  let α := Functor.isoWhiskerLeft (upperStar f)
    (τ.symm ≪≫ Functor.isoWhiskerRight e (nativeConstructibleTensor k₀ l X))
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := d) (f := f)
  have : Smooth (geometricFiberHom (k₀ := k₀) f).left :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f (comp_over f _) ‹_›
  refine ⟨α.hom ≫ π, fun L ↦ ?_⟩
  obtain ⟨φ', ψ', h⟩ := hπ L
  have := CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)
  let u := asIso ((ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)))
  refine ⟨(adicSheafDerivedEquivCondensedMod l _).functor.mapIso (forget.mapIso (α.app L)) ≪≫
    ψ' ≪≫ u ≪≫ φ'.symm ≪≫ φ L ≪≫ u.symm, ?_⟩
  have h' : (adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map (forget.map (π.app L)) =
      (ψ'.hom ≫ u.hom) ≫ φ'.inv :=
    (Iso.eq_comp_inv φ').2 h
  exact comp_map_comp_hom_eq_of_eq _ _ (α.app L) (π.app L) h'

/-- **The purity map of Weil complexes** (blueprint: `thm-pur-weil-equivariance-of-purity-and-trace`
and `sk-thm-purity-transport`, at the coefficient stage `ℚ̄_ℓ` with Weil structures): for a smooth
separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of finite type, there
is a natural morphism of Weil complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which is an isomorphism
on the underlying `ℓ`-adic complexes on the geometric fibre `X̄`.

The underlying complex of `Rf^! L` is `Rf̄^!` of that of `L`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`),
and through this identification `γ_f` is the geometric purity map
(`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap`),
an isomorphism by smooth purity
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`). -/
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

/-- **Smooth purity for Weil complexes** (blueprint: `sk-thm-purity-transport`, at the coefficient
stage `ℚ̄_ℓ` with Weil structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative
dimension `d` of `k₀`-schemes of finite type, the twisted shifted pullback `K ↦ f^* K(d)[2d]` of
Weil complexes is right adjoint to the direct image with compact support `Rf₀!`; that is,
`Rf^! ≅ f^*(d)[2d]`. The purity map `f^*(d)[2d] ⟶ Rf^!`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`) is an
isomorphism, since forgetting the Weil structures reflects isomorphisms. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth (d : ℕ)
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

variable {f} in
/-- **The exceptional inverse image of `ℚ̄_ℓ` along a smooth morphism** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ`): for a
smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d`, and any right adjoint `G` of
`Rf₀!`, `G ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`. This is smooth purity
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`) applied to
`ℚ̄_ℓ`, with `f^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
theorem nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {G : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ G) :
    Nonempty (G.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨adj'⟩ := nonempty_derivedLowerShriek_adjunction_of_smooth (k₀ := k₀) (l := l) f d
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
