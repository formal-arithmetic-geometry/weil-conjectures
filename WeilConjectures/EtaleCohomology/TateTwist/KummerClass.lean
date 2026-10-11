/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalarsExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalarsComp
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.SixFunctors.Etale.Derived.SingleDelta
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Composition

/-!
# The Kummer classes

Let `Λ` be a commutative ring of positive characteristic `n` and `X` a scheme on which `n` is
invertible. A unit `u` of `X` is a morphism `ℤ ⟶ 𝔾ₘ` of étale sheaves
(`AlgebraicGeometry.Etale.unitToGmSheaf`). Pulling the Kummer sequence
`0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` back along it gives the short exact sequence
`0 ⟶ μₙ ⟶ {(x, k) | xⁿ = uᵏ} ⟶ ℤ ⟶ 0` (the class of the `μₙ`-torsor of `n`-th roots of `u`),
and extending scalars to `Λ` keeps it exact, since `ℤ` is projective
(`AlgebraicGeometry.Etale.shortExact_kummerShortComplex_map_extendScalars`). Its connecting
morphism is the *Kummer class*

`κ(u) : Λ_X ⟶ (μₙ ⊗ Λ)[1] = Λ_X(1)[1]`

(`AlgebraicGeometry.Etale.kummerClassOf`): the boundary of `u` in the Kummer sequence, with
coefficients extended to `Λ`. It is additive in `u` (`AlgebraicGeometry.Etale.kummerClassOf_mul`).

## Main definitions

- `AlgebraicGeometry.Etale.kummerClassOf`: the Kummer class `κ(u) ∈ H¹(X, Λ(1))`.
- `AlgebraicGeometry.Etale.hasKummerClass`: the Kummer class datum of the Tate twist `μₙ ⊗ Λ`,
  natural under pullback (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClassOf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Scheme

/-- The constant étale sheaf `ℤ` (written `ℤ/0`, so as to reuse the lemmas on `ℤ/n`). -/
noncomputable abbrev constantSheafInt (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  X.constantZMod 0

variable {X : Scheme.{u}}

/-- The morphism `ℤ ⟶ 𝔾ₘ` of étale sheaves given by a unit `u` of `X`: `k ↦ uᵏ`. -/
noncomputable def unitToGmSheaf (u : Γ(X, ⊤)ˣ) : X.constantSheafInt ⟶ X.gmSheaf :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv
    _ _).symm (zmodToGmSections 0 u (pow_zero u))

lemma zmodToGmSections_zero_mul (u v : Γ(X, ⊤)ˣ) :
    zmodToGmSections 0 (u * v) (pow_zero _) =
      zmodToGmSections 0 u (pow_zero u) + zmodToGmSections 0 v (pow_zero v) := by
  have key : ∀ {G : AddCommGrpCat.{u + 1}} (f g : AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)) ⟶ G),
      f.hom (ULift.up 1) = g.hom (ULift.up 1) → f = g := by
    intro G f g h
    ext ⟨a⟩
    have ha : (ULift.up a : ULift.{u + 1} (ZMod 0)) = (a : ℤ) • ULift.up 1 := by
      apply ULift.ext
      change a = (a : ℤ) • (1 : ZMod 0)
      simp
    rw [ha, map_zsmul, map_zsmul, h]
  apply key
  have h1 := zmodToGmSections_natCast 0 (u * v) (pow_zero _) 1
  have h2 := zmodToGmSections_natCast 0 u (pow_zero _) 1
  have h3 := zmodToGmSections_natCast 0 v (pow_zero _) 1
  simp only [Nat.cast_one, pow_one] at h1 h2 h3
  rw [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, h1, h2, h3, gmSection_mul]

instance (U : (X.Etale)ᵒᵖ) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U).Additive where
  map_add {_ _ _ _} := rfl

lemma unitToGmSheaf_mul (u v : Γ(X, ⊤)ˣ) :
    unitToGmSheaf (u * v) = unitToGmSheaf u + unitToGmSheaf v := by
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _).injective
  rw [unitToGmSheaf, Equiv.apply_symm_apply, zmodToGmSections_zero_mul, Adjunction.homEquiv_unit,
    Functor.map_add, Preadditive.comp_add, ← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_unit]
  simp only [unitToGmSheaf, Equiv.apply_symm_apply]

end Scheme

namespace Etale

open Scheme

/-- Homomorphisms out of `ℤ` are determined by the image of `1`. -/
lemma _root_.AddCommGrpCat.hom_ext_uliftInt {G : AddCommGrpCat.{u + 1}}
    {f g : AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)) ⟶ G}
    (h : f.hom (ULift.up 1) = g.hom (ULift.up 1)) : f = g := by
  ext ⟨a⟩
  have ha : (ULift.up a : ULift.{u + 1} (ZMod 0)) = (a : ℤ) • ULift.up 1 := by
    apply ULift.ext
    change a = (a : ℤ) • (1 : ZMod 0)
    simp
  rw [ha, map_zsmul, map_zsmul, h]

instance : Projective (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0))) where
  factors {E F} f e he := by
    rw [AddCommGrpCat.epi_iff_surjective] at he
    obtain ⟨x, hx⟩ := he (f.hom (ULift.up 1))
    refine ⟨AddCommGrpCat.ofHom ((zmultiplesHom E x).comp
      (AddEquiv.ulift.toAddMonoidHom : ULift.{u + 1} (ZMod 0) →+ ℤ)), ?_⟩
    apply AddCommGrpCat.hom_ext_uliftInt
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
      Function.comp_apply, zmultiplesHom_apply, AddEquiv.coe_toAddMonoidHom, map_zsmul, hx]
    exact one_smul ℤ _

variable {X : Scheme.{u}}

lemma projective_sheafFiber_constantSheafInt (P : X.smallEtaleTopology.Point.{u + 1}) :
    Projective (P.sheafFiber.obj X.constantSheafInt) :=
  Projective.of_iso (P.sheafFiberConstantSheafIso _).symm inferInstance

variable (Λ : Type (u + 1)) [CommRing Λ] [HasInvertibleExponent Λ X]

/-- The Kummer sequence pulled back along a morphism `φ : C ⟶ 𝔾ₘ` from a sheaf with projective
stalks, with coefficients extended to `Λ`, is short exact. -/
lemma shortExact_kummerSequence_pullback_map_extendScalars
    {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (((X.kummerSequence (ringChar Λ)).pullback φ).map (extendScalars Λ X)).ShortExact :=
  shortExact_map_extendScalars Λ ((X.kummerSequence_shortExact _
    (isUnit_ringChar_of_hasInvertibleExponent X)).pullback φ) hC

/-- The connecting morphism `Λ ⊗ C ⟶ (μₙ ⊗ Λ)[1]` of the Kummer sequence pulled back along
`φ : C ⟶ 𝔾ₘ`, with coefficients extended to `Λ`. -/
noncomputable def kummerδ {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj C) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))))⟦(1 : ℤ)⟧ :=
  (shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC).singleδ

/-- The connecting morphisms of pulled back Kummer sequences are compatible with
precomposition. -/
lemma kummerδ_comp {C C' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ψ : C' ⟶ C)
    (φ : C ⟶ X.gmSheaf) (hC) (hC') :
    kummerδ Λ (ψ ≫ φ) hC' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalars Λ X).map ψ) ≫ kummerδ Λ φ hC := by
  have h := (ShortComplex.ShortExact.singleTriangle.map
    (shortExact_kummerSequence_pullback_map_extendScalars Λ (ψ ≫ φ) hC')
    (shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC)
    ((extendScalars Λ X).mapShortComplex.map
      ((X.kummerSequence (ringChar Λ)).pullbackMap φ ψ))).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃] at h
  simp only [Functor.mapShortComplex_map_τ₁, ShortComplex.pullbackMap_τ₁,
    CategoryTheory.Functor.map_id, Functor.mapShortComplex_map_τ₃,
    ShortComplex.pullbackMap_τ₃] at h
  unfold kummerδ
  rw [← h]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

instance : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
  (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).left_adjoint_additive

variable [NeZero (ringChar Λ)]

variable (X) in
/-- The constant complex `Λ_X` is `Λ ⊗ ℤ` placed in degree zero: the identification through the
monoidal unit and `Λ ⊗ ℤ ≅ Λ`. -/
noncomputable def constantComplexIsoSingleFunctorExtendScalarsIntOfUnit :
    constantComplex Λ X ≅
      (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj X.constantSheafInt) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (extendScalarsConstantZModIso X (n := 0) (by simp)).symm

/-- For `π : X ⟶ S`, the identification `π^*(Λ ⊗ ℤ_S) ≅ Λ ⊗ ℤ_X`. -/
noncomputable def upperStarExtendScalarsConstantSheafIntIso {S : Scheme.{u}} (π : X ⟶ S) :
    (π)^*[ModuleCat.{u + 1} Λ].obj ((extendScalars Λ S).obj S.constantSheafInt) ≅
      (extendScalars Λ X).obj X.constantSheafInt :=
  (upperStarExtendScalarsIso Λ π).app _ ≪≫
    (extendScalars Λ X).mapIso ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} π).app _)

variable (X) in
/-- The constant complex `Λ_X` is `Λ ⊗ ℤ` placed in degree zero: the identification pulled back
from the base `Spec ℤ[1/n]`, so that it is compatible with the derived pullbacks. -/
noncomputable def constantComplexIsoSingleFunctorExtendScalarsInt :
    constantComplex Λ X ≅
      (DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ X).obj X.constantSheafInt) :=
  (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) X)).symm ≪≫
    L((toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ]).mapIso
      (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit (invertibleExponentBase.{u} Λ) Λ) ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso _ (toInvertibleExponentBase (Λ := Λ) X)).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) X))

omit [NeZero (ringChar Λ)] in
lemma isUnit_ringChar_invertibleExponentBase :
    IsUnit ((ringChar Λ : ℕ) : Γ(invertibleExponentBase.{u} Λ, ⊤)) := by
  simpa using (isUnit_ringChar_invertibleExponentRing Λ).map
    (Scheme.ΓSpecIso (CommRingCat.of (InvertibleExponentRing.{u} Λ))).inv.hom

variable (X) in
/-- The sheaf `Λ_X(1)` of the Tate twist datum is the Tate sheaf `μₙ ⊗ Λ` of `X`: the pullback of
the Tate sheaf of `Spec ℤ[1/n]`, through `(μₙ ⊗ Λ) ⊗ Λ ≅ μₙ ⊗ Λ`, the compatibility of extension
of scalars with pullback, and the identification of the pullback of `μₙ` with `μₙ`. -/
noncomputable def tateTwistSheafOneIso :
    tateTwistSheaf Λ X 1 ≅ (extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ)) :=
  haveI := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit (ringChar Λ)
    (toInvertibleExponentBase (Λ := Λ) X) (isUnit_ringChar_invertibleExponentBase Λ)
  (toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ].mapIso
      (ρ_ (tateSheaf Λ (invertibleExponentBase.{u} Λ))) ≪≫
    (upperStarExtendScalarsIso Λ (toInvertibleExponentBase (Λ := Λ) X)).app _ ≪≫
    (extendScalars Λ X).mapIso
      (asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf _ (toInvertibleExponentBase X)))

variable (X) in
/-- The Tate twist `Λ_X(1)` is the Tate sheaf `μₙ ⊗ Λ` placed in degree zero. -/
noncomputable def tateTwistObjectOneIso :
    tateTwistObject Λ X 1 ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) :=
  tateTwistObjectIsoSingleFunctor Λ X 1 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tateTwistSheafOneIso X Λ)

variable (X) in
/-- Blueprint `def-pur-affine-line-datum`: The affine-line datum.

The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit `u` of `X`: the
connecting morphism of the Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` pulled back along
`u : ℤ ⟶ 𝔾ₘ`, with coefficients extended to `Λ`. -/
noncomputable def kummerClassOf (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (tateTwistObject Λ X 1)⟦(1 : ℤ)⟧ :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    kummerδ Λ (unitToGmSheaf u)
      (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)) ≫
    (tateTwistObjectOneIso X Λ).inv⟦(1 : ℤ)⟧'

variable (X) in
/-- The Kummer class is additive: `κ(uv) = κ(u) + κ(v)`. -/
lemma kummerClassOf_mul (u v : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ (u * v) = kummerClassOf X Λ u + kummerClassOf X Λ v := by
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod 0))
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let φ₂ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A ⊞ A) ⟶
      X.gmSheaf := (adj.homEquiv _ _).symm
    (biprod.desc (zmodToGmSections 0 u (pow_zero u)) (zmodToGmSections 0 v (pow_zero v)))
  have hC₂ : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A ⊞ A))) :=
    fun x ↦ Projective.of_iso ((X.uliftPointSmallEtale x).sheafFiberConstantSheafIso _).symm
      inferInstance
  have hu : unitToGmSheaf u =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inl ≫ φ₂ := by
    rw [← Adjunction.homEquiv_naturality_left_symm, biprod.inl_desc]
    rfl
  have hv : unitToGmSheaf v =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inr ≫ φ₂ := by
    rw [← Adjunction.homEquiv_naturality_left_symm, biprod.inr_desc]
    rfl
  have huv : unitToGmSheaf (u * v) =
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inl +
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map biprod.inr) ≫ φ₂ := by
    rw [← Functor.map_add, ← Adjunction.homEquiv_naturality_left_symm, Preadditive.add_comp,
      biprod.inl_desc, biprod.inr_desc, ← zmodToGmSections_zero_mul]
    rfl
  simp only [kummerClassOf]
  rw [huv, hu, hv, kummerδ_comp Λ _ φ₂ hC₂, kummerδ_comp Λ _ φ₂ hC₂, kummerδ_comp Λ _ φ₂ hC₂,
    Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.add_comp,
    Preadditive.comp_add]

section Naturality

variable {Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y)

lemma zmodToGmSections_zero_comp_gmSectionsPullback (v : Γ(Y, ⊤)ˣ) :
    zmodToGmSections 0 v (pow_zero v) ≫ gmSectionsPullback f =
      zmodToGmSections 0 (Units.map f.appTop.hom.toMonoidHom v) (pow_zero _) := by
  apply AddCommGrpCat.hom_ext_uliftInt
  have h1 := zmodToGmSections_natCast 0 v (pow_zero v) 1
  have h2 := zmodToGmSections_natCast 0 (Units.map f.appTop.hom.toMonoidHom v) (pow_zero _) 1
  simp only [Nat.cast_one, pow_one] at h1 h2
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, h1, h2, gmSectionsPullback_gmSection]

/-- The morphisms `ℤ ⟶ 𝔾ₘ` given by units are compatible with pullback. -/
lemma upperStar_map_unitToGmSheaf_comp (v : Γ(Y, ⊤)ˣ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map (unitToGmSheaf v) ≫
        upperStarGmSheafToGmSheaf f =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _ ≫
        unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v) := by
  rw [unitToGmSheaf, upperStar_map_constantSheafAdj_homEquiv_symm_comp,
    zmodToGmSections_zero_comp_gmSectionsPullback]
  rfl

/-- The comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` commutes with the `n`-th power maps. -/
lemma upperStarGmSheafToGmSheaf_comp_nsmul (m : ℕ) :
    upperStarGmSheafToGmSheaf f ≫ (m • 𝟙 X.gmSheaf) =
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (m • 𝟙 Y.gmSheaf) ≫
        upperStarGmSheafToGmSheaf f := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]

/-- The comparison map from the pullback of the Kummer sequence pulled back along `v` to the
Kummer sequence pulled back along the pullback of `v`, on the middle terms. -/
noncomputable def upperStarKummerPullbackX₂ (v : Γ(Y, ⊤)ˣ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
        ((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).X₂ ⟶
      ((X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))).X₂ :=
  pullback.lift ((Etale.upperStar _ f).map (pullback.fst _ _) ≫ upperStarGmSheafToGmSheaf f)
    ((Etale.upperStar _ f).map (pullback.snd _ _) ≫
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _) (by
    change _ ≫ (ringChar Λ • 𝟙 X.gmSheaf) = _
    rw [Category.assoc, Category.assoc, upperStarGmSheafToGmSheaf_comp_nsmul,
      ← upperStar_map_unitToGmSheaf_comp, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact pullback.condition)

/-- The comparison from the pullback of the Kummer sequence pulled back along `v` to the Kummer
sequence pulled back along the pullback of `v`. -/
noncomputable def upperStarKummerPullbackHom (v : Γ(Y, ⊤)ˣ) :
    ((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).map
        (Etale.upperStar AddCommGrpCat.{u + 1} f) ⟶
      (X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v)) where
  τ₁ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf _ f
  τ₂ := upperStarKummerPullbackX₂ Λ f v
  τ₃ := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _
  comm₁₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, upperStarKummerPullbackX₂, pullback.lift_fst,
        ShortComplex.map_f, ShortComplex.pullback, ← Functor.map_comp_assoc]
      exact upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι _ f
    · simp only [Category.assoc, upperStarKummerPullbackX₂, pullback.lift_snd,
        ShortComplex.map_f, ShortComplex.pullback, ← Functor.map_comp_assoc]
      simp
  comm₂₃ := by
    simp [upperStarKummerPullbackX₂, ShortComplex.pullback]

/-- The comparison from the pullback of the Kummer sequence pulled back along `v`, with
coefficients extended to `Λ`, to the Kummer sequence pulled back along the pullback of `v`,
with coefficients extended to `Λ`. -/
noncomputable def upperStarKummerExtendScalarsHom (v : Γ(Y, ⊤)ˣ) :
    (((Y.kummerSequence (ringChar Λ)).pullback (unitToGmSheaf v)).map (extendScalars Λ Y)).map
        (f)^*[ModuleCat.{u + 1} Λ] ⟶
      ((X.kummerSequence (ringChar Λ)).pullback
        (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))).map (extendScalars Λ X) where
  τ₁ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₁
  τ₂ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₂
  τ₃ := (upperStarExtendScalarsIso Λ f).hom.app _ ≫
    (extendScalars Λ X).map (upperStarKummerPullbackHom Λ f v).τ₃
  comm₁₂ := by
    simp only [ShortComplex.map_f, Category.assoc, ← Functor.map_comp,
      (upperStarKummerPullbackHom Λ f v).comm₁₂]
    rw [Functor.map_comp]
    exact ((upperStarExtendScalarsIso Λ f).hom.naturality_assoc _ _).symm
  comm₂₃ := by
    simp only [ShortComplex.map_g, Category.assoc, ← Functor.map_comp,
      (upperStarKummerPullbackHom Λ f v).comm₂₃]
    rw [Functor.map_comp]
    exact ((upperStarExtendScalarsIso Λ f).hom.naturality_assoc _ _).symm

omit [NeZero (ringChar Λ)] in
/-- The derived pullback of the connecting morphism of the Kummer sequence pulled back along `v`
is the connecting morphism of the Kummer sequence pulled back along the pullback of `v`. -/
lemma leftDerivedUpperStar_map_kummerδ (v : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerδ Λ (unitToGmSheaf v)
        (fun y ↦ projective_sheafFiber_constantSheafInt (Y.uliftPointSmallEtale y))) ≫
      ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f)))⟦(1 : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((upperStarExtendScalarsIso Λ f).hom.app Y.constantSheafInt ≫
            (extendScalars Λ X).map
              ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _)) ≫
        kummerδ Λ (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))
          (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)) := by
  have hS := shortExact_kummerSequence_pullback_map_extendScalars Λ (unitToGmSheaf v)
    (fun y ↦ projective_sheafFiber_constantSheafInt (Y.uliftPointSmallEtale y))
  have h1 := leftDerivedUpperStar_map_singleδ (ModuleCat.{u + 1} Λ) f hS
  have h2 := (ShortComplex.ShortExact.singleTriangle.map
    (hS.map_of_exact (f)^*[ModuleCat.{u + 1} Λ])
    (shortExact_kummerSequence_pullback_map_extendScalars Λ
      (unitToGmSheaf (Units.map f.appTop.hom.toMonoidHom v))
      (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)))
    (upperStarKummerExtendScalarsHom Λ f v)).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃] at h2
  unfold kummerδ
  rw [Functor.map_comp]
  erw [reassoc_of% h1]
  exact congrArg (_ ≫ ·) h2

/-- The identifications `Λ(1) ≅ μₙ ⊗ Λ` placed in degree zero are compatible with the derived
pullbacks. -/
lemma leftDerivedUpperStar_map_tateTwistObjectOneIso :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectOneIso Y Λ).hom ≫
        (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f)) =
      (leftDerivedUpperStarTateTwistObjectIso Λ f 1).hom ≫ (tateTwistObjectOneIso X Λ).hom := by
  have hπ := (comp_toInvertibleExponentBase (Λ := Λ) f).symm
  have hc : ∀ (πX : X ⟶ invertibleExponentBase.{u} Λ)
      (hπ : πX = f ≫ toInvertibleExponentBase (Λ := Λ) Y),
      (upperStarComp _ f _ πX hπ).hom.app _ ≫
        (f)^*[AddCommGrpCat.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf
          (ringChar Λ) (toInvertibleExponentBase (Λ := Λ) Y)) ≫
          upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f =
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) πX := by
    rintro _ rfl
    exact upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp _ f _
  have hσ := upperStarComp_hom_app_comp_upperStar_map_extendScalars Λ f _ _ hπ _ _ _ (hc _ hπ)
    (ρ_ (tateSheaf Λ (invertibleExponentBase.{u} Λ))).hom
  have hG := leftDerivedUpperStar_map_singleFunctor_comp (ModuleCat.{u + 1} Λ) f _ _ hπ _
    (tateTwistSheafOneIso Y Λ).hom (tateTwistSheafOneIso X Λ).hom _ hσ
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.naturality
    ((tateSheafTensorInverse Λ).zpowSingleFunctorIso 1).hom
  simp only [tateTwistObjectOneIso, tateTwistObjectIsoSingleFunctor,
    leftDerivedUpperStarTateTwistObjectIso, pullbackIntTensorFamilyCopyIso,
    pullbackIntTensorFamilyIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Functor.comp_map] at hG n ⊢
  erw [← reassoc_of% n]
  rw [hG]

omit [NeZero (ringChar Λ)] in
/-- The identifications `Λ ≅ Λ ⊗ ℤ` placed in degree zero are compatible with the derived
pullbacks. -/
lemma leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (constantComplexIsoSingleFunctorExtendScalarsInt Y Λ).hom ≫
        (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app Y.constantSheafInt ≫
              (extendScalars Λ X).map
                ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _)) =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom := by
  have hπ := (comp_toInvertibleExponentBase (Λ := Λ) f).symm
  have hc : ∀ (πX : X ⟶ invertibleExponentBase.{u} Λ)
      (hπ : πX = f ≫ toInvertibleExponentBase (Λ := Λ) Y),
      (upperStarComp _ f _ πX hπ).hom.app _ ≫
        (f)^*[AddCommGrpCat.{u + 1}].map ((upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (toInvertibleExponentBase (Λ := Λ) Y)).hom.app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))) ≫
          (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _ =
        (upperStarConstantSheafIso AddCommGrpCat.{u + 1} πX).hom.app _ := by
    rintro _ rfl
    exact upperStarConstantSheafIso_comp _ f _ _
  have hσ := upperStarComp_hom_app_comp_upperStar_map_extendScalars Λ f _ _ hπ _ _ _ (hc _ hπ)
    (𝟙 ((extendScalars Λ (invertibleExponentBase.{u} Λ)).obj
      (invertibleExponentBase.{u} Λ).constantSheafInt))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hσ
  have hG := leftDerivedUpperStar_map_singleFunctor_comp (ModuleCat.{u + 1} Λ) f _ _ hπ _
    (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).hom
    (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) X)).hom _ hσ
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.naturality
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit (invertibleExponentBase.{u} Λ) Λ).hom
  have hη : (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
      (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) X)).inv =
      (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).inv ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.app _ := by
    have c := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) f
      (toInvertibleExponentBase (Λ := Λ) Y) _ hπ
    rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).hom.app _ ≫
      (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).hom)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    erw [reassoc_of% c]
    exact (leftDerivedUpperStarConstantComplexIso Λ
      (toInvertibleExponentBase (Λ := Λ) X)).hom_inv_id
  simp only [constantComplexIsoSingleFunctorExtendScalarsInt, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
    Functor.comp_map] at hG n ⊢
  rw [reassoc_of% hη, ← reassoc_of% n, ← hG]

/-- The Kummer class is natural under pullback, `Lf^* κ(v) = κ(f^* v)`. -/
lemma leftDerivedUpperStar_map_kummerClassOf (v : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClassOf Y Λ v) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (tateTwistObject Λ Y 1) ≫
          (leftDerivedUpperStarTateTwistObjectIso Λ f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClassOf X Λ (Units.map f.appTop.hom.toMonoidHom v) := by
  have hB := leftDerivedUpperStar_map_tateTwistObjectOneIso Λ f
  have hB' : (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectOneIso Y Λ).inv ≫
      (leftDerivedUpperStarTateTwistObjectIso Λ f 1).hom =
      ((singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f))) ≫
        (tateTwistObjectOneIso X Λ).inv := by
    rw [Iso.eq_comp_inv, ← cancel_epi ((L((f)^*[ModuleCat.{u + 1} Λ])).map
      (tateTwistObjectOneIso Y Λ).hom)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact hB.symm
  have hA := leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt Λ f
  have hδ := leftDerivedUpperStar_map_kummerδ Λ f v
  have hcs := ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.naturality
    (tateTwistObjectOneIso Y Λ).inv
  simp only [Functor.comp_map] at hcs
  simp only [kummerClassOf, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hcs]
  rw [← Functor.map_comp, hB', Functor.map_comp, ← reassoc_of% hA]
  simp only [Functor.map_comp, Category.assoc] at hδ ⊢
  rw [reassoc_of% hδ]

end Naturality

/-- The Kummer class datum of the Tate twist `Λ(1) = μₙ ⊗ Λ`: the Kummer class of a unit is the
boundary of the unit in the Kummer sequence, with coefficients extended to `Λ`. -/
noncomputable instance hasKummerClass : HasKummerClass Λ where
  toHasTateTwist := hasTateTwist Λ
  kummerClass X _ u := kummerClassOf X Λ u
  kummerClass_mul X _ u v := kummerClassOf_mul X Λ u v
  leftDerivedUpperStar_map_kummerClass f u := leftDerivedUpperStar_map_kummerClassOf Λ f u

end Etale

end AlgebraicGeometry
