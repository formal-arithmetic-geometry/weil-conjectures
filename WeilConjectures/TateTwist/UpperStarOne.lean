/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModLimits
public import WeilConjectures.SixFunctors.ProEtale.UpperStarPreservesLimits
public import WeilConjectures.TateTwist.RootsOfUnityUpperStar
public import WeilConjectures.TateTwist.UpperStar

/-!
# The pullback of the Tate twist `ℚ̄_ℓ(1)`

Let `f : X ⟶ Y` be a morphism of schemes, where `Y` lives over a field `k` in which the prime `ℓ`
is invertible, and suppose that `f^*` commutes with sequential limits of abelian pro-étale sheaves
(e.g. `X` and `Y` quasi-compact and quasi-separated,
`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_natOp_upperStar`). Then
```
f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)
```
(`AlgebraicGeometry.ProEtale.upperStarTateTwistOneIsoOfField`), and consequently
`Lf^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for all `d ∈ ℤ`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTateTwistDerivedIsoOfField`, by
`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedIsoOfOne`).

## Proof

Recall `ℚ̄_ℓ(1) = ℚ̄_ℓ ⊗_{ℤ_ℓ} lim_n (ℤ_ℓ ⊗ μ_{ℓⁿ})`. The pullback

* commutes with extension of scalars along `ℤ_ℓ ⟶ ℚ̄_ℓ` (`ProEtale.CondensedRing.pullIso`);
* commutes with the sequential limit, as `f^*` on abelian sheaves does by assumption
  (`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_upperStar_of_ab`);
* sends the free module `ℤ_ℓ,Y ⊗ μ_{ℓⁿ,Y}` to `ℤ_ℓ,X ⊗ f^* μ_{ℓⁿ,Y}`
  (`ProEtale.CondensedRing.freeUpperStarIso`), and `f^* μ_{ℓⁿ,Y} ≅ μ_{ℓⁿ,X}` compatibly with
  the transition maps (`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfField`).

These steps are carried out for general coefficient rings `Λ ⟶ Λ'` and inverse systems of free
modules (`AlgebraicGeometry.ProEtale.upperStarExtendScalarsLimitFreeSystemIso`), and only then
instantiated, which keeps the elaboration of the concrete condensed coefficient rings cheap.

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarTateTwistOneIsoOfField`: `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTateTwistDerivedIsoOfField`:
  `Lf^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for `d ∈ ℤ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-! ### Pullback of limits of free modules -/

section Generic

/-- The inverse system `n ↦ R ⊗ μ n` of free `R`-modules on an inverse system `μ` of abelian
sheaves on `Z_proét`. -/
noncomputable abbrev freeOpSequence {Z : Scheme.{u}} (R : Sheaf (ProEt.topology Z) Ab.{u + 1})
    [MonObj R] (μ : ℕ → Sheaf (ProEt.topology Z) Ab.{u + 1}) (t : ∀ n, μ (n + 1) ⟶ μ n) :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) R :=
  Functor.ofOpSequence (X := fun n ↦ (Mod.freeFunctor R).obj (μ n))
    (fun n ↦ (Mod.freeFunctor R).map (t n))

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If the pullback of abelian sheaves preserves limits of shape `J`, so does the pullback of
module objects: it is `mapMod(f^*)` followed by restriction of scalars along an isomorphism. -/
instance preservesLimitsOfShape_upperStar_of_ab (J : Type) [Category J]
    [PreservesLimitsOfShape J (f)^*[Ab.{u + 1}]] : PreservesLimitsOfShape J (f)^*⟦Λ⟧ :=
  preservesLimitsOfShape_of_natIso (Functor.isoWhiskerLeft
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm

variable {μY : ℕ → Sheaf (ProEt.topology Y) Ab.{u + 1}}
  {μX : ℕ → Sheaf (ProEt.topology X) Ab.{u + 1}}
  (tY : ∀ n, μY (n + 1) ⟶ μY n) (tX : ∀ n, μX (n + 1) ⟶ μX n)
  (φ : ∀ n, (f)^*[Ab.{u + 1}].obj (μY n) ≅ μX n)
  (hφ : ∀ n, (f)^*[Ab.{u + 1}].map (tY n) ≫ (φ n).hom = (φ (n + 1)).hom ≫ tX n)

variable (Λ) in
/-- The components `f^*(Λ_Y ⊗ μY n) ≅ Λ_X ⊗ f^* μY n ≅ Λ_X ⊗ μX n`. -/
noncomputable def upperStarFreeIso (n : ℕ) :
    (f)^*⟦Λ⟧.obj ((Mod.freeFunctor (condensedRingObj Λ Y)).obj (μY n)) ≅
      (Mod.freeFunctor (condensedRingObj Λ X)).obj (μX n) :=
  (freeUpperStarIso Λ f).app (μY n) ≪≫ (Mod.freeFunctor _).mapIso (φ n)

include hφ in
/-- The isomorphisms `AlgebraicGeometry.ProEtale.upperStarFreeIso` are compatible with the
transition maps. -/
lemma upperStarFreeIso_naturality (n : ℕ) :
    (f)^*⟦Λ⟧.map ((Mod.freeFunctor (condensedRingObj Λ Y)).map (tY n)) ≫
        (upperStarFreeIso Λ f φ n).hom =
      (upperStarFreeIso Λ f φ (n + 1)).hom ≫
        (Mod.freeFunctor (condensedRingObj Λ X)).map (tX n) := by
  have h := (freeUpperStarIso Λ f).hom.naturality (tY n)
  dsimp only [Functor.comp_map] at h
  simp only [upperStarFreeIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [reassoc_of% h, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hφ]

variable (Λ) in
/-- The pullback of the inverse system `n ↦ Λ_Y ⊗ μY n` is the inverse system
`n ↦ Λ_X ⊗ μX n`. -/
noncomputable def upperStarFreeSystemIso
    (hφ : ∀ n, (f)^*[Ab.{u + 1}].map (tY n) ≫ (φ n).hom = (φ (n + 1)).hom ≫ tX n) :
    freeOpSequence (condensedRingObj Λ Y) μY tY ⋙ (f)^*⟦Λ⟧ ≅
      freeOpSequence (condensedRingObj Λ X) μX tX :=
  let τ : freeOpSequence (condensedRingObj Λ Y) μY tY ⋙ (f)^*⟦Λ⟧ ⟶
      freeOpSequence (condensedRingObj Λ X) μX tX :=
    NatTrans.ofOpSequence (fun n ↦ (upperStarFreeIso Λ f φ n).hom) (fun n ↦ by
      simpa using upperStarFreeIso_naturality f tY tX φ hφ n)
  haveI : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact inferInstanceAs (IsIso (upperStarFreeIso Λ f φ n.unop).hom)
  asIso τ

variable (Λ) in
/-- If `f^*` commutes with sequential limits, the pullback of `lim_n Λ_Y ⊗ μY n` is
`lim_n Λ_X ⊗ μX n`. -/
noncomputable def upperStarLimitFreeSystemIso [PreservesLimitsOfShape ℕᵒᵖ (f)^*[Ab.{u + 1}]]
    (hφ : ∀ n, (f)^*[Ab.{u + 1}].map (tY n) ≫ (φ n).hom = (φ (n + 1)).hom ≫ tX n) :
    (f)^*⟦Λ⟧.obj (limit (freeOpSequence (condensedRingObj Λ Y) μY tY)) ≅
      limit (freeOpSequence (condensedRingObj Λ X) μX tX) :=
  preservesLimitIso _ _ ≪≫ HasLimit.isoOfNatIso (upperStarFreeSystemIso Λ f tY tX φ hφ)

/-- If `f^*` commutes with sequential limits, the pullback of
`Λ'_Y ⊗_{Λ_Y} lim_n (Λ_Y ⊗ μY n)` is `Λ'_X ⊗_{Λ_X} lim_n (Λ_X ⊗ μX n)`, for a morphism
`a : Λ ⟶ Λ'` of condensed rings. -/
noncomputable def upperStarExtendScalarsLimitFreeSystemIso
    [PreservesLimitsOfShape ℕᵒᵖ (f)^*[Ab.{u + 1}]]
    (hφ : ∀ n, (f)^*[Ab.{u + 1}].map (tY n) ≫ (φ n).hom = (φ (n + 1)).hom ≫ tX n) :
    (f)^*⟦Λ'⟧.obj ((Mod.extendScalars (coefficientMap a Y)).obj
      (limit (freeOpSequence (condensedRingObj Λ Y) μY tY))) ≅
      (Mod.extendScalars (coefficientMap a X)).obj
        (limit (freeOpSequence (condensedRingObj Λ X) μX tX)) :=
  ((pullIso a f).app _).symm ≪≫
    (Mod.extendScalars _).mapIso (upperStarLimitFreeSystemIso Λ f tY tX φ hφ)

end Generic

/-! ### The Tate twist `ℚ̄_ℓ(1)` -/

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Spec (.of k)) (ℓ : ℕ)
  [NeZero (ℓ : k)]

/-- The powers of `ℓ` are invertible in `k`. -/
lemma neZero_natCast_pow (n : ℕ) : NeZero (((ℓ ^ n : ℕ)) : k) :=
  ⟨by push_cast; exact pow_ne_zero _ (NeZero.ne _)⟩

/-- The transition map `μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`, `x ↦ x ^ ℓ`, of the Tate module (as in
`AlgebraicGeometry.ProEtale.tateModuleTransition`). -/
noncomputable def rootsOfUnitySheafTransition (Z : Scheme.{u}) (n : ℕ) :
    rootsOfUnitySheaf Z (ℓ ^ (n + 1)) ⟶ rootsOfUnitySheaf Z (ℓ ^ n) :=
  eqToHom (congrArg (rootsOfUnitySheaf Z) (pow_succ' ℓ n)) ≫ rootsOfUnitySheafPow Z (ℓ ^ n) ℓ

/-- The isomorphisms `f^* μ_{ℓⁿ,Y} ≅ μ_{ℓⁿ,X}`. -/
noncomputable def upperStarRootsOfUnityPowIso (n : ℕ) :
    (f)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf Y (ℓ ^ n)) ≅ rootsOfUnitySheaf X (ℓ ^ n) :=
  haveI := neZero_natCast_pow (k := k) ℓ n
  upperStarRootsOfUnitySheafIsoOfField (ℓ ^ n) f p

/-- The isomorphisms `f^* μ_{ℓⁿ,Y} ≅ μ_{ℓⁿ,X}` are compatible with the transition maps. -/
lemma upperStar_map_rootsOfUnitySheafTransition_comp (n : ℕ) :
    (f)^*[Ab.{u + 1}].map (rootsOfUnitySheafTransition ℓ Y n) ≫
        (upperStarRootsOfUnityPowIso f p ℓ n).hom =
      (upperStarRootsOfUnityPowIso f p ℓ (n + 1)).hom ≫ rootsOfUnitySheafTransition ℓ X n := by
  have := neZero_natCast_pow (k := k) ℓ n
  have := neZero_natCast_pow (k := k) ℓ (n + 1)
  have : NeZero (((ℓ * ℓ ^ n : ℕ)) : k) := by rw [← pow_succ']; infer_instance
  simp only [upperStarRootsOfUnityPowIso, rootsOfUnitySheafTransition, Functor.map_comp,
    Category.assoc]
  rw [upperStar_map_rootsOfUnitySheafPow_comp_isoOfField (ℓ ^ n) ℓ f p,
    upperStar_map_eqToHom_comp_isoOfField_assoc (pow_succ' ℓ n) f p]

variable [Fact ℓ.Prime]

/-- **The pullback of `ℚ̄_ℓ(1)`**: for `f : X ⟶ Y` with `Y` over a field `k` in which `ℓ` is
invertible, and `f^*` commuting with sequential limits of abelian sheaves (e.g. `X`, `Y`
quasi-compact and quasi-separated,
`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_natOp_upperStar`),
`f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)` as `ℚ̄_ℓ,X`-modules. -/
noncomputable def upperStarTateTwistOneIsoOfField
    [PreservesLimitsOfShape ℕᵒᵖ (f)^*[Ab.{u + 1}]] :
    (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistOne Y ℓ) ≅ tateTwistOne X ℓ :=
  upperStarExtendScalarsLimitFreeSystemIso (Profinite.padicIntRingObjToPadicAlgCl ℓ) f
    (μY := fun n ↦ rootsOfUnitySheaf Y (ℓ ^ n)) (μX := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (rootsOfUnitySheafTransition ℓ Y) (rootsOfUnitySheafTransition ℓ X)
    (upperStarRootsOfUnityPowIso f p ℓ) (upperStar_map_rootsOfUnitySheafTransition_comp f p ℓ)

/-- For quasi-compact quasi-separated schemes, the pullback of abelian pro-étale sheaves commutes
with sequential limits (`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab`). -/
instance preservesLimitsOfShape_natOp_upperStar [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    PreservesLimitsOfShape ℕᵒᵖ (f)^*[Ab.{u + 1}] :=
  have := preservesLimitsOfSize_upperStar_ab f
  have : PreservesLimitsOfSize.{0, 0} (f)^*[Ab.{u + 1}] := preservesLimitsOfSize_shrink _
  inferInstance

/-- **The derived pullback of the Tate twists**: for `f : X ⟶ Y` with `Y` over a field `k` in
which `ℓ` is invertible, and `f^*` commuting with sequential limits of abelian sheaves (e.g. `X`,
`Y` quasi-compact and quasi-separated), `Lf^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for all `d ∈ ℤ`. -/
noncomputable def leftDerivedUpperStarTateTwistDerivedIsoOfField
    [PreservesLimitsOfShape ℕᵒᵖ (f)^*[Ab.{u + 1}]] (d : ℤ) :
    L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived Y ℓ d) ≅
      tateTwistDerived X ℓ d :=
  CondensedRing.leftDerivedUpperStarTateTwistDerivedIsoOfOne f ℓ
    (upperStarTateTwistOneIsoOfField f p ℓ) (isDualizable_tateTwistNat ℓ p) d

end AlgebraicGeometry.ProEtale
