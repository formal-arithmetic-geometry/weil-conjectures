/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The derived base change map is invertible for flat base change

Consider a cartesian square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
with `S`, `S'` affine, `f` quasi-compact and quasi-separated and `g` flat. Then the canonical
base change map `Lg^* Rf_* E ⟶ Rf'_* Lg'^* E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`
(Stacks 08IB, 02KH).

The square is Tor-independent since `g` is flat
(`AlgebraicGeometry.flat_right_pullback_torIndependent`), so this is the case `P = 𝒪_X` of
`AlgebraicGeometry.torIndependent_perfect_tensor_baseChange`, transported to an arbitrary
cartesian square by `AlgebraicGeometry.exists_derivedBaseChange_coordinate_naturality`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Flatness of the right morphism makes every pair of stalks Tor independent.
Source: Stacks Project, Algebra, Tag 00M3, and perfect.tex, Tag 08IB. -/
theorem flat_right_pullback_torIndependent {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Flat g] :
    PullbackStalkTensor.IsTorIndependent f g := by
  intro x t h
  let := (f.stalkMap x).hom.toAlgebra
  let := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
  have hflat : ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) (Flat.stalkMap g t)
  have : Module.Flat (S.presheaf.stalk (f x)) (T.presheaf.stalk t) := hflat
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  let A := ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
  let B := ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)
  let P := projectiveResolution A
  apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensorRight B) (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact Module.Flat.rTensor_shortComplex_exact B _ (P.exact_succ n)

/-- The structure sheaf is perfect. -/
theorem isPerfect_tensorUnit (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Scheme.IsPerfect X (𝟙_ (schemeDerivedCategory X)) := by
  intro x
  let R := (moduleRings X.toRingedSpace).over (⊤ : X.Opens)
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
    (SheafOfModules.unit R)
  refine ⟨⊤, trivial, K, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : K.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        (eqToIso (HomologicalComplex.single_obj_X_self _ _ _)) ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (K.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using hz.eq_of_src (0 : K.X n ⟶ K.X n) (𝟙 _)⟩
  · let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
    let eunit : 𝟙_ (schemeDerivedCategory X) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) := Iso.refl _
    exact ⟨F.mapDerivedCategory.mapIso eunit ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (SheafOfModules.unit R)⟩

/-- A quasi-coherent module placed in degree `0` has quasi-coherent cohomology sheaves. -/
theorem schemeDerivedQCohProperty_singleFunctor {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    schemeDerivedQCohProperty X ((DerivedCategory.singleFunctor _ 0).obj ℱ) := by
  have hM : SheafOfModules.IsQuasicoherent (R := moduleRings X.toRingedSpace) ℱ := ‹_›
  have hzero : IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app ℱ).symm hM
  · apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- Flat base change for the chosen pullback square of `f` and `g`: the case `P = 𝒪_X` of
`torIndependent_perfect_tensor_baseChange`. Source: Stacks Project, Tags 08IB and 02KH. -/
theorem isIso_schemeDerivedBaseChangeMap_of_flat_pullback
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition E) := by
  have h := torIndependent_perfect_tensor_baseChange f g
    (flat_right_pullback_torIndependent f g) (𝟙_ _) E (isPerfect_tensorUnit X) hE
  have hn := schemeDerivedBaseChangeMap_naturality f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition (λ_ E).hom
  have hc : IsIso ((schemeDerivedDirectImage f ⋙ derivedPullback g).map (λ_ E).hom ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map (λ_ E).hom) _

/-- **Flat base change, sheaf form** (Stacks 02KH). For a cartesian square with `S`, `S'` affine,
`f` quasi-compact and quasi-separated and `g` flat, the canonical base change map
`Lg^* Rf_* E ⟶ Rf'_* Lg'^* E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`. -/
theorem isIso_schemeDerivedBaseChangeMap_of_flat
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w E) := by
  obtain ⟨e, -, -, j, k, a, h⟩ :=
    exists_derivedBaseChange_coordinate_naturality f g g' f' sq (Iso.refl S) (Iso.refl S')
  have hA := isIso_schemeDerivedBaseChangeMap_of_flat_pullback
    (f ≫ (Iso.refl S).hom) ((Iso.refl S').inv ≫ g ≫ (Iso.refl S).hom) E hE
  have hc : IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
      k.hom.app ((derivedPullback g').obj E) ≫
        (schemeDerivedDirectImage (Iso.refl S').inv).map
          ((schemeDerivedDirectImage _).map (j.hom.app E))) := by
    rw [h E]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (k.hom.app ((derivedPullback g').obj E) ≫
    (schemeDerivedDirectImage (Iso.refl S').inv).map
      ((schemeDerivedDirectImage _).map (j.hom.app E)))

end AlgebraicGeometry
