/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.CategoryTheory.CoefficientPushCopowerCriterion
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis
import Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers

/-!

# Compatibility of the six functors with the extension of `ℓ`-adic coefficients

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`) and `Ω = ℚ̄_ℓ`. The inclusions of condensed rings
`E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`) and `E̲ ⟶ ℚ̲̄_ℓ`
(`Profinite.padicSubfieldRingObjToPadicAlgCl`) of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` pull back, on a
scheme `X`, to coefficient changes `ι : E_X ⟶ F_X` and `ι : E_X ⟶ ℚ̄_ℓ,X`
(`ProEtale.coefficientMap`), inducing the derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - .
```
The comparisons (Pull), (Push) and (Shriek) between these and the derived functors `Lf^*`,
`Rf_*`, `Rf_!` on module objects are the ones of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, for these two
coefficient changes. This file supplies the coefficient-specific input:

* `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`), the pullback along the
  left adjoint `p_X^*` of `ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`);
* both coefficient changes are flat, so that (Pull) and (Push) are defined on the unbounded
  derived categories, and (Pull) is an isomorphism there;
* for a finite extension `F/E`, (Push) is an isomorphism on all unbounded objects, hence so is
  (Shriek);
* for `E ⊆ Ω` and proper `f`, (Push) is an isomorphism at bounded-below objects, by
  the scalar-basis decomposition and uniformly bounded-below coproduct continuity.

## Coefficient-specific input

* **(A0.2)** `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`:
  for finite subextensions `E ≤ F`, the extension of scalars `F_X ⊗_{E_X} -` is exact, i.e.
  `F_X` is flat over `E_X`. Indeed `F_X` is finite free over `E_X`: an `E`-basis `b₁, …, bₙ` of
  `F` gives `C(-, F) ≅ C(-, E)^n`, `h ↦ (hᵢ)` with `h = ∑ hᵢ bᵢ`, on the point, and `p_X^*`
  preserves finite direct sums.
* **(A0.2)**
  `ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`:
  for a finite subextension `E`, the extension of scalars `ℚ̄_ℓ,X ⊗_{E_X} -` is exact, i.e.
  `ℚ̄_ℓ,X` is flat over `E_X`: it is the filtered colimit of the `F_X`, `F ≥ E`
  (`ProEtale.isColimitPadicAlgClRingObjCocone`), each of which is finite free over `E_X`.
* `ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`: for a finite extension
  `F/E`, (Push) is an isomorphism on all unbounded objects, since `F_X ≅ E_X^n` reduces it to
  the compatibility of `Rf_*` with finite direct sums.
* `ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`:
  for `E ⊆ Ω` and `f` proper, (Push) is invertible at bounded-below complexes. Restriction
  of scalars reflects isomorphisms; the unit-mate identity identifies the restricted
  comparison with the coproduct comparison for copies with a common lower bound.
  This is the scope needed by the bounded constructible consumer. The formerly disputed
  ambient instance and its all-unbounded (Shriek) example have been retired.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

section PrivateHelpers

universe v₁ v₂ u₁ u₂ v
open MonoidalCategory MonObj BraidedCategory
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem preservesFiniteLimits_extendScalars_of_flat
    (h : ObjectProperty.flat ((comap φ).obj (regular S))) :
    PreservesFiniteLimits (extendScalars φ) := by
  have : PreservesFiniteLimits (tensorLeft ((comap φ).obj (regular S))) := h.1.1
  have : PreservesFiniteLimits (extendScalars φ ⋙ forget S) :=
    preservesFiniteLimits_of_natIso (extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars φ) (forget S)

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem flat_finiteFree (n : ℕ) : ObjectProperty.flat (finiteFree R n) := by
  have h := ObjectProperty.flat_coproduct
    (fun _ : ULift.{v} (Fin n) ↦ (𝟙_ (Mod C R)))
    (fun _ ↦ ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ (Mod C R))))
  exact ObjectProperty.prop_of_iso _ ((Sigma.whiskerEquiv Equiv.ulift.symm
    (fun _ ↦ Iso.refl _)).symm ≪≫ (biproduct.isoCoproduct _).symm) h


omit [Abelian.HasFunctorialFlatResolution C] in
private theorem flat_of_preservesFiniteLimits_extendScalars
    [PreservesFiniteLimits (extendScalars φ)] :
    ObjectProperty.flat ((comap φ).obj (regular S)) := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesFiniteLimits (tensorLeft ((comap φ).obj (regular S)) ⋙ forget R) :=
    preservesFiniteLimits_of_natIso (extendForgetTensorIso φ)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget R)

private def restrictedRegularMap {T : C} [MonObj T] (a : R ⟶ S) [IsMonHom a]
    (b : R ⟶ T) [IsMonHom b] (c : S ⟶ T) [IsMonHom c] (h : a ≫ c = b) :
    (comap a).obj (regular S) ⟶ (comap b).obj (regular T) :=
  homMk c (by
    change (a ▷ S ≫ μ[S]) ≫ c = R ◁ c ≫ b ▷ T ≫ μ[T]
    rw [Category.assoc, IsMonHom.mul_hom]
    simp only [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← comp_whiskerRight_assoc, h, whisker_exchange_assoc])
end CategoryTheory.Mod

/- The following finite free comparisons use only additive monoidal functors, so they apply
both to sheafification and to inverse image from the point. -/
namespace CategoryTheory.Mod

section Map
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]
private theorem additive_mapMod : (F.mapMod R).Additive where
  map_add := hom_ext _ _ F.map_add

private noncomputable def mapRegularIso :
    (F.mapMod R).obj (regular R) ≅ regular (F.obj R) :=
  isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])
private noncomputable def mapFiniteFreeIso (n : ℕ) :
    (F.mapMod R).obj (finiteFree R n) ≅ finiteFree (F.obj R) n := by
  have : (F.mapMod R).Additive := additive_mapMod F
  exact (F.mapMod R).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ mapRegularIso F)
private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (mapRegularIso F)
private noncomputable def mapFreeRestrictedRegularIso (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap (F.map a)).obj (regular (F.obj S)) ≅ finiteFree (F.obj R) n :=
  (mapRestrictedRegularIso F a).symm ≪≫ (F.mapMod R).mapIso e ≪≫ mapFiniteFreeIso F n
end Map
section RingIso
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S]
private noncomputable def regularRingIso (r : R ≅ S) [IsMonHom r.hom] :
    (comap r.inv).obj (regular R) ≅ regular S :=
  isoMk r (by
    change (r.inv ▷ R ≫ μ[R]) ≫ r.hom = S ◁ r.hom ≫ μ[S]
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← comp_whiskerRight_assoc, r.inv_hom_id,
      id_whiskerRight, Category.id_comp])
private noncomputable def comapFreeIso (e : R ≅ S) [IsMonHom e.hom] (n : ℕ) :
    (comap e.inv).obj (finiteFree R n) ≅ finiteFree S n := by
  letI : PreservesBiproduct (fun _ : Fin n ↦ regular R) (comap e.inv) :=
    preservesBiproduct_of_preservesProduct _
  let er := regularRingIso e
  exact (comap e.inv).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ er)

variable {R' S' : C} [MonObj R'] [MonObj S']
private noncomputable def restrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a) :
    (comap a').obj (regular S') ≅
      (comap r.inv).obj ((comap a).obj (regular S)) := by
  let es := regularRingIso s
  exact (comap a').mapIso es.symm ≪≫
    ((comapComp a' s.inv).symm ≪≫ comapCongr h ≪≫ comapComp r.inv a).app _
private noncomputable def freeRestrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a)
    (n : ℕ) (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap a').obj (regular S') ≅ finiteFree R' n :=
  restrictedRegularIsoOfRingIso a a' r s h ≪≫
    (comap r.inv).mapIso e ≪≫ comapFreeIso r n
end RingIso
end CategoryTheory.Mod

/- Work sectionwise before sheafification: a continuous field-linear map gives an internal
module morphism, and the coordinate maps of a finite basis give inverse biproduct maps. -/
namespace Profinite

private noncomputable def continuousAddHomPresheaf
    {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Ring T] [TopologicalSpace T] [IsTopologicalRing T]
    (l : S →+ T) (hl : Continuous l) :
    continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app U := AddCommGrpCat.ofHom
    { toFun f := ULift.up ⟨fun x ↦ l (f.down x), hl.comp f.down.continuous⟩
      map_zero' := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_zero l
      map_add' f g := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_add l _ _ }
  naturality _ _ _ := rfl

private noncomputable def continuousLinearPresheafHom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : S →ₗ[R] R) (hl : Continuous l) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ⟶
    Mod.regular (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up (⟨fun x ↦ l ((algebraMap R S (r.down x)) * s.down x), _⟩ :
      C(U.unop, R)) = ULift.up _
    congr 1
    ext x
    change l ((algebraMap R S (r.down x)) * s.down x) = r.down x * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousLinearPresheafHomFrom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : R →ₗ[R] S) (hl : Continuous l) :
    Mod.regular (continuousMapRingPresheaf.{u} R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    congr 1
    ext x
    change l (r.down x * s.down x) = algebraMap R S (r.down x) * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousBasisIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ≅
    Mod.finiteFree (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) n := by
  let p (i : Fin n) := continuousLinearPresheafHom ha (b.coord i) (hc i)
  let q (i : Fin n) := continuousLinearPresheafHomFrom ha
    (LinearMap.toSpanSingleton R S (b i))
    (by
      change Continuous (fun r : R ↦ r • b i)
      simp_rw [Algebra.smul_def]
      exact ha.mul_const (b i))
  refine
    { hom := biproduct.lift p
      inv := biproduct.desc q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [biproduct.lift_desc]
    apply Mod.hom_ext
    change (Mod.forget _).map (∑ i, p i ≫ q i) = _
    rw [Functor.map_sum]
    apply NatTrans.ext
    funext U
    simp only [NatTrans.app_sum]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    let ev : (AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S)) ⟶
        AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S))) →+ S :=
      { toFun g := (g.hom f).down x
        map_zero' := rfl
        map_add' _ _ := rfl }
    change ev (∑ i, _) = f.down x
    rw [map_sum]
    change (∑ i, (b.coord i (f.down x)) • b i) = f.down x
    exact b.sum_repr (f.down x)
  · apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      Category.id_comp]
    apply Mod.hom_ext
    by_cases hij : j = i
    · subst j
      rw [biproduct.ι_π_self]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b i) = f.down x
      simp
    · rw [biproduct.ι_π_ne _ hij]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = (0 : ULift.{u + 1} C(U.unop, R))
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b j) = 0
      simp [hij]

private noncomputable def continuousBasisSheafIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap (algebraMap R S) ha))).obj
      (Mod.regular (continuousMapRingObj S)) ≅ Mod.finiteFree (continuousMapRingObj R) n := by
  let a := Functor.whiskerRight (continuousMapRingPresheafMap
    (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let sh := presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  exact Mod.freeRestrictedRegularIsoOfRingIso (sh.map a) _
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf R))
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf S))
    (by rw [Sheaf.sheafCompose_map_eq]; simp [sh, a, continuousMapRingSheafMap_hom]) n
    (Mod.mapFreeRestrictedRegularIso sh a n (continuousBasisIso ha n b hc))

private theorem padicSubfield_isFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.IsFree (continuousMapRingObj.{u} E)
      ((Mod.comap (padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (continuousMapRingObj F))) := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ℚ_[ℓ] F := F.2
  have : FiniteDimensional E F := FiniteDimensional.right ℚ_[ℓ] E F
  let b := Module.finBasis E F
  refine ⟨Module.finrank E F, ⟨continuousBasisSheafIso
    (continuous_subtype_val.subtype_mk _) _ b ?_⟩⟩
  intro i
  exact ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
end Profinite

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [Abelian C] [MonoidalPreadditive C] [SymmetricCategory C]
  [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj R] [IsCommMonObj S] in
private theorem restrictionReflectsIsomorphisms : (comap (D := C) φ).ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro M N f hf
  have : IsIso f.hom := by
    change IsIso ((forget R).map ((comap φ).map f))
    infer_instance
  have : IsIso ((forget S).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (forget S)

private noncomputable def restrictExtendTensorIso (M : Mod C R) :
    (comap φ).obj ((extendScalars φ).obj M) ≅ ((comap φ).obj (regular S)) ⊗ M :=
  isoMk (extendForgetTensorObjIso φ M) (by
    dsimp only [extendForgetTensorObjIso]
    apply (cancel_epi (R ◁ extendπ φ M)).1
    change R ◁ extendπ φ M ≫ (φ ▷ _ ≫ γ[S,_]) ≫ _ = _
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc]
    rw [extendπ_extendDescHom]
    rw [← whiskerLeft_comp_assoc, extendπ_extendDescHom, whiskerLeft_tensorπ_smul]
    rw [associator_inv_naturality_left_assoc]
    change _ = (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫
      tensorObjπ ((comap φ).obj (regular S)) M
    rw [comp_whiskerRight, Category.assoc])

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma tensorπ_leftUnitor_hom (M : Mod C S) :
    tensorObjπ (regular S) M ≫ (λ_ M).hom.hom = γ[S,M.X] := by
  change coequalizer.π _ _ ≫
    ((_root_.Bimod.whiskerRight (toBimodRegularIso (R := S)).hom
        ((toBimod S).obj M)).hom ≫
      _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M)) = _
  rw [← Category.assoc]
  dsimp only [_root_.Bimod.whiskerRight]
  change (colimit.ι _ WalkingParallelPair.one ≫ colimMap _) ≫ _ = _
  rw [ι_colimMap]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom, id_whiskerRight]
  change (𝟙 (S ⊗ M.X) ≫ coequalizer.π _ _) ≫
    _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M) = _
  rw [Category.id_comp]
  dsimp only [_root_.Bimod.LeftUnitorBimod.hom]
  exact coequalizer.π_desc _ _

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma leftUnitor_inv_hom (M : Mod C S) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ tensorObjπ (regular S) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [← comp_hom', Iso.inv_hom_id, id_hom']
  simp only [Category.assoc]
  rw [tensorπ_leftUnitor_hom, one_act, Iso.inv_hom_id]

private noncomputable def scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) : M ⟶ M :=
  (λ_ M).inv ≫ (regularLift (regular S) b ▷ M) ≫ (λ_ M).hom

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma scalarEndo_hom (b : 𝟙_ C ⟶ S) (M : Mod C S) :
    (scalarEndo b M).hom = (λ_ M.X).inv ≫ b ▷ M.X ≫ γ[S,M.X] := by
  simp only [scalarEndo, comp_hom', leftUnitor_inv_hom, Category.assoc]
  rw [tensorObjπ_whiskerRight_assoc, tensorπ_leftUnitor_hom]
  rw [← comp_whiskerRight_assoc, one_comp_regularLift]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendUnit_scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C R) :
    extendUnitHom φ M ≫ (scalarEndo b ((extendScalars φ).obj M)).hom =
      (λ_ M.X).inv ≫ b ▷ M.X ≫ extendπ φ M := by
  rw [scalarEndo_hom]
  change extendUnitHom φ M ≫ (λ_ (extendScalarsObj φ M).X).inv ≫
    b ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X] = _
  rw [leftUnitor_inv_naturality_assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendUnitHom_smul']

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendUnit_scalarEndo_tensor (q : regular R ⟶ (comap φ).obj (regular S))
    (M : Mod C R) :
    extendUnit φ M ≫ (comap φ).map
        (scalarEndo (S := S) (η[R] ≫ q.hom) ((extendScalars φ).obj M)) ≫
        (restrictExtendTensorIso φ M).hom =
      (λ_ M).inv ≫ (q ▷ M) := by
  apply hom_ext
  simp only [comp_hom', comap_map_hom, extendUnit_hom]
  change extendUnitHom φ M ≫
    (scalarEndo (S := S) (η[R] ≫ q.hom) ((extendScalars φ).obj M)).hom ≫
    (extendForgetTensorObjIso φ M).hom = _
  rw [← Category.assoc, extendUnit_scalarEndo]
  simp only [extendForgetTensorObjIso, Category.assoc, extendπ_extendDescHom]
  rw [leftUnitor_inv_hom]
  simp only [Category.assoc]
  rw [tensorObjπ_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]

private noncomputable def freeTensorIso (n : ℕ) (M : Mod C R)
    (e : (comap φ).obj (regular S) ≅ finiteFree R n) :
    (⨁ fun _ : Fin n ↦ M) ≅ ((comap φ).obj (regular S)) ⊗ M :=
  biproduct.mapIso (fun _ ↦ (λ_ M).symm) ≪≫
    ((tensorRight M).mapBiproduct (fun _ : Fin n ↦ regular R)).symm ≪≫
    (tensorRight M).mapIso e.symm

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
private lemma freeTensorIso_hom (n : ℕ) (M : Mod C R)
    (e : (comap φ).obj (regular S) ≅ finiteFree R n) :
    (freeTensorIso φ n M e).hom =
      biproduct.desc (fun i ↦ (λ_ M).inv ≫ ((biproduct.ι _ i ≫ e.inv) ▷ M)) := by
  apply biproduct.hom_ext'
  intro i
  simp [freeTensorIso, CategoryTheory.Functor.mapBiproduct]

omit [Abelian.HasFunctorialFlatResolution C] in
private lemma isIso_basisUnitDesc (n : ℕ) (M : Mod C R)
    (e : (comap φ).obj (regular S) ≅ finiteFree R n) :
    IsIso (biproduct.desc fun i : Fin n ↦ extendUnit φ M ≫ (comap φ).map
      (scalarEndo (S := S) (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom) ((extendScalars φ).obj M))) := by
  let t := restrictExtendTensorIso φ M
  have h : (biproduct.desc fun i : Fin n ↦ extendUnit φ M ≫ (comap φ).map
      (scalarEndo (S := S) (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom) ((extendScalars φ).obj M))) ≫
      t.hom = (freeTensorIso φ n M e).hom := by
    rw [freeTensorIso_hom]
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_desc_assoc, biproduct.ι_desc]
    dsimp only [t]
    rw [Category.assoc]
    exact extendUnit_scalarEndo_tensor (C := C) (R := R) (S := S) φ
      (biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ e.inv) M
  have : IsIso ((biproduct.desc fun i : Fin n ↦ extendUnit φ M ≫ (comap φ).map
      (scalarEndo (S := S) (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom) ((extendScalars φ).obj M))) ≫
      t.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ t.hom

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj S] in
private lemma extendAdj_unit (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M = extendUnit φ M := by
  change extendUnit φ M ≫ (comap φ).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [Abelian.HasFunctorialFlatResolution C] in
private lemma isIso_basisAdjUnitDesc (n : ℕ) (M : Mod C R)
    (e : (comap φ).obj (regular S) ≅ finiteFree R n) :
    IsIso (biproduct.desc fun i : Fin n ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map
        (scalarEndo (S := S) (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom)
          ((extendScalars φ).obj M))) := by
  rw [extendAdj_unit]
  exact isIso_basisUnitDesc φ n M e

private noncomputable def scalarNatEndo (b : 𝟙_ C ⟶ S) :
    𝟭 (Mod C S) ⟶ 𝟭 (Mod C S) where
  app M := scalarEndo b M
  naturality M N f := by
    apply hom_ext
    simp only [CategoryTheory.Functor.id_map, comp_hom', scalarEndo_hom]
    rw [leftUnitor_inv_naturality_assoc f.hom, whisker_exchange_assoc, ← act_hom]
    simp only [Category.assoc]

end CategoryTheory.Mod


namespace CategoryTheory
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
private noncomputable def complexCenter (τ : CatCenter A) :
    CatCenter (CochainComplex A ℤ) where
  app K :=
    { f i := τ.app (K.X i)
      comm' i j _ := by simpa using (τ.naturality (K.d i j)).symm }
  naturality K L f := by
    ext i
    exact τ.naturality (f.f i)

private noncomputable def homotopyCenter (τ : CatCenter A) :
    CatCenter (HomotopyCategory A (.up ℤ)) where
  app K := (HomotopyCategory.quotient A (.up ℤ)).map ((complexCenter τ).app K.as)
  naturality K L f := by
    let f' : K.as ⟶ L.as := (HomotopyCategory.quotient A (.up ℤ)).preimage f
    have hf : (HomotopyCategory.quotient A (.up ℤ)).map f' = f :=
      (HomotopyCategory.quotient A (.up ℤ)).map_preimage f
    simp only [CategoryTheory.Functor.id_map]
    rw [← hf, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (HomotopyCategory.quotient A (.up ℤ)).map
      ((complexCenter τ).naturality f')

private noncomputable def derivedCenter (τ : CatCenter A) : CatCenter (DerivedCategory A) :=
  (homotopyCenter τ).localization DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))

private lemma derivedCenter_Qh (τ : CatCenter A) (K : HomotopyCategory A (.up ℤ)) :
    (derivedCenter τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((homotopyCenter τ).app K) :=
  CatCenter.localization_app _ _ _ _
end CategoryTheory

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (extendScalars φ)]

attribute [local instance] Abelian.hasFiniteBiproducts

omit [IsCommMonObj S] in
private lemma isIso_derivedBasisUnitDesc {I : Type} [Finite I]
    (τ : I → CatCenter (Mod C S))
    (h : ∀ M : Mod C R, IsIso (biproduct.desc fun i ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map ((τ i).app _)))
    (M : DerivedCategory (Mod C R)) :
    IsIso (biproduct.desc fun i ↦
      (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app M ≫
        (comap φ).mapDerivedCategory.map ((derivedCenter (τ i)).app _)) := by
  have hC (K : CochainComplex (Mod C R) ℤ) :
      IsIso (biproduct.desc fun i ↦
        ((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
        ((comap φ).mapHomologicalComplex _).map
          ((complexCenter (τ i)).app (((extendScalars φ).mapHomologicalComplex _).obj K))) := by
    have (n : ℤ) : IsIso ((biproduct.desc fun i ↦
        ((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
        ((comap φ).mapHomologicalComplex _).map
          ((complexCenter (τ i)).app
            (((extendScalars φ).mapHomologicalComplex _).obj K))).f n) := by
      have e : (fun i ↦ (HomologicalComplex.eval _ _ n).map
          (((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
          ((comap φ).mapHomologicalComplex _).map
            ((complexCenter (τ i)).app (((extendScalars φ).mapHomologicalComplex _).obj K)))) =
          fun i ↦ (extendRestrictAdjunction φ).unit.app (K.X n) ≫
            (comap φ).map ((τ i).app _) := by
        ext i
        rfl
      have : IsIso (biproduct.desc fun i ↦ (HomologicalComplex.eval _ _ n).map
          (((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
          ((comap φ).mapHomologicalComplex _).map
            ((complexCenter (τ i)).app (((extendScalars φ).mapHomologicalComplex _).obj K)))) := by
        rw [e]
        exact h (K.X n)
      exact CategoryTheory.Functor.isIso_map_biproductDesc (HomologicalComplex.eval _ _ n) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ (K : CochainComplex (Mod C R) ℤ) :
      IsIso (biproduct.desc fun i ↦
        (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
        (comap φ).mapDerivedCategory.map ((derivedCenter (τ i)).app _)) := by
    have := hC K
    have := CategoryTheory.Functor.isIso_biproductDesc_map
      (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh)
      (fun i ↦ ((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
        ((comap φ).mapHomologicalComplex _).map
          ((complexCenter (τ i)).app (((extendScalars φ).mapHomologicalComplex _).obj K)))
    refine isIso_biproductDesc_of_iso _ (fun i ↦
      (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).map
      (((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.app K ≫
        ((comap φ).mapHomologicalComplex _).map
          ((complexCenter (τ i)).app (((extendScalars φ).mapHomologicalComplex _).obj K))))
      (Iso.refl _)
      ((comap φ).mapDerivedCategory.mapIso ((extendScalars φ).mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≪≫
        (comap φ).mapDerivedCategoryFactorsh.app _) (fun i ↦ ?_) this
    have hfac := (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hfac
    have e₁ := (derivedCenter (τ i)).naturality
      ((extendScalars φ).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
    dsimp only [CategoryTheory.Functor.comp_obj] at e₁
    rw [derivedCenter_Qh] at e₁
    have e₂ := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
      ((homotopyCenter (τ i)).app (((extendScalars φ).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
    simp only [CategoryTheory.Functor.comp_map] at e₂
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.refl_hom,
      Category.id_comp, Category.assoc, CategoryTheory.Functor.map_comp]
    rw [← (comap φ).mapDerivedCategory.map_comp_assoc, ← e₁,
      (comap φ).mapDerivedCategory.map_comp_assoc]
    rw [e₂, reassoc_of% hfac]
    simp only [CategoryTheory.Functor.comp_map]
    congr 2
  let e := DerivedCategory.Qh.objObjPreimageIso M
  refine isIso_biproductDesc_of_iso _ _ e.symm
    (((extendScalars φ).mapDerivedCategory ⋙ (comap φ).mapDerivedCategory).mapIso e.symm)
    (fun i ↦ ?_) (hQ (DerivedCategory.Qh.objPreimage M).as)
  have hu := (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.naturality e.inv
  have he := (derivedCenter (τ i)).naturality ((extendScalars φ).mapDerivedCategory.map e.inv)
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, CategoryTheory.Functor.comp_map, Category.assoc,
    ← (comap φ).mapDerivedCategory.map_comp]
  rw [← he, (comap φ).mapDerivedCategory.map_comp, ← reassoc_of% hu]
  rfl
end CategoryTheory.Mod

namespace CategoryTheory
section Central
variable {A B : Type*} [Category A] [Category B]
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (τA : CatCenter A) (τB : CatCenter B)
include adj in
private lemma map_center_rightAdjoint
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (Y : B) :
    G.map (τB.app Y) = τA.app (G.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, hF]
  rw [adj.counit_naturality]
  exact τB.naturality (adj.counit.app Y)

end Central
end CategoryTheory

namespace CategoryTheory.Mod
section MapScalar
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v₁} C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
  [IsGrothendieckAbelian.{v₂} D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Monoidal] {S : C} [MonObj S] [IsCommMonObj S]
  [IsCommMonObj (F.obj S)]
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]
  [MonoidalPreadditive D] [Abelian.HasFunctorialFlatResolution D] in
private lemma map_scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) :
    (F.mapMod S).map (scalarEndo b M) =
      scalarEndo (Functor.LaxMonoidal.ε F ≫ F.map b) ((F.mapMod S).obj M) := by
  apply hom_ext
  change F.map (scalarEndo b M).hom = _
  rw [scalarEndo_hom, scalarEndo_hom]
  simp only [CategoryTheory.Functor.map_comp, comp_whiskerRight, Category.assoc]
  change F.map (λ_ M.X).inv ≫ F.map (b ▷ M.X) ≫ F.map γ[S,M.X] =
    (λ_ (F.obj M.X)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj M.X ≫
      F.map b ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F S M.X ≫ F.map γ[S,M.X]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  have hunit : F.map (λ_ M.X).inv =
      (λ_ (F.obj M.X)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj M.X ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) M.X := by
    apply (cancel_mono (F.map (λ_ M.X).hom)).1
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [← Functor.LaxMonoidal.left_unitality F M.X]
    exact (Iso.inv_hom_id _).symm
  rw [hunit]
  simp only [Category.assoc]
end MapScalar
end CategoryTheory.Mod

namespace CategoryTheory
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (τA : CatCenter A) (τB : CatCenter B)
private lemma map_derivedCenter
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (M : DerivedCategory A) :
    F.mapDerivedCategory.map ((derivedCenter τA).app M) =
      (derivedCenter τB).app (F.mapDerivedCategory.obj M) := by
  have h : CategoryTheory.Functor.whiskerRight (derivedCenter τA) F.mapDerivedCategory =
      CategoryTheory.Functor.whiskerLeft F.mapDerivedCategory (derivedCenter τB) := by
    apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
    intro K
    dsimp only [CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app]
    apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K)).1
    simp only [derivedCenter_Qh]
    have h₁ := F.mapDerivedCategoryFactorsh.hom.naturality ((homotopyCenter τA).app K)
    have h₂ := (derivedCenter τB).naturality (F.mapDerivedCategoryFactorsh.hom.app K)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at h₁ h₂
    rw [derivedCenter_Qh] at h₂
    rw [← h₂, h₁]
    apply congrArg (F.mapDerivedCategoryFactorsh.hom.app K ≫ ·)
    apply congrArg DerivedCategory.Qh.map
    change (F.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient _ (.up ℤ)).map ((complexCenter τA).app K.as)) = _
    rw [CategoryTheory.Functor.mapHomotopyCategory_map]
    apply congrArg (HomotopyCategory.quotient _ (.up ℤ)).map
    ext n
    exact hF (K.as.X n)
  exact NatTrans.congr_app h M
end CategoryTheory

namespace CategoryTheory.Adjunction
variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Preadditive A] [Preadditive A'] [HasFiniteBiproducts A]
  {N_C : A ⥤ B} {R_C : B ⥤ A} (adj_C : N_C ⊣ R_C)
  {N_D : A' ⥤ B'} {R_D : B' ⥤ A'} (adj_D : N_D ⊣ R_D)
  {G : A ⥤ A'} {G' : B ⥤ B'} [G.Additive] [R_D.ReflectsIsomorphisms]
  (β : G ⋙ N_D ⟶ N_C ⋙ G')
omit [G.Additive] [R_D.ReflectsIsomorphisms] [Preadditive A] [Preadditive A']
  [HasFiniteBiproducts A] in
private theorem isIso_mate_pushHomOfComapIso (κ : G' ⋙ R_D ≅ R_C ⋙ G) :
    IsIso (mateEquiv adj_C adj_D (pushHomOfComapIso adj_C adj_D κ)) := by
  change IsIso ((mateEquiv adj_C adj_D) ((mateEquiv adj_C adj_D).symm
    (TwoSquare.mk _ _ _ _ κ.inv)))
  rw [Equiv.apply_symm_apply]
  infer_instance

private lemma isIso_of_unitDesc {I : Type} [Finite I]
    (hκ : IsIso (mateEquiv adj_C adj_D β)) (M : A)
    (e : I → (N_C.obj M ⟶ N_C.obj M))
    (e' : I → (N_D.obj (G.obj M) ⟶ N_D.obj (G.obj M)))
    (he : ∀ i, e' i ≫ β.app M = β.app M ≫ G'.map (e i))
    [IsIso (biproduct.desc fun i ↦ adj_C.unit.app M ≫ R_C.map (e i))]
    [IsIso (biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i))] :
    IsIso (β.app M) := by
  rename_i hsrc htgt
  have hC : IsIso (Sigma.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) := by
    have h : (Sigma.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) =
        (biproduct.isoCoproduct (fun _ : I ↦ M)).inv ≫
          (biproduct.desc fun i ↦ (show M ⟶ R_C.obj (N_C.obj M) from
          adj_C.unit.app M) ≫ R_C.map (e i)) := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (inferInstance) hsrc
  have hD : IsIso (Sigma.desc fun i ↦
      (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) := by
    have h : (Sigma.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) =
        (biproduct.isoCoproduct (fun _ : I ↦ G.obj M)).inv ≫
          (biproduct.desc fun i ↦ (show G.obj M ⟶ R_D.obj (N_D.obj (G.obj M)) from
          adj_D.unit.app (G.obj M)) ≫ R_D.map (e' i)) := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (inferInstance) htgt
  apply (isIso_iff_unitCoproductComparison adj_C adj_D β hκ M I e e' he).2
  have : PreservesColimit (Discrete.functor (fun _ : I ↦ M)) G := inferInstance
  exact inferInstanceAs (IsIso (sigmaComparison G (fun _ : I ↦ M)))

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (extendScalars φ)]
attribute [local instance] Abelian.hasFiniteBiproducts
private lemma derivedExtend_unit_comp_iso (M : DerivedCategory (Mod C R)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
      (comap φ).mapDerivedCategory.map
        ((extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.hom.app M) =
    (extendRestrictAdjunction φ).mapDerivedCategoryAdjunction.unit.app M := by
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.mapDerivedCategoryAdjunction,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.whiskerLeft_app, Category.assoc]
  rw [← (comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality]

private lemma isIso_leftDerivedBasisUnitDesc {I : Type} [Finite I]
    (τ : I → CatCenter (Mod C S))
    (h : ∀ M : Mod C R, IsIso (biproduct.desc fun i ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map ((τ i).app _)))
    (M : DerivedCategory (Mod C R)) :
    IsIso (biproduct.desc fun i ↦
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
        (comap φ).mapDerivedCategory.map ((derivedCenter (τ i)).app _)) := by
  have := isIso_derivedBasisUnitDesc φ τ h M
  refine isIso_biproductDesc_of_iso _ _ (Iso.refl _)
    ((comap φ).mapDerivedCategory.mapIso
      ((extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.app M)) (fun i ↦ ?_) this
  simp only [Iso.refl_hom, Category.id_comp, CategoryTheory.Functor.mapIso_hom,
    Iso.app_hom, Category.assoc, ← (comap φ).mapDerivedCategory.map_comp]
  rw [← (derivedCenter (τ i)).naturality]
  rw [(comap φ).mapDerivedCategory.map_comp]
  rw [← Category.assoc, derivedExtend_unit_comp_iso]
end CategoryTheory.Mod

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma comap_scalarEndo (b : 𝟙_ C ⟶ R) (N : Mod C S) :
    (comap φ).map (scalarEndo (b ≫ φ) N) = scalarEndo b ((comap φ).obj N) := by
  apply hom_ext
  change (scalarEndo (b ≫ φ) N).hom = (scalarEndo b ((comap φ).obj N)).hom
  simp only [scalarEndo_hom, comp_whiskerRight, Category.assoc]
  rfl

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma extendIso_scalarEndo [IsIso φ] (b : 𝟙_ C ⟶ R) (M : Mod C R) :
    (extendScalars φ).map (scalarEndo b M) =
      scalarEndo (b ≫ φ) ((extendScalars φ).obj M) := by
  let e := extendScalarsIsoComapInv φ
  apply (cancel_mono (e.hom.app M)).1
  rw [e.hom.naturality]
  have h := (scalarNatEndo (b ≫ φ)).naturality (e.hom.app M)
  dsimp only [CategoryTheory.Functor.id_map, scalarNatEndo] at h
  rw [← h]
  congr 1
  have hb : b ≫ φ ≫ inv φ = b := by simp
  change (comap (inv φ)).map (scalarEndo b M) = _
  simpa only [asIso_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    (comap_scalarEndo (inv φ) (b ≫ φ) M)
end CategoryTheory.Mod

namespace CategoryTheory.Mod
section BasisMap
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a]
private lemma mapBasisVector (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) (i : Fin n) :
    η[F.obj R] ≫ (biproduct.ι _ i ≫ (mapFreeRestrictedRegularIso F a n e).inv).hom =
      Functor.LaxMonoidal.ε F ≫ F.map (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom) := by
  have : (F.mapMod R).Additive := additive_mapMod F
  have hi : biproduct.ι _ i ≫ (mapFiniteFreeIso F n).inv =
      (mapRegularIso F).inv ≫ (F.mapMod R).map (biproduct.ι (fun _ : Fin n ↦ regular R) i) := by
    simp [mapFiniteFreeIso, CategoryTheory.Functor.mapBiproduct]
  simp only [mapFreeRestrictedRegularIso, Iso.trans_inv, Iso.symm_inv,
    CategoryTheory.Functor.mapIso_inv, ← Category.assoc, hi]
  simp only [CategoryTheory.Functor.obj.η_def, CategoryTheory.Functor.mapMod_map,
    Category.assoc, comp_hom', homMk_hom, CategoryTheory.Functor.map_comp]
  change Functor.LaxMonoidal.ε F ≫ F.map η[R] ≫ 𝟙 (F.obj R) ≫
    F.map (biproduct.ι (fun _ : Fin n ↦ regular R) i).hom ≫
    F.map e.inv.hom ≫ 𝟙 (F.obj S) ≫ 𝟙 (F.obj S) = _
  simp only [Category.id_comp, Category.comp_id]
  simp only [← Category.assoc]
  exact Category.comp_id _
end BasisMap
end CategoryTheory.Mod

namespace CategoryTheory.Mod
section BasisRingIso
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S']
  (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
  (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
  (h : a' ≫ s.inv = r.inv ≫ a)
omit [MonoidalClosed C] in
private lemma ringIsoBasisVector (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) (i : Fin n) :
    η[R'] ≫
        (biproduct.ι _ i ≫
          (freeRestrictedRegularIsoOfRingIso a a' r s h n e).inv).hom =
      η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom ≫ s.hom := by
  let : PreservesBiproduct (fun _ : Fin n ↦ regular R) (comap r.inv) :=
    preservesBiproduct_of_preservesProduct _
  let er := regularRingIso r
  have hi : biproduct.ι _ i ≫ (comapFreeIso r n).inv =
      er.inv ≫
        (comap r.inv).map (biproduct.ι (fun _ : Fin n ↦ regular R) i) := by
    simp [comapFreeIso, er, CategoryTheory.Functor.mapBiproduct]
  simp only [freeRestrictedRegularIsoOfRingIso, Iso.trans_inv,
    CategoryTheory.Functor.mapIso_inv, ← Category.assoc, hi]
  simp only [regularRingIso, Category.assoc, restrictedRegularIsoOfRingIso,
    CategoryTheory.Functor.mapIso_symm, comapComp, comapCongr, NatIso.trans_app,
    CategoryTheory.Functor.comp_obj, NatIso.ofComponents.app, Iso.trans_inv,
    Iso.app_inv, Iso.symm_inv, NatIso.ofComponents_hom_app,
    CategoryTheory.Functor.mapIso_hom, comp_hom', isoMk_inv_hom, comap_map_hom,
    Iso.refl_inv, isoMk_hom_hom, Iso.refl_hom, Category.id_comp, er]
  change η[R'] ≫ r.inv ≫ _ ≫ _ ≫ 𝟙 S ≫ 𝟙 S ≫ s.hom = _
  simp only [Category.id_comp]
  simp only [← Category.assoc]
  rw [IsMonHom.one_hom]

end BasisRingIso
end CategoryTheory.Mod

namespace CategoryTheory
section CenterTransport
variable {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
private lemma map_center_of_iso (e : F ≅ G) (τA : CatCenter A) (τB : CatCenter B)
    (hG : ∀ X, G.map (τA.app X) = τB.app (G.obj X)) (X : A) :
    F.map (τA.app X) = τB.app (F.obj X) := by
  apply (cancel_mono (e.hom.app X)).1
  rw [e.hom.naturality, hG]
  exact τB.naturality _
end CenterTransport
end CategoryTheory

namespace CategoryTheory
private lemma isoSquare_inv {B : Type*} [Category B]
    {R S R' S' : B} (a : R ⟶ S) (a' : R' ⟶ S')
    (r : R ≅ R') (s : S ≅ S') (h : a ≫ s.hom = r.hom ≫ a') :
    a' ≫ s.inv = r.inv ≫ a := by
  apply (cancel_epi r.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, s.hom_inv_id, Category.comp_id]
end CategoryTheory

namespace CategoryTheory.Mod
section MappedBasis
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D] [MonoidalClosed D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a]
  {R' S' : D} [MonObj R'] [MonObj S'] (a' : R' ⟶ S') [IsMonHom a']
  (r : F.obj R ≅ R') (s : F.obj S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
  (h : a' ≫ s.inv = r.inv ≫ F.map a)
omit [MonoidalClosed D] in
private lemma mappedRingIsoBasisVector (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) (i : Fin n) :
    η[R'] ≫ (biproduct.ι _ i ≫
      (freeRestrictedRegularIsoOfRingIso (F.map a) a' r s h n
        (mapFreeRestrictedRegularIso F a n e)).inv).hom =
      Functor.LaxMonoidal.ε F ≫ F.map (η[R] ≫ (biproduct.ι _ i ≫ e.inv).hom) ≫ s.hom := by
  rw [ringIsoBasisVector]
  simpa only [Category.assoc] using
    congrArg (· ≫ s.hom) (mapBasisVector F a n e i)
end MappedBasis
end CategoryTheory.Mod

end PrivateHelpers

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-! ### The coefficient rings `E_X`, `ℚ̄_ℓ,X` and their inclusions -/

section RingObj

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient ring object `E_X = p_X^* E̲` on `X_proét`, for a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev padicSubfieldRingObj (E : FiniteIntermediateField ℓ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj E) X

/-- The coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ` on `X_proét`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.padicAlgClRingObj ℓ) X

/-- The inclusion `E_X ⟶ F_X` for finite subextensions `E ≤ F`, the coefficient change induced by
the inclusion `E̲ ⟶ F̲` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj X ℓ E ⟶ padicSubfieldRingObj X ℓ F :=
  coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` for a finite subextension `E`, the coefficient change induced by
the inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings. -/
noncomputable abbrev padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj X ℓ E ⟶ padicAlgClRingObj X ℓ :=
  coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X

/-- The inclusion `E_X ⟶ F_X` followed by the inclusion `F_X ⟶ ℚ̄_ℓ,X` is the inclusion
`E_X ⟶ ℚ̄_ℓ,X`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ F =
      padicSubfieldRingObjToPadicAlgCl X ℓ E := by
  rw [← coefficientMap_comp, Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]

/-- The inverse image `p_X^*` from condensed abelian groups is a left adjoint, being the
composite `π_X^* ∘ p^*` of two left adjoints. -/
instance isLeftAdjoint_upperStarFromPoint : (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

/-- The cocone over the diagram `E ↦ E_X` with vertex `ℚ̄_ℓ,X`, given by the inclusions
`E_X ⟶ ℚ̄_ℓ,X`: the image under `p_X^*` of `Profinite.padicAlgClRingObjCocone`. -/
noncomputable abbrev padicAlgClRingObjCocone :
    Cocone (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X) :=
  (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)

/-- **`ℚ̄_ℓ,X = colim_E E_X`**: the inclusions `E_X ⟶ ℚ̄_ℓ,X` exhibit `ℚ̄_ℓ,X` as the filtered
colimit of the `E_X` in abelian pro-étale sheaves on `X`. This is the image of
`ℚ̲̄_ℓ = colim_E E̲` (`Profinite.isColimitPadicAlgClRingObjCocone`) under the left adjoint
`p_X^*`. -/
noncomputable def isColimitPadicAlgClRingObjCocone : IsColimit (padicAlgClRingObjCocone X ℓ) :=
  isColimitOfPreserves (upperStarFromPoint X) (Profinite.isColimitPadicAlgClRingObjCocone ℓ)

end RingObj

namespace CondensedRing
open Abelian MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

section ScalarCompatibility
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
private lemma upperStar_scalarEndo
    (b : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*⟦Λ⟧.map (Mod.scalarEndo b M) =
      Mod.scalarEndo
        (CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map b ≫ condensedPullbackHom Λ f) ((f)^*⟦Λ⟧.obj M) := by
  change (Mod.extendScalars (condensedPullbackHom Λ f)).map
    ((((f)^*[Ab.{u + 1}]).mapMod _).map (Mod.scalarEndo b M)) = _
  rw [Mod.map_scalarEndo, Mod.extendIso_scalarEndo]
  simp only [Category.assoc]
  rfl
private lemma lowerStar_derivedScalarEndo
    (b : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    R((f)_*⟦Λ⟧).map
        ((CategoryTheory.derivedCenter (Mod.scalarNatEndo
          (CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
            (f)^*[Ab.{u + 1}].map b ≫ condensedPullbackHom Λ f))).app M) =
      (CategoryTheory.derivedCenter (Mod.scalarNatEndo b)).app (R((f)_*⟦Λ⟧).obj M) := by
  apply CategoryTheory.map_center_rightAdjoint L((f)^*⟦Λ⟧)
    (derivedUpperStarLowerStarAdjunction Λ f)
  intro N
  apply CategoryTheory.map_center_of_iso
    (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory
  apply CategoryTheory.map_derivedCenter
  intro K
  exact upperStar_scalarEndo f b K
private lemma lowerStar_derivedScalarEndo_of_eq
    (bX : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X)
    (bY : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (hb : bX = CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
      (f)^*[Ab.{u + 1}].map bY ≫ condensedPullbackHom Λ f)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    R((f)_*⟦Λ⟧).map ((CategoryTheory.derivedCenter (Mod.scalarNatEndo bX)).app M) =
      (CategoryTheory.derivedCenter (Mod.scalarNatEndo bY)).app (R((f)_*⟦Λ⟧).obj M) := by
  rw [hb]
  exact lowerStar_derivedScalarEndo f bY M
end ScalarCompatibility

section FiniteFreePush
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- A finite scalar basis and its compatibility with pushforward. -/
private structure FiniteFreePushData (n : ℕ) where
  τY : Fin n → CatCenter
    (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))
  τX : Fin n → CatCenter
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
  hY : ∀ N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
    IsIso (biproduct.desc fun i ↦
      (Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app N ≫
        (Mod.comap (coefficientMap a Y)).map ((τY i).app _))
  hX : ∀ N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    IsIso (biproduct.desc fun i ↦
      (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app N ≫
        (Mod.comap (coefficientMap a X)).map ((τX i).app _))
  hscalar : ∀ (i : Fin n) (N : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))),
    R((f)_*⟦Λ'⟧).map ((CategoryTheory.derivedCenter (τX i)).app N) =
      (CategoryTheory.derivedCenter (τY i)).app (R((f)_*⟦Λ'⟧).obj N)

/-- Construct the scalar basis on both sites, transporting it along pullback. -/
@[irreducible] private noncomputable def finiteFreePushData (n : ℕ)
    (eY : (Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj Λ' Y)) ≅
      Mod.finiteFree (condensedRingObj Λ Y) n) : FiniteFreePushData a f n := by
  classical
  let P := (f)^*[Ab.{u + 1}]
  let eP : (Mod.comap (P.map (coefficientMap a Y))).obj
      (Mod.regular (P.obj (condensedRingObj Λ' Y))) ≅
        Mod.finiteFree (P.obj (condensedRingObj Λ Y)) n :=
    Mod.mapFreeRestrictedRegularIso P (coefficientMap a Y) n eY
  let r := asIso (condensedPullbackHom Λ f)
  let s := asIso (condensedPullbackHom Λ' f)
  have hsquare : coefficientMap a X ≫ s.inv = r.inv ≫ P.map (coefficientMap a Y) := by
    exact CategoryTheory.isoSquare_inv (P.map (coefficientMap a Y))
      (coefficientMap a X) r s (map_coefficientMap_comp_condensedPullbackHom a f)
  let eX := Mod.freeRestrictedRegularIsoOfRingIso (P.map (coefficientMap a Y))
    (coefficientMap a X) r s hsquare n eP
  let bY (i : Fin n) : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶
      condensedRingObj Λ' Y :=
    η[condensedRingObj Λ Y] ≫ (biproduct.ι _ i ≫ eY.inv).hom
  let bX (i : Fin n) : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj Λ' X :=
    η[condensedRingObj Λ X] ≫ (biproduct.ι _ i ≫ eX.inv).hom
  have hb (i : Fin n) : bX i =
      CategoryTheory.Functor.LaxMonoidal.ε P ≫ P.map (bY i) ≫ s.hom := by
    exact Mod.mappedRingIsoBasisVector
      (C := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (D := Sheaf (ProEt.topology X) Ab.{u + 1})
      (R := condensedRingObj Λ Y) (S := condensedRingObj Λ' Y)
      P (coefficientMap a Y) (coefficientMap a X) r s hsquare n eY i
  let τY (i : Fin n) := Mod.scalarNatEndo (bY i)
  let τX (i : Fin n) := Mod.scalarNatEndo (bX i)
  have hY (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
      IsIso (biproduct.desc fun i ↦
        (Mod.extendRestrictAdjunction (coefficientMap a Y)).unit.app N ≫
          (Mod.comap (coefficientMap a Y)).map ((τY i).app _)) :=
    Mod.isIso_basisAdjUnitDesc (coefficientMap a Y) n N eY
  have hX (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
      IsIso (biproduct.desc fun i ↦
        (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app N ≫
          (Mod.comap (coefficientMap a X)).map ((τX i).app _)) :=
    Mod.isIso_basisAdjUnitDesc (coefficientMap a X) n N eX
  have hscalar (i : Fin n) (N : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) :
      R((f)_*⟦Λ'⟧).map
        ((CategoryTheory.derivedCenter (τX i)).app N) =
      (CategoryTheory.derivedCenter (τY i)).app
        (R((f)_*⟦Λ'⟧).obj N) := by
    exact lowerStar_derivedScalarEndo_of_eq f (bX i) (bY i) (hb i) N
  exact ⟨τY, τX, hY, hX, hscalar⟩

/-- The canonical mate is invertible when its units are finite basis decompositions. -/
private theorem derivedPushHom_of_finiteFree (n : ℕ)
    (eY : (Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj Λ' Y)) ≅
      Mod.finiteFree (condensedRingObj Λ Y) n) : IsIso (derivedPushHom a f) := by
  classical
  let d := finiteFreePushData a f n eY
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap a Y)).ReflectsIsomorphisms :=
    Mod.restrictionReflectsIsomorphisms (coefficientMap a Y)
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap a Y)).mapDerivedCategory.ReflectsIsomorphisms := by
    let U := Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1}) (coefficientMap a Y)
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ U
  have : R((f)_*⟦Λ⟧).IsRightAdjoint :=
    (derivedUpperStarLowerStarAdjunction Λ f).isRightAdjoint
  have : PreservesBinaryBiproducts R((f)_*⟦Λ⟧) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : R((f)_*⟦Λ⟧).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _
  apply (NatTrans.isIso_iff_isIso_app (derivedPushHom a f)).2
  intro M
  have hκ : IsIso
      (mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
          (derivedPushHom a f)) := by
    exact Adjunction.isIso_mate_pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (derivedComapLowerStarIso a f)
  have := Mod.isIso_leftDerivedBasisUnitDesc (coefficientMap a X) d.τX d.hX M
  have := Mod.isIso_leftDerivedBasisUnitDesc (coefficientMap a Y) d.τY d.hY
    (R((f)_*⟦Λ⟧).obj M)
  apply Adjunction.isIso_of_unitDesc
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedPushHom a f) hκ M
    (fun i ↦ (CategoryTheory.derivedCenter (d.τX i)).app _)
    (fun i ↦ (CategoryTheory.derivedCenter (d.τY i)).app _)
  intro i
  rw [d.hscalar]
  exact ((CategoryTheory.derivedCenter (d.τY i)).naturality _).symm

end FiniteFreePush

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Flatness of the coefficient inclusions -/

section Flat

variable (X : Scheme.{u})

/-- **(A0.2)** For finite subextensions `E ≤ F`, the extension of scalars along `E_X ⟶ F_X` is
exact: `F_X` is finite free, in particular flat, over `E_X`. See the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) := by
  obtain ⟨n, ⟨e⟩⟩ := Profinite.padicSubfield_isFree.{u} ℓ h
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _
  let eX := Mod.mapFreeRestrictedRegularIso (upperStarFromPoint X)
    (Profinite.padicSubfieldRingObjMap ℓ h) n e
  apply Mod.preservesFiniteLimits_extendScalars_of_flat
  exact ObjectProperty.prop_of_iso _ eX.symm (Mod.flat_finiteFree n)

/-- **(A0.2)** For a finite subextension `E`, the extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` is
exact: `ℚ̄_ℓ,X` is flat over `E_X`, being a filtered colimit of finite free `E_X`-modules. See
the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
    (E : FiniteIntermediateField ℓ) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) :=
by
  let D : Under E ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E) :=
    { obj H := (Mod.comap (padicSubfieldRingObjMap X ℓ (leOfHom H.hom))).obj
        (Mod.regular (padicSubfieldRingObj X ℓ H.right))
      map {H H'} f := Mod.restrictedRegularMap
        (padicSubfieldRingObjMap X ℓ (leOfHom H.hom))
        (padicSubfieldRingObjMap X ℓ (leOfHom H'.hom))
        (padicSubfieldRingObjMap X ℓ (leOfHom f.right)) (by
          rw [← coefficientMap_comp, ← Profinite.padicSubfieldRingObjMap_comp])
      map_id H := by
        apply Mod.hom_ext
        change (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjMap ℓ _) = 𝟙 _
        rw [Profinite.padicSubfieldRingObjMap_id, CategoryTheory.Functor.map_id]
      map_comp f g := by
        apply Mod.hom_ext
        change (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjMap ℓ _) = _
        rw [Profinite.padicSubfieldRingObjMap_comp, CategoryTheory.Functor.map_comp]
        rfl }
  let c : Cocone D :=
    { pt := (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj
        (Mod.regular (padicAlgClRingObj X ℓ))
      «ι» :=
        { app H := Mod.restrictedRegularMap
            (padicSubfieldRingObjMap X ℓ (leOfHom H.hom))
            (padicSubfieldRingObjToPadicAlgCl X ℓ E)
            (padicSubfieldRingObjToPadicAlgCl X ℓ H.right)
            (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _)
          naturality H H' f := by
            apply Mod.hom_ext
            change padicSubfieldRingObjMap X ℓ _ ≫
              padicSubfieldRingObjToPadicAlgCl X ℓ H'.right = _ ≫ 𝟙 _
            rw [padicSubfieldRingObjMap_comp_toPadicAlgCl, Category.comp_id]
            rfl } }
  have hc : IsColimit c := by
    apply isColimitOfReflects (Mod.forget (padicSubfieldRingObj X ℓ E))
    change IsColimit ((padicAlgClRingObjCocone X ℓ).whisker (Under.forget E))
    exact (CategoryTheory.Functor.Final.isColimitWhiskerEquiv (Under.forget E) _).symm
      (isColimitPadicAlgClRingObjCocone X ℓ)
  apply Mod.preservesFiniteLimits_extendScalars_of_flat
  have hD (H : Under E) : ObjectProperty.flat (D.obj H) :=
    Mod.flat_of_preservesFiniteLimits_extendScalars
      (padicSubfieldRingObjMap X ℓ (leOfHom H.hom))
  have : AB5OfSize.{0, 0}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  exact ObjectProperty.prop_of_iso _ (colimit.isoColimitCocone ⟨c, hc⟩)
    (ObjectProperty.flat_colimit D hD)

end Flat

/-! ### (Push) and (Shriek) -/

section Push

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Push)** is an isomorphism for a finite extension `F/E`, on all unbounded objects: `F_X`
is finite free over `E_X`, so both sides are finite direct sums of copies of `Rf_*^E`. See the
module docstring. -/
instance isIso_derivedPushHom_padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
by
  classical
  let n := Classical.choose (Profinite.padicSubfield_isFree.{u} ℓ h)
  let e := Classical.choice (Classical.choose_spec (Profinite.padicSubfield_isFree.{u} ℓ h))
  have : PreservesBinaryBiproducts (upperStarFromPoint Y) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint Y).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _
  let a := Profinite.padicSubfieldRingObjMap ℓ h
  let eY := Mod.mapFreeRestrictedRegularIso (upperStarFromPoint Y) a n e
  exact derivedPushHom_of_finiteFree a f n eY

-- Keep the chosen derived adjunction and sheaf pullbacks folded during the unit comparisons.
-- Unfold the canonical comparison only for the explicit mate calculation below.
attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction upperStarFromPoint ProEtale.upperStar

/-- Exact restriction detects derived isomorphisms through its homology comparison. -/
private theorem reflectsDerivedIsomorphisms
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

/-- Central scalar compatibility supplies the square in the unit/copower criterion. -/
private theorem centralUnitCopower
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc fun i ↦
      (show M ⟶ U.obj (L.obj M) from adj.unit.app M) ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc fun i ↦
      (show G.obj M ⟶ U'.obj (L'.obj (G.obj M)) from adj'.unit.app (G.obj M)) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  have := hC
  have := hD
  apply (Adjunction.isIso_iff_unitCoproductComparison adj adj' β hκ M I
    (fun i ↦ (τ i).app _) (fun i ↦ (τ' i).app _) (fun i ↦ ?_)).2 hc
  exact ((τ' i).naturality (β.app M)).symm.trans
    (congrArg (fun g ↦ β.app M ≫ g) (hs i (L.obj M))).symm

/-- Explicit copower families avoid expanding the concrete unit maps during elaboration. -/
private theorem centralUnitCopowerExplicit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
      adj.unit.app M ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc (f := fun _ : I ↦ G.obj M) fun i ↦
      adj'.unit.app (G.obj M) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  exact centralUnitCopower adj adj' β hκ M I τ τ' hs hC hD hc

/-- Derived module categories have the coproducts supplied by the Grothendieck structure. -/
private theorem coefficientDerivedCoproducts (Λ : Sheaf
    (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z))) := by
  let C := Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete J)
  exact CategoryTheory.derived_hasCoproducts

set_option maxHeartbeats 400000 in
-- The explicit mate and coproduct comparison are elaborated in several large derived categories.
/-- **(Push)** for `E ⊆ ℚ̄_ℓ` is invertible at every bounded-below complex when `f` is proper.
Source: the finite-support coefficient model and bounded-below coproduct continuity.
(blueprint: lem-weil-pbc-condensed-qbar-bounded-push)

Proof: choose the compatible scalar-basis decompositions of both extension units. The mate
of the canonical push comparison is the inverse restriction/pushforward isomorphism.
Restriction reflects derived isomorphisms, by exactness and the homology criterion.
The unit-mate calculation identifies the restricted component, conjugated by the two basis
isomorphisms, with the copower comparison followed by invertible factors. The copies of the
input complex have the same lower bound. Bounded-below copower continuity for the proper,
hence qcqs, map makes this comparison invertible. Reflection gives the conclusion.
This does not assert an isomorphism of functors on the ambient unbounded categories. -/
theorem isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE [IsProper f]
    (E : FiniteIntermediateField ℓ)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (N : ℤ) [M.IsGE N] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M) := by
  classical
  obtain ⟨I, τ, hunit, hscalar⟩ := condensedQbar_derived_scalar_basis.{u} ℓ E
  have : HasCoproduct (fun _ : I ↦ M) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) X I).has_colimit _
  have : HasCoproduct (fun _ : I ↦ R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj M) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) Y I).has_colimit _
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)).ReflectsIsomorphisms :=
    Mod.restrictionReflectsIsomorphisms (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          Y)).mapDerivedCategory.ReflectsIsomorphisms :=
    reflectsDerivedIsomorphisms _
  have hκ : IsIso
      (mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
          (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)) := by
    unfold derivedPushHom
    exact Adjunction.isIso_mate_pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
      (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
  refine centralUnitCopowerExplicit
    (G := R((f)_*⟦Profinite.continuousMapRingObj E⟧))
    (G' := R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
    (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) hκ M I
    (τ X) (τ Y) ?_ ?_ ?_ ?_
  · exact fun i K ↦ hscalar f i K
  · exact hunit X M
  · exact hunit Y (R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj M)
  · exact condensedSubfield_bounded_copower_comparison.{u} ℓ E f I M N

variable [HasCompactification f]

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects. -/
example {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ h) f) :=
  inferInstance

end Push

end CondensedRing

end AlgebraicGeometry.ProEtale
